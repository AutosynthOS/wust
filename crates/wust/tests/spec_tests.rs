//! WebAssembly spec test runner.
//!
//! Runs the official WebAssembly spec `.wast` test files against the wust
//! engine. Auto-discovers all `.wast` files in `tests/spec/test/core/`.

mod harness;

use std::io::IsTerminal;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;
use std::time::{Duration, Instant};
use harness::{
    DirectiveResult, TestResult,
    discover_test_files, matches_filter, parse_cli_args,
    print_subprocess_results, render_dot_grid,
    run_tests_parallel, DIM, RESET,
};
use wust::{Engine, Instance, Linker, Module, Store, Val};

// --- Spec runner ---

struct SpecRunner {
    engine: Engine,
    instance: Option<Instance>,
    store: Store<()>,
}

impl SpecRunner {
    fn new() -> Self {
        let engine = Engine::default();
        let store = Store::new(&engine, ());
        Self {
            engine,
            instance: None,
            store,
        }
    }

    fn instantiate(&mut self, mut wat: wast::QuoteWat) -> anyhow::Result<()> {
        let binary = wat.encode().map_err(|e| anyhow::anyhow!("{e}"))?;
        let module =
            Module::from_bytes(&self.engine, &binary).map_err(|e| anyhow::anyhow!("{e}"))?;
        let linker = Linker::new(&self.engine);
        self.instance = Some(
            linker
                .instantiate(&mut self.store, &module)
                .map_err(|e| anyhow::anyhow!("{e}"))?,
        );
        Ok(())
    }

    fn invoke(&mut self, invoke: &wast::WastInvoke) -> anyhow::Result<Vec<Val>> {
        let args = parse_args(invoke)?;
        let instance = self
            .instance
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("no active instance"))?;
        instance
            .call_dynamic(&mut self.store, invoke.name, &args)
            .map_err(|e| anyhow::anyhow!("{e}"))
    }

    fn execute(&mut self, exec: wast::WastExecute) -> anyhow::Result<Vec<Val>> {
        match exec {
            wast::WastExecute::Invoke(invoke) => self.invoke(&invoke),
            wast::WastExecute::Get { module, global, .. } => {
                anyhow::ensure!(module.is_none(), "named module gets not supported");
                let instance = self
                    .instance
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("no active instance"))?;
                let val = instance
                    .get_global(&self.store, global)
                    .ok_or_else(|| anyhow::anyhow!("global {global} not found"))?;
                Ok(vec![val])
            }
            wast::WastExecute::Wat(wat) => {
                self.instantiate(wast::QuoteWat::Wat(wat))?;
                Ok(vec![])
            }
        }
    }

    fn expect_module_fails(&mut self, wat: wast::QuoteWat, message: &str) -> anyhow::Result<()> {
        match self.instantiate(wat) {
            Err(_) => Ok(()),
            Ok(()) => anyhow::bail!("should fail ({message})"),
        }
    }

    fn run_wast(&mut self, path: &Path) -> Vec<DirectiveResult> {
        let source = std::fs::read_to_string(path).unwrap();
        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = wast::parser::parse::<wast::Wast>(&buf).unwrap();

        // Suppress default panic output so interpreter panics don't
        // produce noisy stack traces — they show up as red dots instead.
        let prev_hook = panic::take_hook();
        panic::set_hook(Box::new(|_| {}));

        let results: Vec<DirectiveResult> = wast
            .directives
            .into_iter()
            .enumerate()
            .map(|(i, d)| {
                let label = directive_label(&d);
                let result = panic::catch_unwind(AssertUnwindSafe(|| {
                    self.run_directive(d)
                }));
                match result {
                    Ok(Ok(())) => DirectiveResult { index: i, passed: true, label, error: None },
                    Ok(Err(e)) => DirectiveResult { index: i, passed: false, label, error: Some(format!("{e}")) },
                    Err(payload) => {
                        let msg = payload
                            .downcast_ref::<String>()
                            .map(|s| s.clone())
                            .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                            .unwrap_or_else(|| "panic".to_string());
                        DirectiveResult { index: i, passed: false, label, error: Some(format!("panic: {msg}")) }
                    }
                }
            })
            .collect();

        panic::set_hook(prev_hook);
        results
    }

    fn run_directive(&mut self, directive: wast::WastDirective) -> anyhow::Result<()> {
        match directive {
            wast::WastDirective::Module(wat) => self.instantiate(wat),
            wast::WastDirective::Register { .. } => Ok(()), // TODO
            wast::WastDirective::AssertReturn { exec, results, .. } => {
                let got = self.execute(exec)?;
                let expected = parse_expected(&results)?;
                anyhow::ensure!(
                    vals_match(&got, &expected),
                    "got {got:?}, expected {expected:?}"
                );
                Ok(())
            }
            wast::WastDirective::AssertTrap { exec, message, .. } => match self.execute(exec) {
                Err(_) => Ok(()),
                Ok(got) => anyhow::bail!("should trap ({message}), got {got:?}"),
            },
            wast::WastDirective::AssertExhaustion { call, message, .. } => {
                match self.invoke(&call) {
                    Err(_) => Ok(()),
                    Ok(got) => anyhow::bail!("should exhaust ({message}), got {got:?}"),
                }
            }
            wast::WastDirective::AssertInvalid {
                module, message, ..
            } => self.expect_module_fails(module, message),
            wast::WastDirective::AssertMalformed {
                module, message, ..
            } => self.expect_module_fails(module, message),
            wast::WastDirective::AssertUnlinkable {
                module, message, ..
            } => self.expect_module_fails(wast::QuoteWat::Wat(module), message),
            wast::WastDirective::Invoke(invoke) => self.invoke(&invoke).map(|_| ()),
            _ => anyhow::bail!("unsupported directive"),
        }
    }
}

// --- Val conversion ---

/// Expected value for assertions. Wraps Val but adds NaN patterns
/// and ref matching that can't be represented as plain Val.
#[derive(Debug)]
enum Expected {
    Val(Val),
    F32Nan,
    F64Nan,
    RefNull,
    RefFunc,
    RefExtern,
}

fn parse_args(invoke: &wast::WastInvoke) -> anyhow::Result<Vec<Val>> {
    invoke
        .args
        .iter()
        .map(|a| match a {
            wast::WastArg::Core(c) => val_from_arg(c),
            _ => anyhow::bail!("unsupported arg"),
        })
        .collect()
}

fn val_from_arg(arg: &wast::core::WastArgCore) -> anyhow::Result<Val> {
    match arg {
        wast::core::WastArgCore::I32(v) => Ok(Val::I32(*v)),
        wast::core::WastArgCore::I64(v) => Ok(Val::I64(*v)),
        wast::core::WastArgCore::F32(v) => Ok(Val::F32(f32::from_bits(v.bits))),
        wast::core::WastArgCore::F64(v) => Ok(Val::F64(f64::from_bits(v.bits))),
        _ => anyhow::bail!("unsupported arg: {arg:?}"),
    }
}

fn parse_expected(results: &[wast::WastRet]) -> anyhow::Result<Vec<Expected>> {
    results
        .iter()
        .map(|r| match r {
            wast::WastRet::Core(c) => expected_from_ret(c),
            _ => anyhow::bail!("unsupported ret"),
        })
        .collect()
}

fn expected_from_ret(ret: &wast::core::WastRetCore) -> anyhow::Result<Expected> {
    Ok(match ret {
        wast::core::WastRetCore::I32(v) => Expected::Val(Val::I32(*v)),
        wast::core::WastRetCore::I64(v) => Expected::Val(Val::I64(*v)),
        wast::core::WastRetCore::F32(v) => match v {
            wast::core::NanPattern::Value(f) => Expected::Val(Val::F32(f32::from_bits(f.bits))),
            _ => Expected::F32Nan,
        },
        wast::core::WastRetCore::F64(v) => match v {
            wast::core::NanPattern::Value(f) => Expected::Val(Val::F64(f64::from_bits(f.bits))),
            _ => Expected::F64Nan,
        },
        wast::core::WastRetCore::RefNull(_) => Expected::RefNull,
        wast::core::WastRetCore::RefExtern(_) => Expected::RefExtern,
        wast::core::WastRetCore::RefFunc(_) => Expected::RefFunc,
        _ => anyhow::bail!("unsupported ret: {ret:?}"),
    })
}

fn vals_match(got: &[Val], expected: &[Expected]) -> bool {
    got.len() == expected.len() && got.iter().zip(expected).all(|(g, e)| val_matches(g, e))
}

fn val_matches(got: &Val, expected: &Expected) -> bool {
    match (got, expected) {
        (Val::I32(a), Expected::Val(Val::I32(b))) => a == b,
        (Val::I64(a), Expected::Val(Val::I64(b))) => a == b,
        (Val::F32(a), Expected::Val(Val::F32(b))) => a.to_bits() == b.to_bits(),
        (Val::F64(a), Expected::Val(Val::F64(b))) => a.to_bits() == b.to_bits(),
        (Val::V128(a), Expected::Val(Val::V128(b))) => a == b,
        (Val::F32(a), Expected::F32Nan) => a.is_nan(),
        (Val::F64(a), Expected::F64Nan) => a.is_nan(),
        (Val::Ref(_), Expected::RefNull) => true,
        (Val::Ref(_), Expected::RefFunc) => true,
        (Val::Ref(_), Expected::RefExtern) => true,
        _ => false,
    }
}

// --- Wast-specific labels ---

fn directive_label(d: &wast::WastDirective) -> String {
    match d {
        wast::WastDirective::Module(_) => "module".into(),
        wast::WastDirective::Register { .. } => "register".into(),
        wast::WastDirective::AssertReturn { exec, .. } => {
            format!("assert_return({})", execute_label(exec))
        }
        wast::WastDirective::AssertTrap { exec, .. } => {
            format!("assert_trap({})", execute_label(exec))
        }
        wast::WastDirective::AssertExhaustion { call, .. } => {
            format!("assert_exhaustion({})", call.name)
        }
        wast::WastDirective::AssertInvalid { .. } => "assert_invalid".into(),
        wast::WastDirective::AssertMalformed { .. } => "assert_malformed".into(),
        wast::WastDirective::AssertUnlinkable { .. } => "assert_unlinkable".into(),
        wast::WastDirective::Invoke(invoke) => format!("invoke({})", invoke.name),
        _ => "directive".into(),
    }
}

fn execute_label(exec: &wast::WastExecute) -> String {
    match exec {
        wast::WastExecute::Invoke(invoke) => invoke.name.to_string(),
        wast::WastExecute::Get { global, .. } => format!("get {global}"),
        wast::WastExecute::Wat(_) => "wat".into(),
    }
}

// --- Entry points ---

/// Run a single test in-process and return its result.
fn run_test_inproc(name: &str, path: &Path) -> TestResult {
    let start = Instant::now();
    let mut runner = SpecRunner::new();
    let directives = runner.run_wast(path);
    TestResult {
        name: name.to_string(),
        directives,
        crashed: false,
        timed_out: false,
        elapsed: start.elapsed(),
    }
}

/// Child process entry point: run a single .wast file and print results
/// using the subprocess protocol.
fn child_run(_name: &str, path: &Path) -> ! {
    let mut runner = SpecRunner::new();
    let results = runner.run_wast(path);
    print_subprocess_results(&results);
    let failed = results.iter().filter(|r| !r.passed).count();
    std::process::exit(if failed > 0 { 1 } else { 0 });
}

fn main() {
    // Internal subcommand: run a single test in a child process.
    let raw_args: Vec<String> = std::env::args().collect();
    if raw_args.len() >= 4 && raw_args[1] == "--__run" {
        child_run(&raw_args[2], Path::new(&raw_args[3]));
    }

    let cli = parse_cli_args();
    let spec_dir = Path::new("tests/spec/test/core");
    let files = discover_test_files(spec_dir, "wast");
    let matched: Vec<_> = files
        .into_iter()
        .filter(|(name, _)| {
            matches_filter(name, cli.filter.as_deref(), cli.exact, &cli.skip)
        })
        .collect();

    if cli.list {
        for (name, _) in &matched {
            println!("{name}");
        }
        return;
    }

    if matched.is_empty() {
        println!("No tests matched filter.");
        return;
    }

    let detailed = cli.expand || matched.len() <= 1;
    let start = Instant::now();

    if detailed {
        let mut any_failed = false;
        for (name, path) in &matched {
            let result = run_test_inproc(name, path);
            println!("\n{}", render_dot_grid(&result.name, &result.directives));
            if result.is_fail() {
                any_failed = true;
            }
        }
        let elapsed = start.elapsed();
        println!("\n{DIM}Finished in {:.2}s{RESET}", elapsed.as_secs_f64());
        if any_failed {
            std::process::exit(1);
        }
    } else {
        let is_tty = std::io::stdout().is_terminal();
        let timeout = Duration::from_secs(5);

        let results = run_tests_parallel(
            "Spec Tests",
            "cargo test -p wust --test spec_tests",
            matched,
            timeout,
            is_tty,
        );

        let any_failed = results.iter().any(|r| r.is_fail());
        let elapsed = start.elapsed();
        println!("{DIM}Finished in {:.2}s{RESET}", elapsed.as_secs_f64());
        if any_failed {
            std::process::exit(1);
        }
    }
}
