//! WebAssembly spec test runner.
//!
//! Runs the official WebAssembly spec `.wast` test files against the wust
//! engine. Auto-discovers all `.wast` files in `tests/spec/test/core/`.
//!
//! See `tests/harness/HARNESS.md` for CLI flags and harness documentation.

mod harness;

use std::io::IsTerminal;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;
use std::time::Duration;
use harness::{
    DirectiveResult,
    discover_test_files, matches_filter, parse_cli_args,
    print_subprocess_results, run_tests_parallel,
};
use wust::{Engine, Instance, JitModule, Linker, Module, Store, Val};

// --- Execution mode ---

#[derive(Clone, Copy)]
enum ExecMode {
    Interpreter,
    Jit,
}

impl ExecMode {
    fn prefix(self) -> &'static str {
        match self {
            ExecMode::Interpreter => "int",
            ExecMode::Jit => "jit",
        }
    }

    fn from_prefix(s: &str) -> Option<Self> {
        match s {
            "int" => Some(ExecMode::Interpreter),
            "jit" => Some(ExecMode::Jit),
            _ => None,
        }
    }
}

// --- Spec runner ---

struct SpecRunner {
    engine: Engine,
    instance: Option<Instance>,
    jit_module: Option<JitModule>,
    store: Store<()>,
    mode: ExecMode,
}

impl SpecRunner {
    fn new(mode: ExecMode) -> Self {
        let engine = Engine::default();
        let store = Store::new(&engine, ());
        Self {
            engine,
            instance: None,
            jit_module: None,
            store,
            mode,
        }
    }

    fn instantiate(&mut self, mut wat: wast::QuoteWat) -> anyhow::Result<()> {
        let binary = wat.encode().map_err(|e| anyhow::anyhow!("{e}"))?;
        let module =
            Module::from_bytes(&self.engine, &binary).map_err(|e| anyhow::anyhow!("{e}"))?;
        let linker = Linker::new(&self.engine);
        if matches!(self.mode, ExecMode::Jit) {
            self.jit_module = Some(JitModule::compile(&module)?);
        }
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
        match self.mode {
            ExecMode::Interpreter => instance
                .call_dynamic(&mut self.store, invoke.name, &args)
                .map_err(|e| anyhow::anyhow!("{e}")),
            ExecMode::Jit => {
                let jit = self
                    .jit_module
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("no JIT module compiled"))?;
                jit.call_dynamic(instance, invoke.name, &args)
                    .map_err(|e| anyhow::anyhow!("{e}"))
            }
        }
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
        let buf = match wast::parser::ParseBuffer::new(&source) {
            Ok(buf) => buf,
            Err(e) => {
                return vec![DirectiveResult {
                    index: 0, passed: false,
                    label: "parse".into(),
                    error: Some(format!("failed to lex .wast file: {e}")),
                    line: None, source: None,
                }];
            }
        };
        let wast = match wast::parser::parse::<wast::Wast>(&buf) {
            Ok(wast) => wast,
            Err(e) => {
                return vec![DirectiveResult {
                    index: 0, passed: false,
                    label: "parse".into(),
                    error: Some(format!("failed to parse .wast file: {e}")),
                    line: None, source: None,
                }];
            }
        };

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
                let span = directive_span(&d);
                let result = panic::catch_unwind(AssertUnwindSafe(|| {
                    self.run_directive(d)
                }));
                // Only compute source info for failures.
                let (line, src) = match &result {
                    Ok(Ok(())) => (None, None),
                    _ => {
                        if let Some(sp) = span {
                            let offset = sp.offset();
                            (
                                Some(line_number(&source, offset)),
                                extract_sexp(&source, offset),
                            )
                        } else {
                            (None, None)
                        }
                    }
                };
                match result {
                    Ok(Ok(())) => DirectiveResult {
                        index: i, passed: true, label,
                        error: None, line: None, source: None,
                    },
                    Ok(Err(e)) => DirectiveResult {
                        index: i, passed: false, label,
                        error: Some(format!("{e}")),
                        line, source: src,
                    },
                    Err(payload) => {
                        let msg = payload
                            .downcast_ref::<String>()
                            .map(|s| s.clone())
                            .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                            .unwrap_or_else(|| "panic".to_string());
                        DirectiveResult {
                            index: i, passed: false, label,
                            error: Some(format!("panic: {msg}")),
                            line, source: src,
                        }
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

// --- Source extraction ---

/// Extract the byte offset of a directive's span.
///
/// Every `WastDirective` variant carries a `Span` pointing at its keyword
/// in the source text (e.g. `assert_return`, `module`, etc.).
fn directive_span(d: &wast::WastDirective) -> Option<wast::token::Span> {
    Some(match d {
        wast::WastDirective::AssertReturn { span, .. }
        | wast::WastDirective::AssertTrap { span, .. }
        | wast::WastDirective::AssertExhaustion { span, .. }
        | wast::WastDirective::AssertInvalid { span, .. }
        | wast::WastDirective::AssertMalformed { span, .. }
        | wast::WastDirective::AssertUnlinkable { span, .. }
        | wast::WastDirective::Register { span, .. } => *span,
        wast::WastDirective::Invoke(invoke) => invoke.span,
        wast::WastDirective::Module(quote_wat) => {
            match quote_wat {
                wast::QuoteWat::Wat(wat) => match wat {
                    wast::Wat::Module(m) => m.span,
                    wast::Wat::Component(c) => c.span,
                },
                wast::QuoteWat::QuoteModule(span, _)
                | wast::QuoteWat::QuoteComponent(span, _) => *span,
            }
        }
        _ => return None,
    })
}

/// Extract the full s-expression starting at (or just before) `offset`.
///
/// Scans backwards from `offset` to find the opening `(`, then counts
/// parens forward until balanced to find the closing `)`. Returns the
/// extracted substring.
fn extract_sexp(source: &str, offset: usize) -> Option<String> {
    let bytes = source.as_bytes();
    // Scan backwards from offset to find the opening paren.
    let start = (0..offset)
        .rev()
        .find(|&i| bytes[i] == b'(')?;
    // Count parens forward to find the matching close.
    let mut depth = 0;
    for (i, &b) in bytes[start..].iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(source[start..start + i + 1].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// Compute the 1-indexed line number for a byte offset in source text.
fn line_number(source: &str, offset: usize) -> usize {
    source[..offset.min(source.len())]
        .bytes()
        .filter(|&b| b == b'\n')
        .count()
        + 1
}

// --- Entry points ---

/// Child process entry point: run a single .wast file and print results
/// using the subprocess protocol.
fn child_run(name: &str, path: &Path) -> ! {
    // Parse mode from "int:foo" or "jit:foo" prefix.
    let mode = name
        .split_once(':')
        .and_then(|(prefix, _)| ExecMode::from_prefix(prefix))
        .unwrap_or(ExecMode::Interpreter);
    let mut runner = SpecRunner::new(mode);
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

    // Each spec file becomes two tests: int:<name> and jit:<name>.
    let all_tests: Vec<(String, std::path::PathBuf)> = files
        .into_iter()
        .flat_map(|(name, path)| {
            vec![
                (format!("int:{name}"), path.clone()),
                (format!("jit:{name}"), path),
            ]
        })
        .collect();

    let matched: Vec<_> = all_tests
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
    let is_tty = std::io::stdout().is_terminal();
    let timeout = Duration::from_secs(5);

    run_tests_parallel(
        "Spec Tests",
        matched,
        timeout,
        is_tty,
        detailed,
        cli.verbose,
    );
}
