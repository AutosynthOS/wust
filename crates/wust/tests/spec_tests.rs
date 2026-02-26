use std::path::Path;
use wust::{Engine, Instance, Linker, Module, Store, Val};

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

    fn run_wast(&mut self, path: &Path) -> (usize, usize) {
        let source = std::fs::read_to_string(path).unwrap();
        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = wast::parser::parse::<wast::Wast>(&buf).unwrap();

        let (mut passed, mut failed) = (0, 0);
        for directive in wast.directives {
            match self.run_directive(directive) {
                Ok(()) => passed += 1,
                Err(e) => {
                    failed += 1;
                    // eprintln!("  FAIL {e}");
                }
            }
        }
        (passed, failed)
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

// --- Test harness ---

fn run_spec_test(name: &str) {
    let path = Path::new("tests/spec/test/core").join(format!("{name}.wast"));
    assert!(path.exists(), "spec test not found: {}", path.display());
    let mut runner = SpecRunner::new();
    let (passed, failed) = runner.run_wast(&path);
    println!("{name}: {passed} passed, {failed} failed");
    assert_eq!(failed, 0, "{name}: {failed} assertions failed");
}

macro_rules! spec_tests {
    ($($name:ident => $file:expr),* $(,)?) => {
        $( #[test] fn $name() { run_spec_test($file); } )*
    };
    (ignored: $($name:ident => $file:expr),* $(,)?) => {
        $( #[test] #[ignore] fn $name() { run_spec_test($file); } )*
    };
}

spec_tests! {
    spec_address => "address",
    spec_align => "align",
    spec_block => "block",
    spec_br => "br",
    spec_br_if => "br_if",
    spec_br_table => "br_table",
    spec_call => "call",
    spec_call_indirect => "call_indirect",
    spec_comments => "comments",
    spec_const_ => "const",
    spec_conversions => "conversions",
    spec_custom => "custom",
    spec_data => "data",
    spec_elem => "elem",
    spec_endianness => "endianness",
    spec_exports => "exports",
    spec_f32 => "f32",
    spec_f32_bitwise => "f32_bitwise",
    spec_f32_cmp => "f32_cmp",
    spec_f64 => "f64",
    spec_f64_bitwise => "f64_bitwise",
    spec_f64_cmp => "f64_cmp",
    spec_fac => "fac",
    spec_float_exprs => "float_exprs",
    spec_float_literals => "float_literals",
    spec_float_memory => "float_memory",
    spec_float_misc => "float_misc",
    spec_forward => "forward",
    spec_func => "func",
    spec_func_ptrs => "func_ptrs",
    spec_global => "global",
    spec_i32 => "i32",
    spec_i64 => "i64",
    spec_if_ => "if",
    spec_int_exprs => "int_exprs",
    spec_int_literals => "int_literals",
    spec_labels => "labels",
    spec_left_to_right => "left-to-right",
    spec_load => "load",
    spec_local_get => "local_get",
    spec_local_set => "local_set",
    spec_local_tee => "local_tee",
    spec_loop_ => "loop",
    spec_memory => "memory",
    spec_memory_grow => "memory_grow",
    spec_memory_size => "memory_size",
    spec_memory_redundancy => "memory_redundancy",
    spec_memory_trap => "memory_trap",
    spec_nop => "nop",
    spec_return_ => "return",
    spec_select => "select",
    spec_stack => "stack",
    spec_start => "start",
    spec_store_ => "store",
    spec_switch => "switch",
    spec_table => "table",
    spec_table_get => "table_get",
    spec_table_grow => "table_grow",
    spec_table_set => "table_set",
    spec_table_size => "table_size",
    spec_token => "token",
    spec_traps => "traps",
    spec_type_ => "type",
    spec_type_canon => "type-canon",
    spec_unreachable => "unreachable",
    spec_unreached_invalid => "unreached-invalid",
    spec_unreached_valid => "unreached-valid",
    spec_unwind => "unwind",
    spec_annotations => "annotations",
    spec_binary => "binary",
    spec_binary_leb128 => "binary-leb128",
    spec_id => "id",
    spec_inline_module => "inline-module",
    spec_local_init => "local_init",
    spec_obsolete_keywords => "obsolete-keywords",
    spec_ref_ => "ref",
    spec_ref_func => "ref_func",
    spec_ref_is_null => "ref_is_null",
    spec_ref_null => "ref_null",
    spec_utf8_custom_section_id => "utf8-custom-section-id",
    spec_utf8_import_field => "utf8-import-field",
    spec_utf8_import_module => "utf8-import-module",
    spec_utf8_invalid_encoding => "utf8-invalid-encoding",
    spec_imports => "imports",
    spec_instance => "instance",
    spec_linking => "linking",
    spec_names => "names",
    spec_br_on_non_null => "br_on_non_null",
    spec_br_on_null => "br_on_null",
    spec_call_ref => "call_ref",
    spec_ref_as_non_null => "ref_as_non_null",
    spec_return_call => "return_call",
    spec_return_call_indirect => "return_call_indirect",
    spec_return_call_ref => "return_call_ref",
    spec_type_equivalence => "type-equivalence",
    spec_type_rec => "type-rec",
}

// spec_tests! { ignored:
// }
