use autosynth_ir::{CodeCtx, Operand, VCode};

/// Assert a block's VCode stream matches the expected sequence.
///
/// On mismatch, prints a colored unified diff:
///   green (+) = expected but missing
///   red   (-) = got but unexpected
///   dim       = matching lines
pub fn assert_stream_eq(block: &CodeCtx, expected: &[VCode]) {
    let got: Vec<&VCode> = block.stream.iter().collect();
    let exp: Vec<&VCode> = expected.iter().collect();

    if got == exp {
        return;
    }

    let got_lines: Vec<String> = block.stream.iter().map(format_item).collect();
    let exp_lines: Vec<String> = expected.iter().map(format_item).collect();

    let mut msg = String::from("\nstream mismatch:\n");

    let max = got_lines.len().max(exp_lines.len());
    for i in 0..max {
        let g = got_lines.get(i);
        let e = exp_lines.get(i);
        match (g, e) {
            (Some(g), Some(e)) if g == e => {
                // Match — dim
                msg.push_str(&format!("  \x1b[2m{g}\x1b[0m\n"));
            }
            (Some(g), Some(e)) => {
                // Mismatch — show both
                msg.push_str(&format!("  \x1b[31m- {g}\x1b[0m\n"));
                msg.push_str(&format!("  \x1b[32m+ {e}\x1b[0m\n"));
            }
            (Some(g), None) => {
                // Extra in got
                msg.push_str(&format!("  \x1b[31m- {g}\x1b[0m\n"));
            }
            (None, Some(e)) => {
                // Missing from got
                msg.push_str(&format!("  \x1b[32m+ {e}\x1b[0m\n"));
            }
            (None, None) => unreachable!(),
        }
    }

    panic!("{msg}");
}

fn format_item(item: &VCode) -> String {
    match item {
        VCode::Operand(op) => format!("  {}", format_operand(op)),
        inst => format!("{inst:?}"),
    }
}

fn format_operand(op: &Operand) -> String {
    match op {
        Operand::Const(v) => format!("Const({v})"),
        Operand::VReg(v) => format!("{v}"),
        Operand::PReg(p) => format!("x{}", p.0),
        Operand::Mem(s) => format!("Mem({s:?})"),
        Operand::UImm12(i) => format!("#{}", i.value()),
    }
}
