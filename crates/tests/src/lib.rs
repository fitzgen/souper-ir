use std::{fmt::Write, path::Path};

pub fn assert_parse_file(path: &Path) {
    let s = std::fs::read_to_string(path).unwrap();

    let repl = souper_ir::parse::parse_replacements_str(&s, Some(path));
    let lhs = souper_ir::parse::parse_left_hand_sides_str(&s, Some(path));
    let rhs = souper_ir::parse::parse_right_hand_sides_str(&s, Some(path));

    assert!(
        repl.is_ok() || lhs.is_ok() || rhs.is_ok(),
        "souper test file {:?} failed to parse as a replacement, LHS, or RHS.

Parse replacement error: {}

Parse LHS error: {}

Parse RHS error: {}",
        path,
        repl.unwrap_err().to_string(),
        lhs.unwrap_err().to_string(),
        rhs.unwrap_err().to_string(),
    );

    // Check that we can deterministically round-trip replacements.
    if let Ok(repl) = repl {
        let mut canonical_string_1 = String::new();
        for r in &repl {
            writeln!(&mut canonical_string_1, "{}\n", r).unwrap();
        }

        let repl_2 = souper_ir::parse::parse_replacements_str(&canonical_string_1, Some(path))
            .expect("should parse our stringified IR okay");

        let mut canonical_string_2 = String::new();
        for r in &repl_2 {
            writeln!(&mut canonical_string_2, "{}\n", r).unwrap();
        }

        assert_eq!(
            canonical_string_1, canonical_string_2,
            "re-stringifying should generate the same string",
        );
    }

    // Check that we can deterministically round-trip LHSes.
    if let Ok(lhs) = lhs {
        let mut canonical_string_1 = String::new();
        for l in &lhs {
            writeln!(&mut canonical_string_1, "{}\n", l).unwrap();
        }

        let lhs_2 = souper_ir::parse::parse_left_hand_sides_str(&canonical_string_1, Some(path))
            .expect("should parse our stringified IR okay");

        let mut canonical_string_2 = String::new();
        for l in &lhs_2 {
            writeln!(&mut canonical_string_2, "{}\n", l).unwrap();
        }

        assert_eq!(
            canonical_string_1, canonical_string_2,
            "re-stringifying should generate the same string",
        );
    }

    // Check that we can deterministically round-trip RHSes.
    if let Ok(rhs) = rhs {
        let mut canonical_string_1 = String::new();
        for r in &rhs {
            writeln!(&mut canonical_string_1, "{}\n", r).unwrap();
        }

        let rhs_2 = souper_ir::parse::parse_right_hand_sides_str(&canonical_string_1, Some(path))
            .expect("should parse our stringified IR okay");

        let mut canonical_string_2 = String::new();
        for r in &rhs_2 {
            writeln!(&mut canonical_string_2, "{}\n", r).unwrap();
        }

        assert_eq!(
            canonical_string_1, canonical_string_2,
            "re-stringifying should generate the same string",
        );
    }
}

#[cfg(test)]
mod tests {
    include!(concat!(env!("OUT_DIR"), "/", "souper_tests.rs"));
}
