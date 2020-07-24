use std::path::Path;

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
}

#[cfg(test)]
mod tests {
    include!(concat!(env!("OUT_DIR"), "/", "souper_tests.rs"));
}
