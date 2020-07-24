#![no_main]

use libfuzzer_sys::fuzz_target;
use souper_ir::parse::{
    parse_left_hand_sides_str, parse_replacements_str, parse_right_hand_sides_str,
};
use std::path::Path;

fuzz_target!(|data: &[u8]| {
    let _ = env_logger::try_init();

    let s = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    log::debug!("input string = \"\"\"\n{}\n\"\"\"", s);

    let _ = parse_replacements_str(s, Some(Path::new("fuzzer.data")));
    let _ = parse_left_hand_sides_str(s, Some(Path::new("fuzzer.data")));
    let _ = parse_right_hand_sides_str(s, Some(Path::new("fuzzer.data")));
});
