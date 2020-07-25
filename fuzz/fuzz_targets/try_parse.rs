#![no_main]

use libfuzzer_sys::fuzz_target;
use souper_ir::parse::{
    parse_left_hand_sides_str, parse_replacements_str, parse_right_hand_sides_str,
};
use std::{fmt::Write, path::Path};

fuzz_target!(|data: &[u8]| {
    let _ = env_logger::try_init();

    let s = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    log::debug!("input string = \"\"\"\n{}\n\"\"\"", s);

    let filepath = Some(Path::new("fuzzer.data"));

    if let Ok(repl) = parse_replacements_str(s, filepath) {
        let mut canon1 = String::with_capacity(s.len() * 2);
        for r in &repl {
            writeln!(canon1, "{}", r).unwrap();
        }

        let repl2 = parse_replacements_str(&canon1, filepath)
            .expect("should re-parse our stringified source text");

        let mut canon2 = String::with_capacity(canon1.len());
        for r in &repl2 {
            writeln!(canon2, "{}", r).unwrap();
        }

        if canon1 != canon2 {
            log::debug!("canon1 = '''\n{}\n'''", canon1);
            log::debug!("canon2 = '''\n{}\n'''", canon2);
            panic!("failed to round-trip deterministically");
        }
    }

    if let Ok(lhs) = parse_left_hand_sides_str(s, filepath) {
        let mut canon1 = String::with_capacity(s.len() * 2);
        for l in &lhs {
            writeln!(canon1, "{}", l).unwrap();
        }

        let lhs2 = parse_left_hand_sides_str(&canon1, filepath)
            .expect("should re-parse our stringified source text");

        let mut canon2 = String::with_capacity(canon1.len());
        for l in &lhs2 {
            writeln!(canon2, "{}", l).unwrap();
        }

        if canon1 != canon2 {
            log::debug!("canon1 = '''\n{}\n'''", canon1);
            log::debug!("canon2 = '''\n{}\n'''", canon2);
            panic!("failed to round-trip deterministically");
        }
    }

    if let Ok(rhs) = parse_right_hand_sides_str(s, filepath) {
        let mut canon1 = String::with_capacity(s.len() * 2);
        for r in &rhs {
            writeln!(canon1, "{}", r).unwrap();
        }

        let rhs2 = parse_right_hand_sides_str(&canon1, filepath)
            .expect("should re-parse our stringified source text");

        let mut canon2 = String::with_capacity(canon1.len());
        for r in &rhs2 {
            writeln!(canon2, "{}", r).unwrap();
        }

        if canon1 != canon2 {
            log::debug!("canon1 = '''\n{}\n'''", canon1);
            log::debug!("canon2 = '''\n{}\n'''", canon2);
            panic!("failed to round-trip deterministically");
        }
    }
});
