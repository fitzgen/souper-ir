use anyhow::Context;
use std::{env, fs, io::Write, path::PathBuf};

fn main() -> anyhow::Result<()> {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(
        env::var_os("OUT_DIR").expect("The OUT_DIR environment variable must be set"),
    );

    let souper_tests = PathBuf::from("souper").join("test");
    println!("cargo:rerun-if-changed={}", souper_tests.display());

    let test_file_path = out_dir.join("souper_tests.rs");
    let mut out = fs::File::create(&test_file_path)
        .with_context(|| format!("failed to create file: {}", test_file_path.display()))?;

    if !souper_tests.exists() {
        return missing_souper_submodule();
    }

    for entry in walkdir::WalkDir::new(souper_tests) {
        let entry = entry?;
        if entry.path().extension().map_or(false, |x| x == "opt") {
            println!("cargo:rerun-if-changed={}", entry.path().display());

            let test_name = entry
                .path()
                .display()
                .to_string()
                .chars()
                .map(|c| match c {
                    'a'..='z' | 'A'..='Z' | '0'..='9' => c,
                    _ => '_',
                })
                .collect::<String>();

            // FIXME: https://github.com/google/souper/pull/784
            let ignore = if entry.file_name() == "pruning.opt" {
                "#[ignore]"
            } else {
                ""
            };

            writeln!(
                out,
                "\
#[test]
#[allow(non_snake_case)]
{}
fn test_{}() {{
    crate::assert_parse_file(std::path::Path::new(\"{}\"));
}}
",
                ignore,
                test_name,
                entry.path().display()
            )
            .with_context(|| format!("failed to write to file: {}", test_file_path.display()))?;
        }
    }

    Ok(())
}

fn missing_souper_submodule() -> anyhow::Result<()> {
    println!(
        "cargo:warning=The `souper` submodule is not checked out, \
         skipping some tests generation"
    );
    Ok(())
}
