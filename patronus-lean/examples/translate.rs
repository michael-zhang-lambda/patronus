// released under BSD 3-Clause License

//! Translate a BTOR2 file into Lean.
//!
//!     cargo run -p patronus-lean --example translate -- <input.btor> [output.lean]
//!
//! Writes to stdout if no output path is given.

use patronus::btor2;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 || args.len() > 3 {
        eprintln!("usage: {} <input.btor> [output.lean]", args[0]);
        std::process::exit(1);
    }
    let (ctx, sys) = btor2::parse_file(&args[1])
        .unwrap_or_else(|| panic!("failed to parse BTOR2 file {}", args[1]));
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    match args.get(2) {
        Some(out) => std::fs::write(out, lean).expect("failed to write output file"),
        None => print!("{lean}"),
    }
}
