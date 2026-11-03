// released under BSD 3-Clause License

use clap::Parser;
use std::io::Write;

#[derive(Parser, Debug)]
#[command(name = "btor2lean")]
#[command(version)]
#[command(about = "Translates a btor2 file into Lean.", long_about = None)]
struct Args {
    #[arg(value_name = "INPUT", index = 1)]
    input_file: std::path::PathBuf,
    /// Output file. Writes to stdout if omitted.
    #[arg(short, long, value_name = "OUTPUT")]
    output: Option<std::path::PathBuf>,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let (ctx, sys) =
        patronus::btor2::parse_file(&args.input_file).expect("failed to parse btor2 file");

    match args.output {
        Some(path) => {
            let mut out = std::io::BufWriter::new(std::fs::File::create(path)?);
            patronus_lean::translate(&ctx, &sys, &mut out)?;
            out.flush()
        }
        None => patronus_lean::translate(&ctx, &sys, &mut std::io::stdout().lock()),
    }
}
