use std::io::Read;

use clap::{Parser, Subcommand};
use wust::{Codegen, Engine, Module};

#[derive(Parser)]
#[command(name = "wust", about = "WebAssembly toolkit")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Inspect the compilation pipeline: WAT → IR → annotated aarch64.
    Inspect {
        /// Path to a .wat file. Reads from stdin if omitted.
        file: Option<String>,
    },
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Inspect { file } => inspect(file),
    }
}

fn inspect(file: Option<String>) -> anyhow::Result<()> {
    let wat = read_input(file)?;
    let wasm_bytes = wat::parse_str(&wat)?;
    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm_bytes)?;

    let output = Codegen::new(&module).compile()?;
    print!("{}", output.render_inspect());
    Ok(())
}

fn read_input(file: Option<String>) -> anyhow::Result<String> {
    match file {
        Some(path) => Ok(std::fs::read_to_string(&path)?),
        None => {
            let mut buf = String::new();
            std::io::stdin().read_to_string(&mut buf)?;
            Ok(buf)
        }
    }
}
