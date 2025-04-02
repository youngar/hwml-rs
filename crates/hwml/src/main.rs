use clap::Parser;
use hwml_parser::grammar;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[clap(author = "Andrew Young", version, about)]
/// Application configuration
struct Args {
    /// whether to be verbose
    #[arg(short = 'v')]
    verbose: bool,

    /// input file to read
    #[arg(short = 'f', long = "file")]
    file: PathBuf,
}

fn main() {
    let args = Args::parse();
    if args.verbose {
        println!("DEBUG {args:?}");
    }
    let contents = fs::read_to_string(&args.file).expect("Should have been able to read the file");

    if args.verbose {
        println!("File contents:\n{contents}");
    }

    let mut errors = Vec::new();
    let result = hwml_parser::grammar::ProgramParser::new().parse(&mut errors, &contents);
    println!("Result: {result:?}");
    let program = result.unwrap();
    println!("Program: {program:?}");
    println!("Errors: {errors:?}");
}
