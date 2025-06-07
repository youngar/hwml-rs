use clap::Parser;
use la_arena;
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
    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");
    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());

    match parse_result {
        Some(program) => println!("Program: {program:?}"),
        _ => println!("Failed to parse"),
    }

    // let program = result.unwrap();
    // let prog: Prog = AstMakerGuy::new(&nodes, &loc, &toks, &contents).create_prog(program);

    //     println!("Program: {program:?}");

    // if args.verbose {
    //     println!("File contents:\n{contents}");
    // }

    println!("Done.")
}
