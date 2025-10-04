use clap::Parser;
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

    let Some(program) = parse_result else {
        println!("Failed to parse");
        return;
    };
    println!("Program: {program:?}");
    let elab_result = hwml_elab::go(program);
    let Ok(declarations) = elab_result else {
        println!("Failed to elaborate");
        return;
    };
    println!("Elaborated:");
    for decl in declarations {
        println!("{decl:?}");
    }

    // let program = result.unwrap();
    // let prog: Prog = AstMakerGuy::ne(&nodes, &loc, &toks, &contents).create_prog(program);

    //     println!("Program: {program:?}");

    // if args.verbose {
    //     println!("File contents:\n{contents}");
    // }

    println!("Done.")
}
