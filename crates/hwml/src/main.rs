// use clap::{Args, Parser, Subcommand};
use clap::Parser;
use hwml_db::db::*;
use salsa::Setter;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Termination;
use hwml_core as core;
// use hwml_parser::grammar;

/// Application configuration.
#[derive(clap::Parser, Debug)]
#[clap(author = "Andrew Young", version, about)]
struct Args {
    /// The main command to run.
    #[command(subcommand)]
    subcommand: Subcommand,

    /// The global options.
    #[clap(flatten)]
    global: GlobalArgs,
}

/// Global configuration options.
#[derive(clap::Args, Debug)]
struct GlobalArgs {
    #[arg(short = 'v', long = "verbose")]
    verbose: bool,

    #[arg(long = "debug")]
    debug: bool,
}

/// The main subcommands for the hwml executable.
#[derive(clap::Subcommand, Debug)]
enum Subcommand {
    Gen(GenArgs),
    Dev(DevArgs),
}

/// The main compilation subcommand.
#[derive(clap::Args, Debug)]
struct GenArgs {
    #[arg()]
    files: Vec<PathBuf>,
}

/// The development shell subcommand.
#[derive(clap::Args, Debug)]
struct DevArgs {
    #[arg()]
    files: Vec<PathBuf>,
}

fn main() -> std::process::ExitCode {
    let args = Args::parse();
    if args.global.verbose {
        println!("DEBUG {args:?}");
    }
<<<<<<< HEAD
    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");
||||||| parent of 6d0a708 (Add a core language)
    let contents = fs::read_to_string(&args.file).expect("Should have been able to read the file");
=======
    match args.subcommand {
        Subcommand::Dev(dev_args) => cmd_dev(&args.global, &dev_args),
        Subcommand::Gen(gen_args) => cmd_gen(&args.global, &gen_args),
    }
}
>>>>>>> 6d0a708 (Add a core language)

fn cmd_gen(global_args: &GlobalArgs, args: &GenArgs) -> std::process::ExitCode {
    for file in &args.files {
        let contents = fs::read_to_string(file).expect("Should have been able to read the file");
        if global_args.verbose {
            println!("File contents:\n{contents}");
        }
        let mut errors = Vec::new();
        let result = hwml_parser::grammar::ProgramParser::new().parse(&mut errors, &contents);
        println!("Result: {result:?}");
        let program = result.unwrap();
        println!("Program: {program:?}");
        println!("Errors: {errors:?}");
    }
    let db = HwmlDatabase::new();
    let file = File::new(&db, contents);
    {
        let program = parse_program(&db, file);
        let diagnostics = parse_program::accumulated::<Diagnostics>(&db, file);
        let line_info = get_line_info(&db, file);

<<<<<<< HEAD
        // Get current working directory
        let cwd = env::current_dir().unwrap();

        for diagnostic in diagnostics {
            let (line, col) = line_info.loc(diagnostic.0.span.start);
            let relative_path = path.strip_prefix(&cwd).unwrap_or(&path);
            println!(
                "{:?}:{}:{}:{}",
                relative_path, line, col, diagnostic.0.message
            );
        }
        //println!("Diagnostics: {diagnostics:?}");
        println!("Program: {program:?}");
    }
    let mut db = db.clone();
    file.set_text(&mut db).to("".to_string());
||||||| parent of 6d0a708 (Add a core language)
    let mut errors = Vec::new();
    let result = hwml_parser::grammar::ProgramParser::new().parse(&mut errors, &contents);
    println!("Result: {result:?}");
    let program = result.unwrap();
    println!("Program: {program:?}");
    println!("Errors: {errors:?}");
=======
    std::process::ExitCode::SUCCESS
}

fn cmd_dev(global_args: &GlobalArgs, args: &DevArgs) -> std::process::ExitCode {
    if args.files.is_empty() {
        println!("No files provided");
    }

    for file in &args.files {
        let result = hwml_dev::run_file(file);
        if result.is_err() {
            return result.report();
        }
    }

    std::process::ExitCode::SUCCESS
>>>>>>> 6d0a708 (Add a core language)
}
