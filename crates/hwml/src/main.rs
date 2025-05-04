use clap::Parser;
use hwml_db::db::*;
// use hwml_parser::grammar;
use salsa::Setter;
use std::env;
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

    if args.verbose {
        println!("File contents:\n{contents}");
    }
    let db = HwmlDatabase::new();
    let file = File::new(&db, contents);
    {
        let program = parse_program(&db, file);
        let diagnostics = parse_program::accumulated::<Diagnostics>(&db, file);
        let line_info = get_line_info(&db, file);

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
}
