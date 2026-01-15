use clap::Parser;
use hwml_core::{syn, val};
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[clap(author = "Andrew Young", version, about)]
/// Application configuration
struct Args {
    /// whether to be verbose.
    #[arg(short = 'v')]
    verbose: bool,
    /// Whether to run in "core mode" or "surface mode".
    #[arg(short = 'c', long = "core")]
    core: bool,
    /// input file to read.
    #[arg(short = 'f', long = "file")]
    file: PathBuf,
}

fn main() {
    let args = Args::parse();
    if args.verbose {
        println!("DEBUG {args:?}");
    }

    if args.core {
        run_core(args);
        return;
    }

    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");
    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());

    let Some(program) = parse_result else {
        println!("Failed to parse");
        return;
    };
    println!("Program: {program:?}");
    // let db = hwml_core::Database::new();
    // let elab_result = hwml_elab::go(&db, program);
    // let Ok(module) = elab_result else {
    //     println!("Failed to elaborate");
    //     return;
    // };
    // println!("Elaborated:");
    // for decl in module.declarations() {
    //     println!("{decl:?}");
    // }

    // let program = result.unwrap();
    // let prog: Prog = AstMakerGuy::ne(&nodes, &loc, &toks, &contents).create_prog(program);

    //     println!("Program: {program:?}");

    // if args.verbose {
    //     println!("File contents:\n{contents}");
    // }

    println!("Done.")
}

fn run_core(args: Args) {
    let path = args.file.canonicalize().unwrap();
    let input = fs::read_to_string(&path).expect("Should have been able to read the file");

    let db = hwml_core::Database::new();
    let syn_tm = match hwml_core::syn::parse_syntax(&db, &input) {
        Ok(s) => s,
        Err(e) => {
            println!("parse error: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        println!("Parsed syntax: {:#?}", syn_tm);
    }

    let mut globals = val::GlobalEnv::new();
    hwml_core::prelude::load(&db, &mut globals);

    let mut tc_env = hwml_core::check::TCEnvironment {
        values: val::Environment::new(&globals),
        types: Vec::new(),
    };
    let sem_ty = match hwml_core::check::type_synth(&mut tc_env, &syn_tm) {
        Ok(ty) => ty,
        Err(e) => {
            println!("check error: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        println!("Sem Ty: {:#?}", sem_ty);
    }

    let mut env = val::Environment {
        global: &globals,
        local: val::LocalEnv::new(),
    };
    let sem_tm = match hwml_core::eval::eval(&mut env, &syn_tm) {
        Ok(s) => s,
        Err(e) => {
            println!("eval error: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        println!("Evaluated to: {:#?}", sem_tm);
    }

    let syn_ty = match hwml_core::quote::quote_type(&db, &env.global, 0, &sem_ty) {
        Ok(s) => s,
        Err(e) => {
            println!("error quoting type: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        print!("Type: ");
        hwml_core::syn::dump_syntax(&db, &syn_ty);
    }

    let syn_tm = match hwml_core::quote::quote_normal(
        &db,
        &env.global,
        0,
        &hwml_core::val::Normal::new(sem_ty, sem_tm),
    ) {
        Ok(s) => s,
        Err(e) => {
            println!("error quoting term: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        print!("Type: ");
        hwml_core::syn::dump_syntax(&db, &syn_ty);
    }

    let syn_ch = syn::Syntax::check(syn_ty, syn_tm);
    hwml_core::syn::dump_syntax(&db, &syn_ch);
}
