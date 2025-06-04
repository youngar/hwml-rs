use clap::Parser;
use hwml_db::cst::Assoc;
use hwml_db::cst::Location;
use hwml_db::cst::Node;
use hwml_db::db::*;
use hwml_db::parsing::Token;
use hwml_db::parsing::TokenKind;
use hwml_db::parsing::T;
use la_arena;
use la_arena::Idx;
use la_arena::RawIdx;
use lalrpop_util::ErrorRecovery;
use salsa::Setter;
use std::collections::BTreeMap;
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

#[salsa::interned]
pub struct Id<'db> {
    #[return_ref]
    pub text: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct App {
    head: Box<Expr>,
    arg: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Var {
    name: Id,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Expr {
    App(App),
    Var(Var),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Def<'db> {
    name: Id<'db>,
    value: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Prog<'db> {
    defs: Vec<Def<'db>>,
}

/////// Errors
struct Error {}
type Result<T> = std::result::Result<T, Error>;

////// Create an ast thingy.
struct AstMakerGuy<'a> {
    nodes: &'a la_arena::Arena<Node>,
    loc: &'a la_arena::Arena<Location>,

    tokens: &'a la_arena::Arena<Token>,
    token_index: Idx<Token>,

    contents: &'a str,
    contents_index: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Operator<'db> {
    name_parts: Vec<Id<'db>>,
    associativity: Assoc,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Precedence<'db> {
    none: Vec<Operator<'db>>,
    left: Vec<Operator<'db>>,
    right: Vec<Operator<'db>>,
}

impl<'db> Precedence<'db> {
    fn new() -> Precedence<'db> {
        Precedence {
            none: Vec::new(),
            left: Vec::new(),
            right: Vec::new(),
        }
    }

    fn insert(&mut self, assoc: Assoc, operator: Operator<'db>) {
        match assoc {
            Assoc::Left => self.left.push(operator),
            Assoc::Right => self.right.push(operator),
            Assoc::None => self.none.push(operator),
        }
    }
}

type PrecedenceGraph<'db> = BTreeMap<u8, Precedence<'db>>;

impl<'a> AstMakerGuy<'a> {
    fn new(
        nodes: &'a la_arena::Arena<Node>,
        loc: &'a la_arena::Arena<Location>,
        tokens: &'a la_arena::Arena<Token>,
        contents: &'a str,
    ) -> AstMakerGuy<'a> {
        AstMakerGuy {
            nodes,
            loc,
            tokens,
            token_index: Idx::from_raw((0u32).into()),
            contents,
            contents_index: 0,
        }
    }

    fn get_node(&self, idx: Idx<Node>) -> &Node {
        &self.nodes[idx]
    }

    fn create_scopes(&mut self, idx: Idx<Node>) {
        let Node::Program(program) = self.get_node(idx) else {
            panic!("Expected program node");
        };

        // Collect all defs
        let mut prec_graph: PrecedenceGraph = BTreeMap::new();
        for idx in program.stmt_indices.iter() {
            let Node::Def(def) = self.get_node(*idx) else {
                panic!("Expected def node");
            };
            defs.insert(def.precedence, def.assoc, def.id);
        }
    }

    fn create_prog(&mut self, idx: Idx<Node>) -> Prog {
        //let node_index: u32 = self.nodes.len() as u32;
        // let node_index = Idx::from_raw((self.nodes.len() as u32).into());
        let Node::Program(data) = self.get_node(idx) else {
            panic!("Expected program node");
        };

        self.create_scopes(idx);

        // self.skip_token_to_node(node_index);

        // assert!(matches!(node, Node::Program(_)));

        let mut defs = Vec::new();
        // while node_index != 0 {
        //     let def = self.parse_def(node_index);
        //     defs.push(def);
        // }
        Prog { defs }
    }
}

fn main() {
    let args = Args::parse();
    if args.verbose {
        println!("DEBUG {args:?}");
    }
    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");

    let toks = hwml_db::parsing::lex(contents.as_bytes());
    for tok in toks.clone() {
        println!("{:?}", tok);
    }

    let parser = hwml_db::parsing::grammar::ProgramParser::new();
    let mut nodes = la_arena::Arena::new();
    let mut loc = la_arena::Arena::new();
    let mut errors = Vec::new();
    let mut offset: usize = 0;
    let mut index: u32 = 0;
    let result = parser.parse(
        contents.as_str(),
        &mut nodes,
        &mut loc,
        &mut errors,
        toks.iter().filter_map(|(_, tok)| {
            let i = index;
            let start = offset;

            index = index + 1;
            offset += tok.size as usize;

            let kind = tok.kind;
            let str = &contents[start..offset];

            let c = tok.clone();
            eprintln!(
                "index: {index}, offset: {offset}, token: {c:?}, str: {:?}",
                &contents[start..offset]
            );

            if tok.is_trivia() {
                return None;
            }
            Some((i, T { kind, str }, i + 1))
        }),
    );

    match result {
        Ok(program) => println!("Program: {program:?}"),
        Err(err) => {
            println!("Error: {err:?}");
            return;
        }
    }

    let program = result.unwrap();
    let prog: Prog = AstMakerGuy::new(&nodes, &loc, &toks, &contents).create_prog(program);

    //     println!("Program: {program:?}");

    // if args.verbose {
    //     println!("File contents:\n{contents}");
    // }
    // let db = HwmlDatabase::new();
    // let file = File::new(&db, contents);
    // {
    //     let program = parse_program(&db, file);
    //     let diagnostics = parse_program::accumulated::<Diagnostics>(&db, file);
    //     let line_info = get_line_info(&db, file);

    //     // Get current working directory
    //     let cwd = env::current_dir().unwrap();

    //     for diagnostic in diagnostics {
    //         let (line, col) = line_info.loc(diagnostic.0.span.start);
    //         let relative_path = path.strip_prefix(&cwd).unwrap_or(&path);
    //         println!(
    //             "{:?}:{}:{}:{}",
    //             relative_path, line, col, diagnostic.0.message
    //         );
    //     }
    //     //println!("Diagnostics: {diagnostics:?}");
    //     println!("Program: {program:?}");
    // }
    // let mut db = db.clone();
    // file.set_text(&mut db).to("".to_string());

    println!("Done.")
}
