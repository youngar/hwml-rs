use anyhow::Error;
use hwml_core::syntax::{
    dump_syntax,
    parse::{p_term, BindingEnv},
    RcSyntax, Syntax,
};
use hwml_support::{
    line_info::LineInfo,
    parsing::{p_match_token, p_match_token_opt},
};
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug)]
pub struct Document {
    commands: Vec<Command>,
}

impl Document {
    pub fn new() -> Document {
        Document { commands: vec![] }
    }
}

#[derive(Clone, Debug)]
pub enum Command {
    Print(RcSyntax),
    Eq(RcSyntax, RcSyntax),
    Ne(RcSyntax, RcSyntax),
    Synth(RcSyntax),
    Check(RcSyntax, RcSyntax),
    Eval(RcSyntax),
    Error,
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Config {
    pub file_name: Option<String>,
    pub line_info: Option<LineInfo>,
}

impl Config {
    pub fn new() -> Config {
        Config {
            file_name: None,
            line_info: None,
        }
    }

    pub fn with_file_name(mut self, file_name: String) -> Config {
        self.file_name = Some(file_name);
        self
    }

    pub fn with_line_info(mut self, line_info: LineInfo) -> Config {
        self.line_info = Some(line_info);
        self
    }
}

/// The immutable state.
pub struct Context {
    pub path: Option<PathBuf>,
    pub line_info: Option<LineInfo>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            path: None,
            line_info: None,
        }
    }

    pub fn set_path(&mut self, path: PathBuf) -> &mut Context {
        self.path = Some(path);
        self
    }

    pub fn set_line_info(&mut self, line_info: LineInfo) -> &mut Context {
        self.line_info = Some(line_info);
        self
    }
}

/// The mutable state.
pub struct State {
    context: Context,
    error_occurred: bool,
}

impl State {
    pub fn new(context: Context) -> State {
        State {
            context,
            error_occurred: false,
        }
    }

    pub fn loc(&self, offset: usize) -> Option<(usize, usize)> {
        match &self.context.line_info {
            Some(info) => Some(info.loc(offset)),
            None => None,
        }
    }
}

/// #print <syntax>
pub fn p_cmd_print_opt(input: &[u8], cursor: &mut usize) -> Option<Result<Command>> {
    p_match_token_opt(input, cursor, "#print");

    let mut env = BindingEnv::new();
    let stx = match p_term(input, cursor, &mut env) {
        Ok(stx) => stx,
        Err(e) => return Some(Err(e)),
    };

    Some(Ok(Command::Print(stx)))
}

/// #synth <syntax>
pub fn p_cmd_synth_opt(input: &[u8], cursor: &mut usize) -> Option<Result<Command>> {
    p_match_token_opt(input, cursor, "#synth")?;

    let mut env = BindingEnv::new();
    let stx = match p_term(input, cursor, &mut env) {
        Ok(stx) => stx,
        Err(e) => return Some(Err(e)),
    };

    Some(Ok(Command::Synth(stx)))
}

/// #check <syntax> #is <syntax>
pub fn p_cmd_check_opt(input: &[u8], cursor: &mut usize) -> Option<Result<Command>> {
    p_match_token_opt(input, cursor, "#check")?;

    let mut env = BindingEnv::new();
    let stx = match p_term(input, cursor, &mut env) {
        Ok(stx) => stx,
        Err(e) => return Some(Err(e)),
    };

    if let Err(e) = p_match_token(input, cursor, "#is", "expected #is") {
        return Some(Err(e));
    }

    let mut env = BindingEnv::new();
    let ty = match p_term(input, cursor, &mut env) {
        Ok(stx) => stx,
        Err(e) => return Some(Err(e)),
    };

    Some(Ok(Command::Check(stx, ty)))
}

/// #eval <syntax>
pub fn p_cmd_eval_opt(input: &[u8], cursor: &mut usize) -> Option<Result<Command>> {
    if let None = p_match_token_opt(input, cursor, "#eval") {
        return None;
    }
    let mut env = BindingEnv::new();
    let stx = match p_term(input, cursor, &mut env) {
        Ok(stx) => stx,
        Err(e) => return Some(Err(e)),
    };

    Some(Ok(Command::Eval(stx)))
}

pub fn p_command_opt(input: &[u8], cursor: &mut usize) -> Option<Result<Command>> {
    if let Some(cmd) = p_cmd_print_opt(input, cursor) {
        return Some(cmd);
    }
    if let Some(cmd) = p_cmd_synth_opt(input, cursor) {
        return Some(cmd);
    }
    if let Some(cmd) = p_cmd_check_opt(input, cursor) {
        return Some(cmd);
    }
    if let Some(cmd) = p_cmd_eval_opt(input, cursor) {
        return Some(cmd);
    }
    None
}

pub fn p_document(input: &[u8], cursor: &mut usize) -> Result<Document> {
    let mut doc = Document::new();

    loop {
        match p_command_opt(input, cursor) {
            Some(Ok(cmd)) => doc.commands.push(cmd),
            Some(Err(e)) => return Err(e),
            None => break,
        }
    }

    Ok(doc)
}

pub fn run_file<P: AsRef<Path>>(path: P) -> Result<()> {
    // Load the file.
    let Ok(contents) = fs::read_to_string(&path) else {
        let msg = format!("Could not open file: {}", path.as_ref().display());
        return Err(anyhow::Error::msg(msg));
    };

    // Build the context.
    let mut ctx = Context::new();
    ctx.set_path(PathBuf::from(path.as_ref()));
    ctx.set_line_info(LineInfo::from_str(&contents));

    // Parse the file.
    let input = contents.as_bytes();
    let mut cursor = 0;
    let doc = match p_document(&input, &mut cursor) {
        Ok(doc) => doc,
        Err(e) => return Err(e),
    };

    // Run the file.
    run_document(ctx, &doc)
}

pub fn run_document(ctx: Context, doc: &Document) -> Result<()> {
    let mut state = State::new(ctx);

    for cmd in &doc.commands {
        run_command(&mut state, cmd);
    }

    if state.error_occurred {
        Err(Error::msg("Error occurred during execution."))
    } else {
        Ok(())
    }
}

pub fn run_command(state: &mut State, cmd: &Command) {
    match cmd {
        Command::Print(term) => run_print(state, &*term),
        Command::Eq(lhs, rhs) => run_eq(state, &*lhs, &*rhs),
        Command::Ne(lhs, rhs) => run_ne(state, &*lhs, &*rhs),
        Command::Synth(term) => run_synth(state, &*term),
        Command::Check(term, ty) => run_check(state, &*term, &*ty),
        Command::Eval(term) => run_eval(state, &*term),
        Command::Error => state.error_occurred = true,
    }
}

fn run_print(_state: &mut State, term: &Syntax) {
    hwml_core::syntax::dump_syntax(term);
}

fn run_eq(state: &mut State, lhs: &Syntax, rhs: &Syntax) {}

fn run_ne(state: &mut State, lhs: &Syntax, rhs: &Syntax) {}

fn run_synth(state: &mut State, term: &Syntax) {
    use hwml_core::*;
    match check::type_synth(&mut vec![], term) {
        Ok(sem_type) => match quote::quote_type(0, &*sem_type) {
            Ok(ty) => dump_syntax(&*ty),
            Err(err) => {
                println!("failed to quote type: {:?}", err);
                state.error_occurred = true;
            }
        },
        Err(err) => {
            println!("failed to synthesize type: {:?}", err);
            state.error_occurred = true;
        }
    }
}

fn run_check(state: &mut State, term: &Syntax, ty: &Syntax) {}

fn run_eval(state: &mut State, term: &Syntax) {}
