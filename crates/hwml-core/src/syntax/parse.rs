use std::rc::Rc;

use crate::{db::Index, syntax, syntax::RcSyntax, syntax::Syntax};
use anyhow::Error;
use core::fmt::{Debug, Display};
use hwml_support::parsing::{
    at_end, get, is_ws, p_alt_token, p_alt_token_opt, p_match_byte, p_match_str, p_match_token,
    p_match_token_opt, p_name, p_name_opt, trace, Name, Result,
};

pub struct BindingEnv {
    /// The names in scope. Each new name is pushed on the end.
    names: Vec<String>,
}

impl BindingEnv {
    pub fn new() -> BindingEnv {
        BindingEnv { names: Vec::new() }
    }

    fn push(&mut self, name: String) {
        self.names.push(name);
    }

    fn find(&self, name: &str) -> Option<Index> {
        for (i, n) in self.names.iter().rev().enumerate() {
            if name == n.as_str() {
                return Some(Index::new(i));
            }
        }
        None
    }

    fn depth(&self) -> usize {
        self.names.len()
    }

    fn reset(&mut self, depth: usize) {
        self.names.truncate(depth);
    }
}

fn p_variable_opt(
    input: &[u8],
    cursor: &mut usize,
    env: &mut BindingEnv,
) -> Option<Result<RcSyntax>> {
    trace(input, *cursor, "p_variable_opt");

    let name = match p_name_opt(input, cursor) {
        Some(Ok(n)) => n,
        Some(Err(e)) => return Some(Err(e)),
        None => return None,
    };

    trace(input, *cursor, "p_variable_opt: got name");

    let text = name.str(input);
    match env.find(text) {
        None => Some(Err(Error::msg("unknown variable"))),
        Some(index) => Some(Ok(Syntax::variable_rc(index))),
    }
}

fn p_variable(input: &[u8], cursor: &mut usize, env: &mut BindingEnv) -> Result<RcSyntax> {
    match p_variable_opt(input, cursor, env) {
        Some(Ok(n)) => Ok(n),
        Some(Err(e)) => Err(e),
        None => Err(Error::msg("expected variable")),
    }
}

/// Parse a lambda.
fn p_lambda_opt(
    input: &[u8],
    cursor: &mut usize,
    env: &mut BindingEnv,
) -> Option<Result<RcSyntax>> {
    // Leading keyword.
    p_alt_token_opt(input, cursor, &["\\", "lambda", "fun", "λ"])?;
    trace(input, *cursor, "lambda");

    // Bound variable names.
    let mut binders: Vec<Name> = vec![];
    loop {
        match p_name_opt(input, cursor) {
            Some(Ok(name)) => binders.push(name),
            Some(Err(err)) => return Some(Err(err)),
            None => break,
        }
    }
    if binders.is_empty() {
        return Some(Err(Error::msg("expected binders")));
    }

    // Arrow.
    if let Err(e) = p_alt_token(input, cursor, &["|->", "↦"], "expected arrow") {
        return Some(Err(e));
    }

    // Extend the environment with bound variable names.
    let depth = env.depth();
    for name in &binders {
        env.push(name.str_owned(input));
    }

    // Body.
    let body = match p_term(input, cursor, env) {
        Ok(body) => body,
        Err(err) => {
            env.reset(depth);
            return Some(Err(err));
        }
    };

    // Reset the environment.
    env.reset(depth);

    // Build the lambdas around the body.
    let mut term = body;
    for _ in 0..binders.len() {
        term = Syntax::lambda_rc(term);
    }

    // Done.
    Some(Ok(term))
}

/// Parse an optional paren () group.
fn p_paren_group_opt(
    input: &[u8],
    cursor: &mut usize,
    env: &mut BindingEnv,
) -> Option<Result<RcSyntax>> {
    p_match_token_opt(input, cursor, "(")?;
    trace(input, *cursor, "p_paren_group_opt");

    let body = match p_term(input, cursor, env) {
        Ok(body) => body,
        Err(err) => return Some(Err(err)),
    };
    if let Err(e) = p_match_token(input, cursor, ")", "expected closing paren") {
        return Some(Err(e));
    }
    Some(Ok(body))
}

/// Parse a pi term.
fn p_pi_opt(input: &[u8], cursor: &mut usize, env: &mut BindingEnv) -> Option<Result<RcSyntax>> {
    // Leading keyword.
    p_alt_token_opt(input, cursor, &["∀", "forall"])?;
    trace(input, *cursor, "pi");

    // Bound variable names.
    let mut binders: Vec<Name> = vec![];
    loop {
        match p_name_opt(input, cursor) {
            Some(Ok(name)) => binders.push(name),
            Some(Err(e)) => return Some(Err(e)),
            None => break,
        }
    }
    if binders.is_empty() {
        return Some(Err(Error::msg("expected binder")));
    }

    // Colon.
    if let Err(e) = p_match_token(input, cursor, ":", "expected type annotation") {
        return Some(Err(e));
    };

    // Source type.
    let src = match p_term(input, cursor, env) {
        Ok(ty) => ty,
        Err(err) => return Some(Err(err)),
    };

    // Arrow.
    if let Err(e) = p_alt_token(input, cursor, &["->", "→"], "expected arrow") {
        return Some(Err(e));
    }

    // Extend the environment with bound variable names.
    let depth = env.depth();
    for name in &binders {
        env.push(name.str_owned(input));
    }

    // Target type.
    let tgt = match p_term(input, cursor, env) {
        Ok(body) => body,
        Err(err) => {
            env.reset(depth);
            return Some(Err(err));
        }
    };

    // Reset the environment.
    env.reset(depth);

    // Build the pis around the target type.
    let mut term = tgt;
    for _ in 0..binders.len() {
        term = Syntax::pi_rc(src.clone(), term)
    }

    // Done.
    Some(Ok(term))
}

////////////////////////////
/// Term Parsing

/// Parse an optional atomic term.
fn p_atomic_term_opt(
    input: &[u8],
    cursor: &mut usize,
    env: &mut BindingEnv,
) -> Option<Result<RcSyntax>> {
    trace(input, *cursor, "p_atomic_term_opt");
    if let Some(lam) = p_lambda_opt(input, cursor, env) {
        return Some(lam);
    }
    if let Some(pi) = p_pi_opt(input, cursor, env) {
        return Some(pi);
    }
    if let Some(group) = p_paren_group_opt(input, cursor, env) {
        return Some(group);
    }
    if let Some(var) = p_variable_opt(input, cursor, env) {
        return Some(var);
    }
    None
}

fn p_term_opt(input: &[u8], cursor: &mut usize, env: &mut BindingEnv) -> Option<Result<RcSyntax>> {
    let mut term = match p_atomic_term_opt(input, cursor, env) {
        Some(Ok(term)) => term,
        Some(Err(err)) => return Some(Err(err)),
        None => return None,
    };

    loop {
        let arg = match p_atomic_term_opt(input, cursor, env) {
            Some(Ok(arg)) => arg,
            Some(Err(err)) => return Some(Err(err)),
            None => break,
        };
        term = Syntax::application_rc(term, arg);
    }

    Some(Ok(term))
}

pub fn p_term(input: &[u8], cursor: &mut usize, env: &mut BindingEnv) -> Result<RcSyntax> {
    match p_term_opt(input, cursor, env) {
        Some(Ok(term)) => Ok(term),
        Some(Err(err)) => Err(err),
        None => Err(Error::msg("expected term")),
    }
}

pub fn parse_syntax(input: &[u8], cursor: &mut usize) -> Result<RcSyntax> {
    let mut env = BindingEnv::new();
    p_term(input, cursor, &mut env)
}
