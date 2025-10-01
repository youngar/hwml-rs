use crate::*;
use anyhow::{anyhow, Result};
use hwml_core::{syn::Syntax, *};

pub fn solve_equality(state: &mut State, cons: EqualityConstraint) -> Result<()> {
    println!("solving equality: {:?}", cons);
    let lhs = cons.lhs;
    let rhs = cons.rhs;

    if lhs == rhs {
        println!("constraints are equal");
        return Ok(());
    }

    // Try reducing the terms and try again.

    // If the two terrms are telescopes headed by constants, we can unify the spines.

    // Same thing for Lam e == Lam f ~> e == f

    // Pi x y == Pi a b _> x == a && y == b
    // Pi Injectivity - two pis are equal if their source and target are equal.
    if let Syntax::Pi(pi1) = &*lhs {
        if let Syntax::Pi(pi2) = &*rhs {
            println!("pi injectivity solver");
            // Domains are equal.
            let mdom =
                state.equality_constraint(pi1.source.clone(), pi2.source.clone(), cons.ty.clone());
            let mdomTy = state.metavariable(mdom);

            // TODO: here in the paper, they rewrite the second pi's codomain
            // to use the binder of the first pi.  I don't think that we have to
            // do this here - but it is unclear to me.
            //let pi2_cod = subst(pi2.target, Index::new(0), );

            // TODO: why do we do this?  We constrain equality under an extended
            // context to create the metavariable with the correct context?
            state.extend_context_nameless(mdomTy.clone());
            let mcod =
                state.equality_constraint(pi1.target.clone(), pi2.target.clone(), cons.ty.clone());
            state.pop_context();
            let mcodTy = state.metavariable(mcod);

            // Solve the antiunifier for the original constraint.
            state.solve_metavariable_id(cons.meta, Syntax::pi_rc(mdomTy, mcodTy));
            return Ok(());
        }
    }

    // Left Meta Solver - solve an equality constriant where the left side is an unsolved meta.
    // if let Syntax::Metavariable(meta) = &*cons.lhs {
    //     println!("left meta solver: {:?}", meta);
    // }
    Err(anyhow!("not implemented"))
}

pub fn solve_constraint(state: &mut State, cons: Constraint) -> Result<()> {
    match cons.data {
        ConstraintData::EmptyConstraint => Ok(()),
        ConstraintData::EqualityConstraint(cons) => solve_equality(state, cons),
    }
}

pub fn solve_all(state: &mut State) -> Result<()> {
    while let Some(constraint) = state.constraints.pop() {
        solve_constraint(state, constraint)?;
    }
    Ok(())
}
