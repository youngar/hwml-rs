//! Unification for HWML type codes and values
//!
//! This module implements bidirectional pattern unification following the
//! algorithm described in Abel & Pientka (2011).
//!
//! ## Structure
//!
//! The unification algorithm is organized into several categories:
//!
//! - **Entry points**: `unify`, `unify_at`, `unify_type_codes`
//! - **Main dispatch**: `unify_structural` - dispatches to specific cases
//! - **Neutral cases**: `unify_flex_any`, `unify_rigids`, `unify_same_meta_flex`
//! - **Structural cases**: `unify_universe_codes`, `unify_pi_codes`, `unify_lift_codes`
//! - **Spine unification**: `unify_spines`
//! - **Pattern unification**: See `pattern` submodule
//!
//! ## Unification Results
//!
//! - `Solved`: Values are definitionally equal
//! - `Stuck`: Cannot proceed without solving metavariables (solver will block)
//! - `Error`: Hard failure - values are incompatible

pub mod pattern;

use hwml_core::common::Icit;
use std::rc::Rc;

use hwml_core::{
    eval,
    ty::{RcTy, Ty},
    val::{Eliminator, Flex, GlobalEnv, LocalEnv, MetaVariable, Normal, Spine},
    Binding, Index, Level, MetaVariableId, Name, RcSyntax, RcValue, Syntax, Value,
};

use crate::{
    error::ElabError,
    meta::{MetaId, MetaKind},
    state::SolverState,
};

#[derive(Debug)]
pub enum UnifyResult {
    Solved,
    Stuck,
}

pub struct Unifier<'a, 'db> {
    pub global: &'a GlobalEnv<'db>,
    pub state: &'a mut SolverState<'db>,
    pub db: &'db dyn salsa::Database,
    pub depth: usize,
}

impl<'a, 'db> Unifier<'a, 'db> {
    pub fn new(
        db: &'db dyn salsa::Database,
        global: &'a GlobalEnv<'db>,
        state: &'a mut SolverState<'db>,
        depth: usize,
    ) -> Self {
        Unifier {
            global,
            state,
            db,
            depth,
        }
    }

    /// Force a value by substituting solved metas.
    fn force(&self, val: RcValue<'db>) -> RcValue<'db> {
        if let Value::Flex(flex) = val.as_ref() {
            if let Some(forced) = self.state.force_flex(self.global, flex) {
                return self.force(forced);
            }
        }
        val
    }

    /// Apply a value to a single argument (for eta expansion).
    fn apply_val(
        &self,
        fun: RcValue<'db>,
        arg: RcValue<'db>,
        arg_ty: RcValue<'db>,
    ) -> RcValue<'db> {
        // **PHASE 9**: Decode arg_ty to get semantic type for Normal
        let arg_ty_semantic = hwml_core::eval::decode_type_code(self.global, &arg_ty)
            .unwrap_or_else(|_| Rc::new(Ty::universe(0)));
        let elim = Eliminator::application(Normal::new(arg_ty_semantic, arg), Icit::Explicit);
        let mut spine = Spine::empty();
        spine.push(elim);
        eval::run_spine(self.global, fun, &spine)
            .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0)))
    }

    /// Typed, eta-aware unification (homogeneous - both sides have same type).
    pub fn unify(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        self.unify_at(lhs, rhs, ty)
    }

    /// Homogeneous typed unification with eta.
    pub fn unify_at(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        let lhs = self.force(lhs);
        let rhs = self.force(rhs);

        if Rc::ptr_eq(&lhs, &rhs) {
            return Ok(UnifyResult::Solved);
        }

        // **PHASE 9**: Pi eta-expansion - handle decoded Ty::Pi directly
        if let Ty::Pi(dom_ty, _icit, ty_closure) = ty.as_ref() {
            // Encode domain type back to a value for the rigid variable
            let dom_code = hwml_core::quote::encode_type(
                self.global.db(),
                self.global,
                self.depth,
                dom_ty.as_ref(),
            )
            .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0)));

            // Decode domain type for variable creation
            let var: RcValue<'db> =
                Rc::new(Value::variable(Level::new(self.depth), dom_ty.clone()));

            // Apply both sides to the fresh variable
            let lhs_app = self.apply_val(lhs, var.clone(), dom_code.clone());
            let rhs_app = self.apply_val(rhs, var.clone(), dom_code.clone());

            // Compute return type by applying the type closure
            let ret_ty = hwml_core::val::run_ty_closure(self.global, ty_closure, [var.clone()])
                .unwrap_or_else(|_| Rc::new(Ty::universe(0)));

            self.depth += 1;
            let result = self.unify_at(lhs_app, rhs_app, ret_ty);
            self.depth -= 1;
            return result;
        }

        if matches!(ty.as_ref(), Ty::UniverseType) {
            return self.unify_type_codes(lhs, rhs);
        }

        self.unify_structural(lhs, rhs)
    }

    /// Structural unification (after forcing, no eta).
    fn unify_structural(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // Flex-flex same meta with empty spines: intersection (Abel-Pientka §3.5).
        if let (Value::Flex(lf), Value::Flex(rf)) = (lhs.as_ref(), rhs.as_ref()) {
            if lf.head.id == rf.head.id && lf.spine.is_empty() && rf.spine.is_empty() {
                return self.unify_same_meta_flex(&lf, &rf, &lhs, &rhs);
            }
        }

        // Left Flex: try pattern unification.
        if let Value::Flex(flex) = lhs.as_ref() {
            return self.unify_flex_any(flex, &rhs);
        }

        // Right Flex: try pattern unification (symmetric).
        if let Value::Flex(flex) = rhs.as_ref() {
            return self.unify_flex_any(flex, &lhs);
        }

        // Both Rigid: unify variable heads and spines.
        if let (Value::Rigid(lr), Value::Rigid(rr)) = (lhs.as_ref(), rhs.as_ref()) {
            return self.unify_rigids(lr, rr, &lhs, &rhs);
        }

        // Both StuckApplication: unify constant heads and spines.
        if let (Value::StuckApplication(sa1), Value::StuckApplication(sa2)) =
            (lhs.as_ref(), rhs.as_ref())
        {
            return self.unify_stuck_applications(sa1, sa2, &lhs, &rhs);
        }

        // Structural cases for specific value forms
        match (lhs.as_ref(), rhs.as_ref()) {
            (Value::UniverseCode(n), Value::UniverseCode(m)) => {
                self.unify_universe_codes(*n, *m, &lhs, &rhs)
            }
            (Value::BitCode, Value::BitCode) => Ok(UnifyResult::Solved),
            (Value::PiCode(d1, _icit1, c1), Value::PiCode(d2, _icit2, c2)) => {
                self.unify_pi_codes(d1.clone(), c1.clone(), d2.clone(), c2.clone())
            }
            (Value::LiftCode(n, i1), Value::LiftCode(m, i2)) => {
                self.unify_lift_codes(*n, i1.clone(), *m, i2.clone(), &lhs, &rhs)
            }

            // Name-based structural equality
            (Value::Prim(p1), Value::Prim(p2)) => self.unify_prims(p1, p2, &lhs, &rhs),
            (Value::Constant(c1), Value::Constant(c2)) => self.unify_constants(c1, c2, &lhs, &rhs),

            // Unit types (always equal)
            (Value::Zero(_), Value::Zero(_)) => Ok(UnifyResult::Solved),
            (Value::One(_), Value::One(_)) => Ok(UnifyResult::Solved),
            (Value::Bit(_), Value::Bit(_)) => Ok(UnifyResult::Solved),
            (Value::Refl(_), Value::Refl(_)) => Ok(UnifyResult::Solved),
            (Value::HardwareUniverse(_), Value::HardwareUniverse(_)) => Ok(UnifyResult::Solved),
            (Value::SignalUniverse(_), Value::SignalUniverse(_)) => Ok(UnifyResult::Solved),
            (Value::ModuleUniverse(_), Value::ModuleUniverse(_)) => Ok(UnifyResult::Solved),

            // Hardware lift types (structural injectivity on inner type)
            (Value::SLift(s1), Value::SLift(s2)) => {
                // Both are signal lifts, unify their inner types
                // Note: This is structural unification at universe level
                self.unify_type_codes(s1.ty.clone(), s2.ty.clone())
            }
            (Value::MLift(m1), Value::MLift(m2)) => {
                // Both are module lifts, unify their inner types
                self.unify_type_codes(m1.ty.clone(), m2.ty.clone())
            }

            // Hardware arrow types (injectivity on source and target)
            (Value::HArrow(ha1), Value::HArrow(ha2)) => self.unify_harrows(ha1, ha2),

            // Hardware applications (structural equality)
            (Value::HApplication(happ1), Value::HApplication(happ2)) => {
                self.unify_happlications(happ1, happ2)
            }

            // Hard failures for definitely incompatible forms
            // These are cases where no amount of meta-solving will make them equal
            (Value::UniverseCode(_), Value::TypeConstructor(_))
            | (Value::TypeConstructor(_), Value::UniverseCode(_))
            | (Value::UniverseCode(_), Value::DataConstructor(_))
            | (Value::DataConstructor(_), Value::UniverseCode(_))
            | (Value::TypeConstructor(_), Value::DataConstructor(_))
            | (Value::DataConstructor(_), Value::TypeConstructor(_)) => {
                self.unify_incompatible(&lhs, &rhs)
            }

            // Default: return Stuck and let the solver handle it
            // This includes DataConstructor vs DataConstructor (handled by solver's constructor injectivity)
            // and TypeConstructor vs TypeConstructor (also handled by solver)
            _ => Ok(UnifyResult::Stuck),
        }
    }

    // ─── Neutral Unification Cases ────────────────────────────────────────────

    /// Unify a flex (metavariable) with any value using pattern unification.
    fn unify_flex_any(
        &mut self,
        flex: &Flex<'db>,
        other: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        let flex = flex.clone();
        let dummy: RcTy<'db> = Rc::new(Ty::UniverseType);
        if pattern::pattern_unify(
            self.db,
            self.global,
            self.state,
            &flex,
            other.clone(),
            dummy,
        )? {
            return Ok(UnifyResult::Solved);
        }
        Ok(UnifyResult::Stuck)
    }

    /// Unify two rigid neutrals with the same variable head.
    /// Rigid(x, sp1) = Rigid(x, sp2) requires sp1 = sp2 (unify spines).
    fn unify_rigids(
        &mut self,
        lr: &hwml_core::val::Rigid<'db>,
        rr: &hwml_core::val::Rigid<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if lr.head.level != rr.head.level {
            return Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            });
        }
        let sp1 = lr.spine.clone();
        let sp2 = rr.spine.clone();
        self.unify_spines(&sp1, &sp2)
    }

    /// Unify two stuck applications with the same constant head.
    /// StuckApplication(c, sp1) = StuckApplication(c, sp2) requires c1 == c2 && sp1 = sp2.
    /// This handles applications of opaque constants during mutual recursion.
    fn unify_stuck_applications(
        &mut self,
        sa1: &hwml_core::val::StuckApplication<'db>,
        sa2: &hwml_core::val::StuckApplication<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // Check that both have the same constant head
        if sa1.head.name != sa2.head.name {
            return Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            });
        }
        // Unify spines
        let sp1 = sa1.spine.clone();
        let sp2 = sa2.spine.clone();
        self.unify_spines(&sp1, &sp2)
    }

    /// Unify the same metavariable with different local environments.
    /// ?m[ρ] = ?m[ξ] (both have empty spines).
    /// Uses Abel-Pientka intersection algorithm (§3.5).
    fn unify_same_meta_flex(
        &mut self,
        lf: &Flex<'db>,
        rf: &Flex<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        self.unify_same_meta(lf, rf, lhs, rhs)
    }

    // ─── Structural Unification Cases ─────────────────────────────────────────

    /// Unify two universe codes.
    /// UniverseCode(n) = UniverseCode(m) succeeds iff n == m.
    fn unify_universe_codes(
        &mut self,
        n: usize,
        m: usize,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if n == m {
            Ok(UnifyResult::Solved)
        } else {
            Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            })
        }
    }

    /// Unify two Pi type codes.
    /// PiCode(d1, c1) = PiCode(d2, c2) requires:
    /// 1. d1 = d2 (domain types unify)
    /// 2. c1(x) = c2(x) for fresh variable x (codomain closures unify)
    fn unify_pi_codes(
        &mut self,
        d1: RcValue<'db>,
        c1: hwml_core::val::Closure<'db>,
        d2: RcValue<'db>,
        c2: hwml_core::val::Closure<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // First unify the domains
        match self.unify_type_codes(d1.clone(), d2)? {
            UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
            UnifyResult::Solved => {}
        }

        // Create a fresh variable and unify the codomains
        // Decode d1 (type code) to semantic type for variable
        let d1_ty = hwml_core::eval::decode_type_code(self.global, &d1)
            .unwrap_or_else(|_| Rc::new(Ty::Universe(0)));
        let var: RcValue<'db> = Rc::new(Value::variable(Level::new(self.depth), d1_ty));
        let ret1 = c1.apply(self.global, &var);
        let ret2 = c2.apply(self.global, &var);

        self.depth += 1;
        let result = self.unify_type_codes(ret1, ret2);
        self.depth -= 1;

        result
    }

    /// Unify two LiftCode values.
    /// LiftCode(n, i1) = LiftCode(m, i2) requires:
    /// 1. n == m (lift levels must match)
    /// 2. i1 = i2 (inner types unify)
    fn unify_lift_codes(
        &mut self,
        n: usize,
        i1: RcValue<'db>,
        m: usize,
        i2: RcValue<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if n != m {
            return Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            });
        }
        self.unify_type_codes(i1, i2)
    }

    /// Unify two primitives by checking name equality.
    /// Prim(name1) = Prim(name2) succeeds iff name1 == name2.
    fn unify_prims(
        &mut self,
        p1: &hwml_core::val::Prim<'db>,
        p2: &hwml_core::val::Prim<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if p1.name == p2.name {
            Ok(UnifyResult::Solved)
        } else {
            Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            })
        }
    }

    /// Unify two constants by checking name equality.
    /// Constant(name1) = Constant(name2) succeeds iff name1 == name2.
    fn unify_constants(
        &mut self,
        c1: &hwml_core::val::Constant<'db>,
        c2: &hwml_core::val::Constant<'db>,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if c1.name == c2.name {
            Ok(UnifyResult::Solved)
        } else {
            Err(ElabError::UnificationFailure {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                span: None,
                elab_backtrace: Vec::new(),
            })
        }
    }

    /// Unify two hardware arrow types.
    /// HArrow(src1, tgt1) = HArrow(src2, tgt2) requires:
    /// 1. src1 = src2 (source types unify)
    /// 2. tgt1(x) = tgt2(x) for fresh variable x (target closures unify)
    fn unify_harrows(
        &mut self,
        ha1: &hwml_core::val::HArrow<'db>,
        ha2: &hwml_core::val::HArrow<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // First unify the source types
        match self.unify_type_codes(ha1.source.clone(), ha2.source.clone())? {
            UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
            UnifyResult::Solved => {}
        }

        // Create a fresh variable and unify the target closures
        // Decode source type code to semantic type for variable
        let source_ty = hwml_core::eval::decode_type_code(self.global, &ha1.source)
            .unwrap_or_else(|_| Rc::new(Ty::Universe(0)));
        let var: RcValue<'db> = Rc::new(Value::variable(Level::new(self.depth), source_ty));
        let tgt1 = ha1.target.apply(self.global, &var);
        let tgt2 = ha2.target.apply(self.global, &var);

        self.depth += 1;
        let result = self.unify_type_codes(tgt1, tgt2);
        self.depth -= 1;

        result
    }

    /// Unify two hardware applications.
    /// HApplication requires unifying the module, module type, and argument.
    fn unify_happlications(
        &mut self,
        happ1: &hwml_core::val::HApplication<'db>,
        happ2: &hwml_core::val::HApplication<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // Unify the module values
        match self.unify_structural(happ1.module.clone(), happ2.module.clone())? {
            UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
            UnifyResult::Solved => {}
        }

        // Unify the module types
        match self.unify_type_codes(happ1.module_ty.clone(), happ2.module_ty.clone())? {
            UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
            UnifyResult::Solved => {}
        }

        // Unify the arguments
        self.unify_structural(happ1.argument.clone(), happ2.argument.clone())
    }

    /// Handle definitively incompatible value forms.
    /// These are hard failures where no amount of meta-solving will help.
    fn unify_incompatible(
        &mut self,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        Err(ElabError::UnificationFailure {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            span: None,
            elab_backtrace: Vec::new(),
        })
    }

    /// Same-meta intersection (Abel-Pientka §3.5).
    ///
    /// `?m[ρ] = ?m[ξ]` (both have empty spines).
    /// Compute the intersection of ρ and ξ: kept positions where both agree.
    /// Create fresh ?m' with arity = |kept| and solve ?m ← λ(old_arity). ?m'[kept_args].
    fn unify_same_meta(
        &mut self,
        lf: &Flex<'db>,
        rf: &Flex<'db>,
        _lhs: &RcValue<'db>,
        _rhs: &RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        let old_arity = lf.head.local.depth();
        let kept = compute_intersection(&lf.head.local, &rf.head.local, old_arity);

        // All positions agree: trivially solved (no need to constrain ?m further).
        if kept.len() == old_arity {
            return Ok(UnifyResult::Solved);
        }

        let old_meta_id = MetaId(lf.head.id.local_index as u32);

        // Already solved: treat as solved (unifier should have forced this).
        if self.state.meta_solution(old_meta_id).is_some() {
            return Ok(UnifyResult::Solved);
        }

        let dummy_ty = Rc::new(hwml_core::ty::Ty::UniverseType);
        let new_meta_id = self.state.fresh_meta(dummy_ty, kept.len(), MetaKind::Term);

        let syn = intersection_syntax_solution(self.db, new_meta_id, old_arity, &kept);
        let val = intersection_value_solution(new_meta_id, &kept);

        self.state.solve_meta(old_meta_id, syn, val)?;
        Ok(UnifyResult::Solved)
    }

    /// Unify two spines (sequences of eliminators).
    /// Both spines must have the same length and matching eliminators.
    fn unify_spines(
        &mut self,
        sp1: &Spine<'db>,
        sp2: &Spine<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        if sp1.len() != sp2.len() {
            return Ok(UnifyResult::Stuck);
        }
        for (e1, e2) in sp1.iter().zip(sp2.iter()) {
            match (e1, e2) {
                (Eliminator::Application(a1), Eliminator::Application(a2)) => {
                    let v1 = a1.argument.value.clone();
                    let v2 = a2.argument.value.clone();
                    match self.unify_structural(v1, v2)? {
                        UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
                        UnifyResult::Solved => {}
                    }
                }
                (Eliminator::Case(c1), Eliminator::Case(c2)) => {
                    match self.unify_case_eliminators(c1, c2)? {
                        UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
                        UnifyResult::Solved => {}
                    }
                }
                _ => {
                    // Mismatched eliminator kinds (Application vs Case)
                    return Ok(UnifyResult::Stuck);
                }
            }
        }
        Ok(UnifyResult::Solved)
    }

    /// Unify two Case eliminators.
    /// Case(tc1, params1, branches1) = Case(tc2, params2, branches2) requires:
    /// 1. tc1 == tc2 (same type constructor)
    /// 2. params1[i] = params2[i] for all i (parameters unify)
    /// 3. branches1[i].constructor == branches2[i].constructor for all i
    /// 4. branches1[i].body(xs) = branches2[i].body(xs) for fresh variables xs
    fn unify_case_eliminators(
        &mut self,
        case1: &hwml_core::val::Case<'db>,
        case2: &hwml_core::val::Case<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        // 1. Check type constructors match
        if case1.type_constructor != case2.type_constructor {
            // Type constructor mismatch is a hard failure
            return Ok(UnifyResult::Stuck);
        }

        // 2. Check parameter count matches
        if case1.parameters.len() != case2.parameters.len() {
            return Ok(UnifyResult::Stuck);
        }

        // 3. Unify parameters pairwise (structural unification)
        for (p1, p2) in case1.parameters.iter().zip(case2.parameters.iter()) {
            match self.unify_type_codes(p1.clone(), p2.clone())? {
                UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
                UnifyResult::Solved => {}
            }
        }

        // 4. Check branch count and constructors match
        if case1.branches.len() != case2.branches.len() {
            return Ok(UnifyResult::Stuck);
        }

        for (b1, b2) in case1.branches.iter().zip(case2.branches.iter()) {
            // Check constructor names match
            if b1.constructor != b2.constructor {
                // Constructor mismatch is a hard failure
                return Ok(UnifyResult::Stuck);
            }

            // Check arities match
            if b1.arity != b2.arity {
                return Ok(UnifyResult::Stuck);
            }

            // Create fresh variables for the constructor arguments
            let args: Vec<RcValue<'db>> = (0..b1.arity)
                .map(|i| {
                    // Use Universe(0) as semantic type
                    let var: RcValue<'db> = Rc::new(Value::variable(
                        Level::new(self.depth + i),
                        Rc::new(Ty::Universe(0)), // Use Universe(0) as approximation
                    ));
                    var
                })
                .collect();

            // Apply closures to fresh variables using run_closure
            let body1 = eval::run_closure(self.global, &b1.body, args.clone()).map_err(|_| {
                ElabError::UnificationFailure {
                    lhs: Rc::new(Value::UniverseCode(0)),
                    rhs: Rc::new(Value::UniverseCode(0)),
                    span: None,
                    elab_backtrace: Vec::new(),
                }
            })?;
            let body2 = eval::run_closure(self.global, &b2.body, args).map_err(|_| {
                ElabError::UnificationFailure {
                    lhs: Rc::new(Value::UniverseCode(0)),
                    rhs: Rc::new(Value::UniverseCode(0)),
                    span: None,
                    elab_backtrace: Vec::new(),
                }
            })?;

            // Increase depth for the fresh variables
            self.depth += b1.arity;

            // Unify the branch bodies
            let result = self.unify_structural(body1, body2)?;

            // Restore depth
            self.depth -= b1.arity;

            match result {
                UnifyResult::Stuck => return Ok(UnifyResult::Stuck),
                UnifyResult::Solved => {}
            }
        }

        Ok(UnifyResult::Solved)
    }

    /// Structural unification of type codes (no Pi eta).
    pub fn unify_type_codes(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        let lhs = self.force(lhs);
        let rhs = self.force(rhs);
        if Rc::ptr_eq(&lhs, &rhs) {
            return Ok(UnifyResult::Solved);
        }
        self.unify_structural(lhs, rhs)
    }
}

// ─── Intersection helpers ──────────────────────────────────────────────────────

/// Compute positions where ρ[i] and ξ[i] are the same rigid variable.
fn compute_intersection<'db>(lhs: &LocalEnv<'db>, rhs: &LocalEnv<'db>, arity: usize) -> Vec<usize> {
    let mut kept = Vec::new();
    for i in 0..arity {
        let lv = lhs.get(Level::new(i));
        let rv = rhs.get(Level::new(i));
        if Rc::ptr_eq(lv, rv) {
            kept.push(i);
            continue;
        }
        if let (Value::Rigid(lr), Value::Rigid(rr)) = (lv.as_ref(), rv.as_ref()) {
            if lr.head.level == rr.head.level && lr.spine.is_empty() && rr.spine.is_empty() {
                kept.push(i);
            }
        }
    }
    kept
}

/// Build the syntax solution for `?m`:
/// `λ(old_arity). Metavariable(m', [Index(old_arity-1-kept[0]), ..., Index(old_arity-1-kept[j])])`
pub(crate) fn intersection_syntax_solution<'db>(
    db: &'db dyn salsa::Database,
    new_meta_id: MetaId,
    old_arity: usize,
    kept: &[usize],
) -> RcSyntax<'db> {
    let meta_vid = MetaVariableId::new(new_meta_id.0 as u16);
    let subst: Vec<RcSyntax<'db>> = kept
        .iter()
        .map(|&pos| Syntax::variable_rc(Index(old_arity - 1 - pos)))
        .collect();
    let mut body: RcSyntax<'db> = Syntax::metavariable_rc(meta_vid, subst);
    for _ in 0..old_arity {
        body = Syntax::lambda_rc(Icit::Explicit, Binding::new(Name::anonymous(db), body));
    }
    body
}

/// Build the value solution for `?m`:
/// `Flex(m', LocalEnv([Rigid(Level(kept[0])), ..., Rigid(Level(kept[j]))]), [], dummy_ty)`
///
/// `subst_value(this, actual_ρ)` = `Flex(m', [actual_ρ[kept[0]], ..., actual_ρ[kept[j]]], [])`.
pub(crate) fn intersection_value_solution<'db>(
    new_meta_id: MetaId,
    kept: &[usize],
) -> RcValue<'db> {
    let dummy_ty: RcTy<'db> = Rc::new(Ty::Universe(0));
    let mut inner_local = LocalEnv::new();
    for &pos in kept {
        inner_local.push(Rc::new(Value::variable(Level::new(pos), dummy_ty.clone())));
    }
    let meta_vid = MetaVariableId::new(new_meta_id.0 as u16);
    Rc::new(Value::Flex(Flex::new(
        MetaVariable::new(meta_vid, inner_local),
        Spine::empty(),
        dummy_ty,
    )))
}
