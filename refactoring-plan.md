  Clean Refactoring Plan: Fix Ty vs Value Architecture (No Hacks)

  Phase 1: Audit and Preparation

  Task 1.1: Comprehensive code audit
    • [ ] Identify all type_synth* functions and their return types
    • [ ] Identify all type_check* functions and their parameter types
    • [ ] List all TCEnvironment method signatures
    • [ ] Document all places that read/write env.types
    • [ ] Create spreadsheet of all functions that need signature changes

  Task 1.2: Create architectural validation tests
    • [ ] Write tests that will verify correct Ty vs Value separation
    • [ ] Write tests for checking against native types (UniverseType, etc.)
    • [ ] Write tests for Pi type checking with TyClosure
    • [ ] These tests will FAIL initially and guide the refactor

  Phase 2: Core Type Infrastructure

  Task 2.1: Update TCEnvironment structure
  pub struct TCEnvironment<'db, 'g> {
      pub db: &'db dyn Database,
      pub values: val::Environment<'db, 'g>,  // For evaluation
      pub types: Vec<RcTy<'db>>,              // For type checking
  }
    • [ ] Change types: Vec<RcValue<'db>> to types: Vec<RcTy<'db>>
    • [ ] Update type_of() to return &RcTy<'db>
    • [ ] Update var_type() to return &RcTy<'db>
    • [ ] Update push_var() to take RcTy<'db>
    • [ ] Update all other methods (pop, context, depth stay same)

  Task 2.2: Update type_synth signature
  pub fn type_synth<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      term: &Syntax<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>  // Returns Ty, not Value
    • [ ] Change return type from Result<RcValue, Error> to Result<RcTy, Error>
    • [ ] Leave implementation empty for now (will fill in Phase 4)
    • [ ] Let compiler errors accumulate

  Task 2.3: Update type_check signature
  pub fn type_check<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      term: &Syntax<'db>,
      expected_ty: &val::Ty<'db>,  // Takes Ty, not Value
  ) -> Result<(), Error<'db>>
    • [ ] Change parameter from ty: &Value to expected_ty: &Ty
    • [ ] Leave implementation empty for now
    • [ ] Let compiler errors accumulate

  Task 2.4: Update type equality/subsumption signatures
  pub fn is_subtype<'db>(
      global: &val::GlobalEnv<'db>,
      transparent: &val::TransparentEnv<'db>,
      depth: usize,
      sub_ty: &val::Ty<'db>,    // Ty, not Value
      super_ty: &val::Ty<'db>,  // Ty, not Value
  ) -> bool
    • [ ] Change both parameters to &Ty
    • [ ] Leave implementation for later

  Phase 3: Implement Type Equality First (Foundation)

  Task 3.1: Implement structural equality for Ty
  pub fn types_equal<'db>(
      global: &val::GlobalEnv<'db>,
      transparent: &val::TransparentEnv<'db>,
      depth: usize,
      ty1: &val::Ty<'db>,
      ty2: &val::Ty<'db>,
  ) -> bool
    • [ ] UniverseType == UniverseType → true
    • [ ] SignalUniverseType == SignalUniverseType → true
    • [ ] ModuleUniverseType == ModuleUniverseType → true
    • [ ] Pi(s1, t1) == Pi(s2, t2) → recursively check source and target
    • [ ] HArrow(s1, t1) == HArrow(s2, t2) → recursively check both sides
    • [ ] El(c1) == El(c2) → use equal(c1, c2) for value equality
    • [ ] SignalEl(c1) == SignalEl(c2) → use equal(c1, c2)
    • [ ] ModuleEl(c1) == ModuleEl(c2) → use equal(c1, c2)
    • [ ] Different constructors → false

  Task 3.2: Implement TyClosure comparison
    • [ ] Extract body from TyClosure
    • [ ] Create fresh variable
    • [ ] Apply closure to variable
    • [ ] Recursively compare resulting types

  Task 3.3: Implement is_subtype for Ty
    • [ ] Reflexivity: ty <: ty → true
    • [ ] Universe cumulativity: El(UniverseCode(n)) <: El(UniverseCode(m)) if n ≤ m
    • [ ] Pi contravariance/covariance: Pi(s1, t1) <: Pi(s2, t2) if s2 <: s1 and t1 <: t2
    • [ ] Otherwise delegate to equality

  Phase 4: Implement type_synth (Bottom-Up)

  Task 4.1: Implement type_synth_variable
  pub fn type_synth_variable<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      variable: &syn::Variable<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>
    • [ ] Get type from env.var_type(variable) (now returns &RcTy)
    • [ ] Return cloned RcTy

  Task 4.2: Implement type_synth_constant
  pub fn type_synth_constant<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      constant: &syn::Constant<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>
    • [ ] Lookup constant in global env
    • [ ] Evaluate its type: eval(env, &constant_info.ty) → RcValue
    • [ ] Wrap in Ty::El: Ok(val::Ty::el_rc(type_code))

  Task 4.3: Implement type_synth_prim
    • [ ] Lookup primitive in global env
    • [ ] Evaluate its type to get type code
    • [ ] Wrap in Ty::El

  Task 4.4: Implement type_synth_check (clean version)
  pub fn type_synth_check<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      check: &syn::Check<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>
    • [ ] Validate type annotation: check_ty(env, &check.ty)?
    • [ ] Evaluate to semantic type: let expected_ty = eval_ty(&mut env.values, &check.ty)?
    • [ ] Check term: type_check(env, &check.term, &expected_ty)?
    • [ ] Return semantic type: Ok(expected_ty)

  Task 4.5: Implement type_synth for UniverseCode
  Syntax::UniverseCode(level) => {
      Ok(val::Ty::el_rc(Value::UniverseCode(level + 1).into()))
  }
    • [ ] UniverseCode(n) has type El(UniverseCode(n+1))
    • [ ] This is the Tarski tower in action

  Task 4.6: Implement type_synth for PiCode
    • [ ] Synthesize type of source → source_ty
    • [ ] Check source_ty is El(UniverseCode(i)) for some i
    • [ ] Push variable, synthesize type of target → target_ty
    • [ ] Check target_ty is El(UniverseCode(j)) for some j
    • [ ] Pop variable
    • [ ] Return Ty::el_rc(Value::UniverseCode(max(i, j)).into())

  Task 4.7: Implement type_synth for BitCode
    • [ ] Return Ty::el_rc(Value::UniverseCode(0).into())

  Task 4.8: Implement type_synth_application
  pub fn type_synth_application<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      app: &syn::Application<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>
    • [ ] Synthesize function type: let fun_ty = type_synth(env, &app.function)?
    • [ ] Match on fun_ty:
       • Ty::Pi(source, target) → check arg against source, apply TyClosure
       • Ty::El(code) where code is Value::PiCode → extract and handle
       • Otherwise → error
    • [ ] Apply TyClosure: run_ty_closure(global, target, arg_val)?
    • [ ] Return resulting type

  Task 4.9: Implement run_ty_closure helper
  pub fn run_ty_closure<'db>(
      global: &val::GlobalEnv<'db>,
      closure: &val::TyClosure<'db>,
      arg: RcValue<'db>,
  ) -> Result<RcTy<'db>, Error<'db>>
    • [ ] Extend closure environment with arg
    • [ ] Return closure body (already a type)

  Task 4.10: Implement type_synth_case
    • [ ] Synthesize scrutinee type
    • [ ] Extract data constructor info
    • [ ] Check all branches
    • [ ] Return motive type applied to scrutinee

  Task 4.11: Implement type_synth_let
    • [ ] Check value against its type annotation
    • [ ] Evaluate type and value
    • [ ] Push transparent binding with RcTy
    • [ ] Synthesize body type
    • [ ] Pop
    • [ ] Return body type

  Task 4.12: Implement type_synth_metavariable
    • [ ] Lookup metavariable info
    • [ ] Build local environment
    • [ ] Evaluate metavariable type to get RcValue
    • [ ] Wrap in Ty::el_rc

  Task 4.13: Implement type_synth_eq
    • [ ] Synthesize type of the type field → should be Ty::El(UniverseCode(n))
    • [ ] Check lhs and rhs against the type
    • [ ] Return same universe level

  Task 4.14: Implement type_synth_transport
    • [ ] Check structure
    • [ ] Return motive applied to rhs

  Task 4.15: Complete type_synth dispatcher
    • [ ] Wire all cases together
    • [ ] Handle all Syntax variants
    • [ ] Return BadSynth for non-synthesizable forms

  Phase 5: Implement type_check (Top-Down)

  Task 5.1: Implement type_check dispatcher
  pub fn type_check<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      term: &Syntax<'db>,
      expected_ty: &val::Ty<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] Match on term and expected_ty
    • [ ] Lambda → must be Pi or El(PiCode)
    • [ ] DataConstructor → check against its type
    • [ ] TypeConstructor → check against its type
    • [ ] Case → check against motive result
    • [ ] Otherwise → synthesize and check subtyping

  Task 5.2: Implement type_check_lambda
  fn type_check_lambda<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      lam: &syn::Lambda<'db>,
      expected_ty: &val::Ty<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] Match expected_ty:
       • Ty::Pi(source, target) → push var with source, check body against target.body, pop
       • Ty::El(Value::PiCode(...)) → extract code parts, push, check, pop
       • Otherwise → error

  Task 5.3: Implement type_check_data_constructor
    • [ ] Lookup data constructor type
    • [ ] Must be Ty::El(code) where code is a type constructor
    • [ ] Check each argument
    • [ ] Build saturated application
    • [ ] Check against expected

  Task 5.4: Implement type_check_type_constructor
    • [ ] Similar to data constructor
    • [ ] Check all arguments

  Task 5.5: Implement type_check_case
    • [ ] Check scrutinee
    • [ ] Check motive
    • [ ] Check all branches
    • [ ] Ensure result matches expected

  Task 5.6: Implement type_check_let
    • [ ] Check value against annotation
    • [ ] Push transparent binding
    • [ ] Check body
    • [ ] Pop

  Task 5.7: Implement type_check_refl
    • [ ] Expected type must be Ty::El(Value::EqType(...))
    • [ ] Check lhs == rhs

  Task 5.8: Implement type_check_module
    • [ ] Expected type must be hardware module type
    • [ ] Check body

  Task 5.9: Implement type_check_synth_term (subsumption)
  pub fn type_check_synth_term<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      term: &Syntax<'db>,
      expected_ty: &val::Ty<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] Synthesize: let synth_ty = type_synth(env, term)?
    • [ ] Check subtyping: is_subtype(global, transparent, depth, &synth_ty, expected_ty)
    • [ ] If true → Ok, else → error

  Phase 6: Fix check_ty Properly

  Task 6.1: Reimplement check_ty with correct Tarski bridge
  pub fn check_ty<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      ty: &syn::Ty<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] UniverseType | SignalUniverseType | ModuleUniverseType → Ok(())
    • [ ] Pi(source, target) → check source, push, check target, pop
    • [ ] HArrow(source, target) → check both
    • [ ] El(code) → `type_check(env, code, &Ty::UniverseType)?`
    • [ ] SignalEl(code) → `type_check(env, code, &Ty::SignalUniverseType)?`
    • [ ] ModuleEl(code) → `type_check(env, code, &Ty::ModuleUniverseType)?`

  Task 6.2: Remove all Russell-style hacks
    • [ ] Delete the pattern matching on Value::UniverseCode
    • [ ] Delete ty_to_code_temporary_hack
    • [ ] Search for "ARCHITECTURAL" comments and remove them

  Phase 7: Update Helper Functions

  Task 7.1: Update check_type function
  pub fn check_type<'db, 'g>(
      env: &mut TCEnvironment<'db, 'g>,
      term: &Syntax<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] Synthesize: let ty = type_synth(env, term)?
    • [ ] Check it's a valid type (universe or hardware type)
    • [ ] Match on ty:
       • Ty::El(Value::UniverseCode(_)) → Ok
       • Ty::El(Value::HardwareUniverse(_)) → Ok
       • Otherwise → error

  Task 7.2: Update check_meta_type
    • [ ] Similar to check_type but only universe types

  Task 7.3: Update check_signal_type
    • [ ] Check synthesized type is signal type

  Task 7.4: Update check_module_type
    • [ ] Check synthesized type is module type

  Phase 8: Update Pattern Unification

  Task 8.1: Update unify function signature
  pub fn unify<'db>(
      global: &mut val::GlobalEnv<'db>,
      transparent: &val::TransparentEnv<'db>,
      depth: usize,
      ty: &val::Ty<'db>,  // Ty, not Value
      lhs: &Value<'db>,
      rhs: &Value<'db>,
  ) -> Result<(), Error<'db>>
    • [ ] Change ty parameter to &Ty
    • [ ] Update all recursive calls

  Task 8.2: Update pattern_unify_spine
    • [ ] Pass types correctly
    • [ ] Handle El extraction when needed

  Task 8.3: Update invert function
    • [ ] Use Ty throughout
  Phase 9: Update Elaborator (hwml-elab)

  Task 9.1: Update elab/expr.rs check function
  pub fn check<'a, 'db, Db>(
      db: &'db Db,
      elab: &mut Elaborator<'a, 'db>,
      expr: &Expression,
      expected_ty: RcTy<'db>,  // Ty, not Value
  ) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
    • [ ] Change parameter to RcTy
    • [ ] Update all call sites

  Task 9.2: Update elab/expr.rs synth function
  pub fn synth<'a, 'db, Db>(
      db: &'db Db,
      elab: &mut Elaborator<'a, 'db>,
      expr: &Expression,
  ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
    • [ ] Return RcTy instead of RcValue
    • [ ] Update all call sites

  Task 9.3: Update Kernel context
  pub struct Context<'db> {
      pub types: Vec<RcTy<'db>>,  // Ty, not Value
      pub terms: Vec<RcValue<'db>>,
  }
    • [ ] Change types vector
    • [ ] Update push/pop methods

  Task 9.4: Update all elaboration helpers
    • [ ] elab_pi → return type is RcTy
    • [ ] elab_arrow → return type is RcTy
    • [ ] elab_telescope → push RcTy to context
    • [ ] expect → takes RcTy parameters

  Phase 10: Testing

  Task 10.1: Fix broken tests
    • [ ] Run cargo test -p hwml_core
    • [ ] Fix each failing test
    • [ ] Update test expectations for new types

  Task 10.2: Add new tests for native types
    • [ ] Test @x : UniverseType works
    • [ ] Test @x : SignalUniverseType works
    • [ ] Test @x : ModuleUniverseType works
    • [ ] Test Pi type synthesis
    • [ ] Test HArrow type checking

  Task 10.3: Test Tarski bridge
    • [ ] Test check_ty for El(code) validates code type
    • [ ] Test check_ty for SignalEl(code) validates code type
    • [ ] Test check_ty for ModuleEl(code) validates code type

  Task 10.4: Test cumulativity
    • [ ] Test El(UniverseCode(0)) <: El(UniverseCode(1))
    • [ ] Test universe subsumption works

  Task 10.5: Integration tests
    • [ ] Test full elaboration pipeline
    • [ ] Test with real code examples
    • [ ] Test error messages

  Phase 11: Documentation and Cleanup

  Task 11.1: Update design documents
    • [ ] Document the correct architecture
    • [ ] Update design/syn-ty-design-vs-implementation.md
    • [ ] Remove mentions of temporary hacks

  Task 11.2: Add architectural comments
    • [ ] Comment TCEnvironment explaining the split
    • [ ] Comment type_synth/type_check explaining invariants
    • [ ] Document the Tarski bridge

  Task 11.3: Code cleanup
    • [ ] Remove all dead code
    • [ ] Remove all "ARCHITECTURAL ISSUE" comments
    • [ ] Remove all "TEMPORARY" comments
    • [ ] Format code

  Task 11.4: Final verification
    • [ ] cargo test - all tests pass
    • [ ] cargo clippy - no warnings
    • [ ] cargo build --release - clean build
    • [ ] Review all changes


  ───────────────────────────────────────────────────────────────────

  Execution Strategy

  Clean, No-Compromise Approach:

    1. Phase 2: Change all signatures at once (will break everything)
    2. Phase 3: Implement equality (needed by everything else)
    3. Phase 4: Implement synthesis bottom-up (leaf functions first)
    4. Phase 5: Implement checking top-down (dispatcher last)
    5. Phase 6: Fix check_ty properly
    6. Phases 7-9: Update helpers and downstream code
    7. Phases 10-11: Test and document

  No temporary hacks. No bridges. No workarounds.

  The codebase will not compile until Phase 5 is complete, but that's fine - we're doing a clean refactor.