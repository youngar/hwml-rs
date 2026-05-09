Here is the complete algorithm for the unification loop, pulling all the transition rules from the paper into a concrete, executable pipeline.

In a real implementation, you maintain a state consisting of `(Delta, K)` where `Delta` is your meta-variable context (keeping track of their types and solutions) and `K` is a queue of `Unify` constraints. The algorithm repeatedly pops a constraint from `K` and matches it against the rules below.

### The Unification Algorithm: `step(constraint)`

```haskell
function step(constraint):
  match constraint:
  
    -- ==========================================================
    -- PHASE 1: DECOMPOSITION & ORIENTATION
    -- Strip away matching rigid structures (lambdas, pairs, constructors).
    -- ==========================================================
    
    [cite_start]-- Function Decomposition [cite: 1]
    case Unify(Lam x M, Lam y N, Pi A B):
        return [Unify(M, N[x/y], B)]
    case Unify(Lam x M, R, Pi A B):
        return [Unify(M, App R x, B)]
    case Unify(R, Lam x M, Pi A B):
        return [Unify(App R x, M, B)]
        
    [cite_start]-- Pair Decomposition [cite: 1]
    case Unify(Pair M1 M2, Pair N1 N2, Sigma A B):
        return [Unify(M1, N1, A), Unify(M2, N2, B[M1/x])]
    case Unify(Pair M1 M2, R, Sigma A B):
        return [Unify(M1, Fst R, A), Unify(M2, Snd R, B[M1/x])]
    case Unify(R, Pair M1 M2, Sigma A B):
        return [Unify(Fst R, M1, A), Unify(Snd R, M2, B[Fst R/x])]
        
    [cite_start]-- Neutral Decomposition (Spines) [cite: 1]
    case Unify(E1[H1], E2[H2], C):
        if H1 == H2: 
            return decomposeSpine(E1, E2)
        else: 
            throw RigidClashError  -- Unification fundamentally fails
            
    [cite_start]-- Orientation [cite: 1]
    case Unify(M, Meta u sigma, C):
        if not isMeta(M): 
            return [Unify(Meta u sigma, M, C)]

    -- ==========================================================
    -- PHASE 2: LOWERING
    -- If a metavariable is stuck inside an elimination context (E), 
    -- split it into smaller metavariables to free it.
    -- ==========================================================
    
    case Unify(E[Meta u sigma], M, C) where E is not empty:
        if type(u) == Pi A B:
            v = newMeta(type = B)
            instantiate(u, Lam x v)
            [cite_start]return [Unify(E[(Lam x v)[sigma]], M, C)] -- Re-queue with new metas [cite: 1]
            
        if type(u) == Sigma A B:
            v1 = newMeta(type = A)
            v2 = newMeta(type = B[v1/x])
            instantiate(u, Pair v1 v2)
            [cite_start]return [Unify(E[(Pair v1 v2)[sigma]], M, C)] -- Re-queue [cite: 1]

    -- ==========================================================
    -- PHASE 3: MASSAGING SUBSTITUTIONS
    -- Try to turn 'sigma' into a pure variable substitution 'rho'.
    -- ==========================================================
    
    case Unify(Meta u sigma, M, C):
        if not isVariableSubstitution(sigma):
            [cite_start]-- Try Eta-Contraction [cite: 1]
            if canEtaContract(sigma):
                sigma' = etaContract(sigma)
                return [Unify(Meta u sigma', M, C)]
                
            [cite_start]-- Try Eliminating Projections & Sigma-Flattening [cite: 1]
            if hasProjections(sigma) or hasSigmaInContext(u):
                (u', sigma', M') = applyFlattening(u, sigma, M)
                return [Unify(Meta u' sigma', M', C)]
                
            -- If we can't massage it into a pattern, we are stuck for now.
            return PostponeConstraint

        -- ==========================================================
        -- PHASE 4: PRUNING AND SOLVING
        -- 'sigma' is now a pure variable substitution 'rho'.
        -- ==========================================================
        
        else:
            rho = sigma 
            
            [cite_start]-- Same Meta-Variable [cite: 1]
            if M == Meta u xi:
                -- e.g., u[x, y] = u[x, z]  =>  u only depends on x
                intersect = intersectSubsts(rho, xi)
                v = newMeta(context = intersect)
                instantiate(u, v[intersect])
                [cite_start]return [] -- Successfully solved [cite: 1]

            [cite_start]-- Occurs Check [cite: 1]
            if occursRigidly(u, M):
                [cite_start]throw OccursCheckFailedError  -- Infinite term [cite: 1]

            [cite_start]-- Pruning [cite: 1]
            if not isSubset(freeVariables(M), rho):
                -- M contains variables not in rho. Try to prune them out of M.
                (success, M_pruned) = attemptPrune(M, rho)
                if success:
                    return [Unify(Meta u rho, M_pruned, C)]
                else:
                    throw PruningFailedError

            [cite_start]-- Final Solve (Inverse Substitution) [cite: 1]
            M_inv = invertSubstitution(rho, M)
            instantiate(u, M_inv)
            [cite_start]return [] -- Successfully solved [cite: 1]

```

### How the Main Loop Consumes This

Your top-level elaborator loop will look roughly like this:

1. Pop `constraint` from `K`.
2. Run `newConstraints = step(constraint)`.
3. If it returns new constraints, prepend them to `K`.
4. If it triggers an `instantiate(u, term)` effect, you must immediately walk through `K` and replace all occurrences of `u` with `term`.
5. If it returns `PostponeConstraint`, push the constraint to a secondary "stuck" queue.
6. If `K` becomes empty, move all constraints from the "stuck" queue back into `K` (because instantiating a metavariable elsewhere might have unblocked them). If `K` is still empty, you win!

Would you like to zoom in on how the `invertSubstitution` function is implemented to safely reverse `rho` against the term `M`, or would you like to explore how to implement `attemptPrune`?
