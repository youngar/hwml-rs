{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -Werror #-}
module Tog.Unify.Impl.Simple
  (module Tog.Unify.Class
  ,Simple)
  where

import Tog.Unify.Class hiding (done)
import Tog.Unify.Common

import Tog.Prelude 
import Tog.PrettyPrint (($$), (<+>), (//>), (//), group, hang)
import qualified Tog.PrettyPrint as PP
import Tog.Error
import Tog.Term
import Tog.Monad
import qualified Data.BitSet as B

import           Tog.Names
import           Tog.Names.Sorts

import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Data.PhysEq

#include "impossible.h"

data Simple
type C t  = Constraint Simple t
type Constraints_ t = Constraints Simple t
type UFS t a = UF Simple t a
type UFS_ t r = UF_ Simple t r

instance UnifierImpl Simple where
  unifierShortName = "S"
  unifierLongName  = "Simple"

instance Unify t => Unifier Simple t where
  data Constraint Simple t =
      Unify {
            ctx :: Ctx t
          , ty  :: Type t
          , lht :: Term t
          , rht :: Term t
          }
    | UnifySpine {
            ctx :: Ctx t
          , ty  :: Type t
          , hd  :: Maybe (Term t)
          , lhs :: [Elim (Term t)]
          , rhs :: [Elim (Term t)]
          }

  makeConstraint ctx (type1 :∋ t1) (type2 :∋ t2) =
     (>>:) <$> newConstraint (Unify ctx set type1 type2)
           <*> newConstraint (Unify ctx type1 t1 t2)

  refine constr0 = case constr0 of
    Unify ctx type_ t1 t2 -> do
      checkEqual (ctx, type_, t1, t2)
    UnifySpine ctx type_ mbH elims1 elims2 -> do
      checkEqualSpine' ctx type_ mbH elims1 elims2

instance ExpandGuards (Constraint Simple t) where
  expandGuards s = pure s

instance PrettyM t (C t) where
  prettyM = \case 
      Unify ctx type_ t1 t2 -> do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyM type_
        t1Doc <- prettyM t1
        t2Doc <- prettyM t2
        return $ group $
          ctxDoc <+> "|-" //
          group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
      UnifySpine ctx type_ mbH elims1 elims2 -> do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyM type_
        hDoc <- case mbH of
          Nothing -> return "no head"
          Just h  -> prettyM h
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "UnifySpine" $$
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "h:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc


type CheckEqual t = (Ctx t, Type t, Term t, Term t)

data CheckEqualProgress t
  = Done (Constraints_ t)
  | KeepGoing (CheckEqual t)

done :: Constraints_ t -> TC t r s (CheckEqualProgress t)
done = return . Done

keepGoing :: CheckEqual t -> TC t r s (CheckEqualProgress t)
keepGoing = return . KeepGoing

checkEqual :: (Unify t) => CheckEqual t -> UFS t (Constraints_ t)
checkEqual (ctx0, type0, t1_0, t2_0) = do
  let msg = runNamesT ctx0$ do
        ctxDoc <- prettyM ctx0
        typeDoc <- prettyM type0
        xDoc <- prettyM t1_0
        yDoc <- prettyM t2_0
        return $
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "x:" //> xDoc $$
          "y:" //> yDoc
  debugBracket DL.Unify msg $ do
    runCheckEqual
      [ checkPhysEq         -- Check if the adresses are equal
      , doMaybeNf           -- Perhaps make the terms into Nf
      , checkSynEq          -- Optimization: check if the two terms are equal
      , etaExpandMeta'      -- Expand metavariable arguments
      , checkMetas          -- Assign/intersect metavariables if needed
      , etaExpand'          -- Eta-expand terms before comparing them
      ]
      compareTerms          -- If there are no blockers, then the terms must be in a canonical form
      (ctx0, type0, t1_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          constrsOrArgs <- action args
          case constrsOrArgs of
            Done constrs    -> return constrs
            KeepGoing args' -> runCheckEqual actions finally args'

doMaybeNf :: (IsTerm t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
doMaybeNf (ctx, type_, t1, t2) = do
  t1' <- maybeNfElseWhnf t1
  t2' <- maybeNfElseWhnf t2
  keepGoing (ctx, type_, t1', t2')

checkSynEq
  :: (Unify t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
checkSynEq args@(_ctx, _type, t1, t2) = do
  disabled <- confDisableSynEquality <$> readConf
  if disabled
    then do
      keepGoing args
    else do
      debugBracket_ DL.CheckSynEq "" $ do
        -- Optimization: try with a simple syntactic check first.
        eq <- synEq t1 t2
        if eq
          then done solved
          else keepGoing args

checkPhysEq
  :: (Unify t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
checkPhysEq args@(_ctx, _type, t1, t2) = do
  enabled <- confPhysicalEquality <$> readConf
  if enabled
    then do
      debugBracket_ DL.CheckPhysEq "" $ do
        -- Optimization: try with a simple syntactic check first.
        eq <- physEq t1 t2
        if eq
          then done solved
          else keepGoing args
    else do
      keepGoing args

etaExpandMeta'
  :: (Unify t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
etaExpandMeta' (ctx, type0, t1, t2) = do
  t1' <- etaExpandMeta t1
  t2' <- etaExpandMeta  t2
  keepGoing (ctx, type0, t1', t2')

etaExpand'
  :: (Unify t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
etaExpand' (ctx, type0, t1, t2) = do
  t1' <- etaExpand type0 t1
  t2' <- etaExpand type0 t2
  keepGoing (ctx, type0, t1', t2')

checkMetas
  :: (Unify t)
  => CheckEqual t -> UFS t (CheckEqualProgress t)
checkMetas (ctx, type_, t1, t2) = do
  blockedT1 <- whnf t1
  t1' <- ignoreBlocking blockedT1
  blockedT2 <- whnf t2
  t2' <- ignoreBlocking blockedT2
  let syntacticEqualityOrPostpone mvs = do
        eq <- synEq t1' t2'
        if eq
          then done solved
          else do
            mvsDoc <- prettyM_ mvs
            debug_ "both sides blocked" $ "waiting for" <+> mvsDoc
            done =<< newBlockedConstraint (anyMeta mvs) (Unify ctx type_ t1' t2')
  case (blockedT1, blockedT2) of
    (BlockingHeadMeta mv1 els1, BlockingHeadMeta mv2 els2) -> do
      if mv1 == mv2 then
        intersectMetaSpine ctx mv1 els1 els2 >>= \case                                                               
          Just mvs -> syntacticEqualityOrPostpone mvs
          Nothing  -> done solved
      else
        metaAssign ctx type_ mv1 els1 t2' >>= \case
          Left (mvs1, t2'') ->
            whnf t2'' >>= \case
              -- If there still is a meta on the other size, try to solve the equation
              -- in the other direction.
              BlockingHeadMeta mv2' els2' -> done =<< metaAssign_ ctx type_ mv2' els2' t1'
              -- Otherwise, retry later
              blockedT2''               -> do
                t2''' <- ignoreBlocking blockedT2''
                done =<< newBlockedConstraint (anyMeta mvs1) (Unify ctx type_ t1' t2''')
          Right cs          -> done cs
        
    (BlockingHeadMeta mv elims, _) -> do
      done =<< metaAssign_ ctx type_ mv elims t2'
    (_, BlockingHeadMeta mv elims) -> do
      done =<< metaAssign_ ctx type_ mv elims t1'
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
    (BlockedOn mvs f elims, _) -> do
      done =<< checkEqualBlockedOn ctx type_ mvs f elims t2'
    (_, BlockedOn mvs f elims) -> do
      done =<< checkEqualBlockedOn ctx type_ mvs f elims t1'
    -- If one of them is blocked on definitions, we stop
    (b1, b2) -> do
      case isBlocked b1 <> isBlocked b2 of
        Nothing -> keepGoing (ctx, type_, t1', t2')
        Just bs -> syntacticEqualityOrPostpone bs

checkEqualBlockedOn
  :: forall t.
     (Unify t)
  => Ctx t -> Type t
  -> Guard -> BlockedHead t -> [Elim t]
  -> Term t
  -> UFS t (Constraints_ t)
checkEqualBlockedOn ctx type_ mvs bh elims1 t2 = do
  let msg = runNamesT ctx$ do
        bhDoc <- prettyM bh
        mvsDoc <- prettyM mvs
        return $ "Equality blocked on metavars" <+> mvsDoc <>
                  ", trying to invert definition" <+> bhDoc
  t1 <- ignoreBlocking $ BlockedOn mvs bh elims1
  debugBracket DL.CheckEqualBlockedOn msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "head is J, couldn't invert." ""
        fallback t1
      BlockedOnFunction fun1 -> do
        Constant _ (Function (Inst clauses)) <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "couldn't invert." ""
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfView t2
            let notInvertible = do
                  t2Head <- termHead t2
                  case t2Head of
                    Nothing -> do
                      debug_ "definition invertible but we don't have a clause head." ""
                      fallback t1
                    Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                      debug_ ("inverting on" <+> PP.pretty tHead) ""
                      -- Make the eliminators match the patterns
                      matched <- matchPats pats elims1
                      -- And restart, if we matched something.
                      if matched
                        then do
                          debug_ "matched constructor, restarting" ""
                          checkEqual (ctx, type_, t1, t2)
                        else do
                          debug_ "couldn't match constructor" ""
                          fallback t1
                    Just _ -> do
                      checkError $ TermsNotEqual type_ t1 type_ t2
            case t2View of
              App (Def fun2) elims2 -> do
                sameFun <- synEq fun1 fun2
                if sameFun
                  then do
                    debug_ "could invert, and same heads, checking spines." ""
                    equalSpine (Def fun1) ctx elims1 elims2
                  else notInvertible
              _ -> do
                notInvertible
  where
    fallback t1 = do
      newBlockedConstraint (anyMeta mvs) (Unify ctx type_ t1 t2)

    matchPats :: [Pattern t] -> [Elim t] -> UFS t Bool
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matched <- matchPat dataCon pats' elim
      (matched ||) <$> matchPats pats elims
    matchPats _ _ = do
      -- Less patterns than arguments is fine.
      --
      -- Less arguments than patterns is fine too -- it happens if we
      -- are waiting on some metavar which doesn't head an eliminator.
      return False

    matchPat :: Opened DConName t -> [Pattern t] -> Elim t -> UFS t Bool
    matchPat (Opened _ (_:_)) _ _ = do
      return False              
    matchPat openedDataCon@(Opened dataCon []) pats (Apply t) = do
      tView <- whnfView t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv (DConName dataCon)
          void $ matchPat openedDataCon pats . Apply =<< eliminate mvT mvArgs
          return True
        Con (ODCon (Opened dataCon' _)) dataConArgs | dataCon == dataCon' -> do
          matchPats pats (map Apply dataConArgs)
        Con (ORCon{}) _ -> __IMPOSSIBLE__
        _ -> do
          -- This can happen -- when we are blocked on metavariables
          -- that are impeding other definitions.
          return False
    matchPat _ _ _ = do
      -- Same as above.
      return False

equalSpine
  :: (Unify t)
  => Head t -> Ctx t -> [Elim t] -> [Elim t] -> UFS t (Constraints_ t)
equalSpine h ctx elims1 elims2 = do
  hType <- headType ctx h
  checkEqualSpine ctx hType h elims1 elims2

checkEqualApplySpine
  :: (Unify t)
  => Ctx t -> Type t -> [Term t] -> [Term t]
  -> UFS t (Constraints_ t)
checkEqualApplySpine ctx type_ args1 args2 =
  checkEqualSpine' ctx type_ Nothing (map Apply args1) (map Apply args2)

checkEqualSpine
  :: (Unify t)
  => Ctx t -> Type t -> Head t -> [Elim (Term t)] -> [Elim (Term t)]
  -> UFS t (Constraints_ t)
checkEqualSpine ctx type_ h elims1 elims2  = do
  h' <- app h []
  checkEqualSpine' ctx type_ (Just h') elims1 elims2

checkEqualSpine'
  :: (Unify t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> UFS t (Constraints_ t)
checkEqualSpine' ctx type_ mbH elims1 elims2 = do
  let msg = runNamesT ctx$ do
        typeDoc <- prettyM type_
        hDoc <- case mbH of
          Nothing -> return "No head"
          Just h  -> prettyM h
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket DL.CheckEqualSpine msg $
    checkEqualSpine'' ctx type_ mbH elims1 elims2


checkEqualSpine''
  :: (Unify t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> UFS t (Constraints_ t)
checkEqualSpine'' _ _ _ [] [] = do
  return solved
checkEqualSpine'' ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
    let fallback =
          checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom cod@(Abs name codBody) <- whnfView type_
        res1 <- checkEqual (ctx, dom, arg1, arg2)
        mbCod <- flip safeStrengthen (boundVar name) codBody
        mbH' <- traverse (`eliminate` [Apply arg1]) mbH
        -- If the rest is non-dependent, we can continue immediately.
        case mbCod of
          Just cod' -> do
            res2 <- checkEqualSpine' ctx cod' mbH' elims1 elims2
            return (res1 /\ res2)
          Nothing -> do
            cod' <- instantiateMaybeNf_ cod arg1
            (res1 >>:) <$> newConstraint (UnifySpine ctx cod' mbH' elims1 elims2)
      (Proj proj, Proj proj') -> do
          -- If it is a projection, then the head term (mbH) is necessarily
          -- non empty.
          -- We need the projected term to compute the type!
          sameProj <- synEq proj proj'
          if sameProj
            then do
              let Just h = mbH
              App (Def type_con) type_elims <- whnfView type_
              let OTyCon tyCon = type_con
              (h',type') <- applyProjection proj h tyCon type_elims
              checkEqualSpine' ctx type' (Just h') elims1 elims2
            else do
              fallback
      _ ->
        fallback
checkEqualSpine'' _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

metaAssign_
  :: (Unify t)
  => Ctx t -> Type t -> Meta -> [Elim (Term t)] -> Term t
  -> UFS t (Constraints_ t)
metaAssign_ ctx type_ mv elims t = metaAssign ctx type_ mv elims t >>= \case
  Left (mvs, t0) -> do
    mvT <- meta mv elims
    newBlockedConstraint (anyMeta mvs) $ Unify ctx type_ mvT t0
  Right cs -> return cs

-- | Result
-- 
--   Left: Could not assign the metavariable. Return a simplified
--         constraint and a Guard that moderates when to retry.
--   Right: One metavariable was assigned to the other. return the
--          resulting constraints (if any).
--
metaAssign
  :: forall t r. (Unify t)
  => Ctx t -> Type t -> Meta -> [Elim (Term t)] -> Term t
  -> UFS_ t r (Either (Guard, Term t) (Constraints_ t))
metaAssign ctx0 type0 mv elims t0 = do
  mvType <- getMetaType mv
  let msg = runNamesT ctx0$ do
        mvTypeDoc <- prettyM mvType
        elimsDoc <- prettyM elims
        tDoc <- prettyM t0
        return $
          "assigning metavar:" <+> PP.pretty mv $$
          "of type:" //> mvTypeDoc $$
          "elims:" //> elimsDoc $$
          "to term:" //> tDoc
  let fallback mvs t0' = do
        -- Also unblock the constraint if the metavariable being assigned
        -- happens to be instantiated elsewhere.
        return$ Left (metaGuard mv <> mvs, t0')
  debugBracket DL.MetaAssign msg $ do
    -- See if we can invert the metavariable
    invOrMvs <- do
      tt <- invertMeta ctx0 elims
      return $ case tt of
        Right x             -> Right x
        Left (CFail ())     -> Left $ metaGuard mv
        Left (CCollect mvs) -> Left $ metaGuard mv <> mvs
    case invOrMvs of
      Left mvs -> do
        debug_ "couldn't invert" ""
        -- If we can't invert, try to prune the variables not
        -- present on the right from the eliminators.
        t' <- maybeNf t0
        fvs <- fvAll <$> freeVars t'
        elims' <- maybeNf elims
        mbMvT <- pruneMeta fvs mv elims'
        -- If we managed to prune them, restart the equality.
        -- Otherwise, wait on the metavariables.
        case mbMvT of
          Nothing -> do
            fallback mvs t'
          Just mvT -> do
            mvT' <- eliminate mvT elims'
            Right <$> checkEqual (ctx0, type0, mvT', t')
      Right (ctx, acts, inv) -> do
        t <- applySubst t0 acts
        type_ <- applySubst type0 acts
        whenDebug $ unless (subNull acts) $ debug "could invert, new stuff" $ runNamesT ctx$ do
          ctxDoc <- prettyM ctx
          tDoc <- prettyM t
          typeDoc <- prettyM type_
          return $
            "ctx:" //> ctxDoc $$
            "type:" //> typeDoc $$
            "term:" //> tDoc
        debug "could invert" $ runNamesT ctx $ do
          invDoc <- prettyM inv
          return $ "inversion:" //> invDoc
        t1 <- prune (B.fromList $ invertMetaVars inv) t
        debug "pruned term" $ runNamesT ctx $ prettyM t1
        t2 <- applyInvertMeta ctx inv t
        case t2 of
          Success mvb -> do
            safeInstantiateMeta mv mvb 
            return$ Right solved
          Failure (CCollect mvs) -> do
            debug "inversion blocked on"$ runNamesT ctx $ prettyM mvs
            fallback (metasGuard mvs) t0
          Failure (CFail v) ->
            checkError $ FreeVariableInEquatedTerm mv elims t v

compareTerms :: (Unify t) => CheckEqual t -> UFS t (Constraints_ t)
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfView type_
  t1View <- whnfView t1
  t2View <- whnfView t2
  let fallback =
        checkError $ TermsNotEqual type_ t1 type_ t2
  case (typeView, t1View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom (Abs_ cod), Lam body1, Lam body2) -> do
      
      name <- getAbsName_ body1
      ctx' <- extendContext ctx (name, dom)
      checkEqual (ctx', cod, unAbs body1, unAbs body2)
    (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
      -- Pi : (A : Set) -> (A -> Set) -> Set
      piType <- do
        av <- var $ mkVar "A" 0
        b <- pi_ av set
        pi set . Abs "A" =<< pi_ b set
      cod1' <- lam cod1
      cod2' <- lam cod2
      checkEqualApplySpine ctx piType [dom1, cod1'] [dom2, cod2']
    (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
      -- _==_ : (A : Set) -> A -> A -> Set
      equalType_ <- do
        xv <- var $ mkVar "A" 0
        yv <- var $ mkVar "A" 1
        pi set . Abs "A" =<< pi_ xv =<< pi_ yv set
      checkEqualApplySpine ctx equalType_ [type1', l1, r1] [type2', l2, r2]
    (Equal _ _ _, Refl, Refl) -> do
      return solved
    (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) -> do
       sameDataCon <- synEq dataCon dataCon'
       if sameDataCon
         then do
           let Just tyConPars = mapM isApply tyConPars0
           DataCon _ _ dataConType <- getDefinition dataCon
           appliedDataConType <- openContextual dataConType tyConPars
           checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
         else do
           fallback
    (Set, Set, Set) -> do
      return solved
    (_, App h elims1, App h' elims2) -> do
      sameH <- synEq h h'
      if sameH then equalSpine h ctx elims1 elims2 else fallback
    (_, _, _) -> do
      fallback


 
