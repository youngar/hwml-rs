-- | Type checks a term, treating meta-variables as object variables (no
-- unification).
module Tog.TypeCheck
  ( check
  , definitionallyEqual
  , instantiateMeta
  , checkMetaTypeConsistency
  ) where

import           Tog.Prelude
import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Names
import           Tog.Names.Sorts
import           Tog.Term
import           Data.PhysEq
import           Tog.PrettyPrint                  ((<+>), ($$), (//>), render)
import qualified Tog.PrettyPrint                  as PP
import           Tog.Monad
import           Tog.Error

-- | @check Γ t A@ checks that @t@ is of type @A@ in @Γ@, treating
-- metavariables as object variables.
--
-- Because type-checking is actually done via unification, this function
-- serves only as a sanity check.
check
  :: (IsTerm t)
  => Ctx t -> Term t -> Type t -> TC_ t ()
check ctx t type_ = do
  let msg = do
        tDoc <- prettyMWithCtx ctx t
        typeDoc <- prettyMWithCtx ctx type_
        return $
          "t:" //> tDoc $$
          "type:" //> typeDoc
  debugBracket DL.Check msg $ do
    tView <- whnfView t
    case tView of
      Con dataCon args -> do
        DataCon tyCon _ dataConType <- getDefinition dataCon
        tyConArgs <- matchTyCon tyCon type_
        appliedDataConType <- openContextual dataConType tyConArgs
        checkConArgs ctx args appliedDataConType
      Refl -> do
        typeView <- whnfView type_
        case typeView of
          Equal type' t1 t2 -> do
            definitionallyEqual ctx type' t1 t2
          _ -> do
            checkError $ ExpectingEqual type_
      Lam body -> do
        (dom, cod) <- matchPi type_
        name <- getAbsName_ body
        ctx' <- extendContext ctx (name, dom)
        check ctx' (unAbs body) (unAbs cod)
      _ -> do
        type' <- infer ctx t
        definitionallyEqual ctx set type' type_

-- | Check that the arguments to a constructor match its type
--   This function is not specific to constructors, in principle
--   it can be used with any constant.
checkConArgs
  :: (IsTerm t)
  => Ctx t -> [Term t] -> Type t -> TC t r s ()
checkConArgs _ [] _ = do
  return ()
checkConArgs ctx (arg : args) type_ = do
  (dom, cod) <- matchPi type_
  check ctx arg dom
  cod' <-  instantiate_ cod arg
  checkConArgs ctx args cod'

-- | Checks that a list of eliminations (application to an argument,
--   and projection), can actually be applied to a type.
checkSpine
  :: (IsTerm t)
  => Ctx t -> Term t -> [Elim t] -> Type t -> TC t r s (Type t)
checkSpine _ _ [] type_ =
  return (type_)
checkSpine ctx h (el : els) type_ = case el of
  Proj proj -> do
    (h', type') <- applyProjection proj h type_
    checkSpine ctx h' els type'
  Apply arg -> do
    (dom, cod) <- matchPi type_
    check ctx arg dom
    cod' <- instantiate_ cod arg
    h' <- eliminate h [Apply arg]
    checkSpine ctx h' els cod'

-- | Computes the result of applying a projection to a term, and the resulting
--   type.
applyProjection
  :: (IsTerm t)
  => Projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC t r s (Term t, Type t)
applyProjection proj h type_ = do
  (tyCon, tyConArgs) <- matchTyCon_ type_
  -- We open the projection in the same context as the type constructor
  let openedProj = first (const (pName proj)) tyCon 
  Projection _ _ projType <- getDefinition openedProj 
  appliedProjType <-  openContextual projType tyConArgs
  appliedProjTypeView <- whnfView appliedProjType
  case appliedProjTypeView of
    Pi _ endType -> do
      endType' <- instantiate_ endType h
      h'       <- eliminate h [Proj proj]
      return (h', endType')
    _ -> do
      doc <- prettyM_ appliedProjType
      fatalError $ "impossible.applyProjection: " ++ render doc

-- | Infers the type of a term from its syntax, checking it.
--   This can be used in a very limited number of cases.
--
--   Note that the if this function returns a type,
--   it is guaranteed that the term has that type.
infer
  :: (IsTerm t)
  => Ctx t -> Term t -> TC t r s (Type t)
infer ctx t = do
  debugBracket DL.Infer (prettyMWithCtx ctx t) $ do
    tView <- whnfView t
    case tView of
      Set ->
        return set
      Pi dom (Abs name cod) -> do
        check ctx dom set
        ctx' <- extendContext ctx (name, dom)
        check ctx' cod set
        return set
      App h elims -> do
        type_ <- inferHeadType ctx h
        h' <- app h []
        checkSpine ctx h' elims type_
      Equal type_ t1 t2 -> do
        check ctx type_ set
        check ctx t1 type_
        check ctx t2 type_
        return set
      _ -> do
        fatalError "impossible.infer: non-inferrable type."

-- | Extracts the parameters of a type constructor from a type
--   which is the result of the application of that type constructor.
matchTyCon
  :: (IsTerm t) => Opened TyConName t -> Type t -> TC t r s [Term t]
matchTyCon tyCon type_ = do
  let fallback = checkError $ ExpectingTyCon (Just$ opndKey tyCon) type_
  (tyCon', tyConArgs) <- matchTyCon_ type_
  synEq tyCon tyCon' >>= \case
    True -> return tyConArgs
    False -> fallback

matchTyCon_
  :: (IsTerm t) => Type t -> TC t r s (Opened TyConName t, [Term t])
matchTyCon_ type_ = do
  typeView <- whnfView type_
  let fallback = checkError $ ExpectingTyCon Nothing type_
  case typeView of
    App (Def (OTyCon tyCon)) elims -> do
      case  mapM isApply elims of
        Just tyConArgs -> return (tyCon, tyConArgs)
        _ -> fallback
    _ -> fallback

-- | Extracts the domain and co-domain of a ∏-type
matchPi
  :: (IsTerm t) => Type t -> TC t r s (Type t, Abs t)
matchPi type_ = do
  typeView <- whnfView type_
  case typeView of
    Pi dom cod -> do
      return (dom, cod)
    _ -> do
      checkError $ ExpectingPi type_

matchPi_
  :: (IsTerm t) => Type t -> TC t r s (Type t, Type t)
matchPi_ = matchPi >&> second unAbs

-- Definitional equality
------------------------------------------------------------------------

-- | Type-directed definitional equality, up to βηδ.
definitionallyEqual :: (IsTerm t) => Ctx t -> Type t -> Term t -> Term t -> TC_ t ()
definitionallyEqual ctx type_ t1 t2 = checkEqual (ctx, type_, t1, t2)

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

checkEqual
  :: (IsTerm t)
  => CheckEqual t -> TC t r s ()
checkEqual x@(ctx, type_, t1, t2) = do
  let msg = runNamesT ctx$ do
        typeDoc <- prettyM type_
        t1Doc <- prettyM t1
        t2Doc <- prettyM t2
        return $
          "type:" //> typeDoc $$
          "t1:" //> t1Doc $$
          "t2:" //> t2Doc
  debugBracket DL.DefEqual msg $
    runCheckEqual [checkPhysEq, checkSynEq, etaExpand] compareTerms x
  where
    runCheckEqual [] finally x' = do
      finally x'
    runCheckEqual (action : actions) finally x' = do
      mbX <- action x'
      forM_ mbX $ runCheckEqual actions finally

-- | Check two terms for physical (pointer) equality
checkPhysEq :: (IsTerm t) => CheckEqual t -> TC t r s (Maybe (CheckEqual t))
checkPhysEq args@(ctx, type_, t1, t2) = do
  enabled <- confPhysicalEquality <$> readConf
  if enabled then do
    debug_ "checkPhysEq" ""
    t1' <- ignoreBlocking =<< whnf t1
    t2' <- ignoreBlocking =<< whnf t2

    eq <- physEq t1' t2'
    return $ if eq
      then Nothing
      else Just (ctx, type_, t1', t2')
  else do
    return$ Just args

-- | Check two terms for syntactic equality (no ηβδ reduction)
checkSynEq :: (IsTerm t) => CheckEqual t -> TC t r s (Maybe (CheckEqual t))
checkSynEq args@(ctx, type_, t1, t2) = do
  disabled <- confDisableSynEquality <$> readConf
  if disabled then return (Just args)
  else do
    debug_ "checkSynEq" ""
    -- Optimization: try with a simple syntactic check first.
    t1' <- ignoreBlocking =<< whnf t1
    t2' <- ignoreBlocking =<< whnf t2
    
    eq <- synEq t1' t2'
    return $ if eq
      then Nothing
      else Just (ctx, type_, t1', t2')

-- | Applies η expansion to a term (if possible)
etaExpand :: (IsTerm t) => CheckEqual t -> TC t r s (Maybe (CheckEqual t))
etaExpand (ctx, type_, t1, t2) = do
  debug "etaExpand" $ runNamesT ctx $ do
    typeDoc <- prettyM type_
    t1Doc <- prettyM t1
    t2Doc <- prettyM t2
    return $
      "type:" //> typeDoc $$
      "t1:" //> t1Doc $$
      "t2:" //> t2Doc
  f <- expand
  t1' <- f t1
  t2' <- f t2
  return $ Just (ctx, type_, t1', t2')
  where
    expand = do
      typeView <- whnfView type_
      case typeView of
        App (Def (OTyCon tyCon)) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant _ (Record dataCon projs) -> return $ \t -> do
              tView <- whnfView t
              case tView of
                Con _ _ -> return t
                _       -> do
                  ts <- sequence [eliminate t [Proj p] | Opened p _ <- projs]
                  con dataCon ts
            _ ->
              return return
        Pi _ codomain -> return $ \t -> do
          name <- getAbsName_ codomain
          v <- var $ boundVar name
          tView <- whnfView t
          case tView of
            Lam _ -> return t
            _     -> do t' <-  weaken_ 1 t
                        t'' <- lam =<< Abs name <$> eliminate t' [Apply v]
                        return t''
        _ ->
          return return

-- ^ Compare terms up to βηδ equivalence
compareTerms :: (IsTerm t) => CheckEqual t -> TC t r s ()
compareTerms (ctx, type_, t1, t2) = do
  debug_ "compareTerms" ""
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
      checkEqual (ctx, set, dom1, dom2)
      name <- getAbsName_ cod1
      ctx' <- extendContext ctx (name,dom1)
      checkEqual (ctx', set, unAbs cod1, unAbs cod2)
    (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
      checkEqual (ctx, set, type1', type2')
      checkEqual (ctx, type1', l1, l2)
      checkEqual (ctx, type1', r1, r2)
    (Equal _ _ _, Refl, Refl) -> do
      return ()
    (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) -> do
      sameDataCon <- synEq dataCon dataCon'
      if sameDataCon
        then do
          let Just tyConPars = mapM isApply tyConPars0
          DataCon _ _ dataConType <- getDefinition dataCon
          appliedDataConType <-  openContextual dataConType tyConPars
          checkEqualSpine ctx appliedDataConType Nothing (map Apply dataConArgs1) (map Apply dataConArgs2)
        else do
          fallback
    (Set, Set, Set) -> do
      return ()
    (_, App h elims1, App h'' elims2) -> do
      sameH <- synEq h h''
      if sameH
        then do
          hType <- inferHeadType ctx h
          h' <- app h []
          checkEqualSpine ctx hType (Just h') elims1 elims2
        else do
          fallback
    (_, _, _) -> do
      fallback

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t) -> [Elim t] -> [Elim t] -> TC t r s ()
checkEqualSpine _ _ _ [] [] = do
  return ()
checkEqualSpine ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  let fallback =
        checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      (dom, cod) <- matchPi type_
      checkEqual (ctx, dom, arg1, arg2)
      cod' <-  instantiate_ cod arg1
      mbH' <- traverse (`eliminate` [Apply arg1]) mbH
      checkEqualSpine ctx cod' mbH' elims1 elims2
    (Proj proj, Proj proj') -> do
      sameProj <- synEq proj proj'
      if sameProj
        then do
          let Just h = mbH
          (h', type') <- applyProjection proj h type_
          checkEqualSpine ctx type' (Just h') elims1 elims2
        else do
          fallback
    _ ->
      fallback
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

-- Safe metavar instantiation
------------------------------------------------------------------------

instantiateMeta
  :: (IsTerm t)
  => Meta -> MetaBody t -> TC_ t ()
instantiateMeta mv mvb' = do

  let msg = do
        tDoc <- prettyM_ mvb'
        return $
          "metavar:" //> PP.pretty mv $$
          "term:" //> tDoc

  
  debugBracket DL.InstantiateMeta msg $ do
    mvb <- maybeNf mvb'
    checkConsistency <- confCheckMetaConsistency <$> readConf
    when checkConsistency $ do
      mvType <- getMetaType mv
      -- Check that it has not been instantiated already
      lookupMetaBody mv >>= \case
          Just mvbPrev -> do
              mvTypeDoc <- prettyM_ mvType
              tDoc <- prettyM_ mvb
              tPrevDoc <- prettyM_ mvbPrev
              typeError . ppGenericError $
                 "Doubly instantiated meta" $$
                 "metavar:" <+> PP.pretty mv $$
                 "type:" //> mvTypeDoc $$
                 "previous:" //> tPrevDoc $$
                 "new:" //> tDoc
          Nothing -> return ()

      -- Check meta type consistency
      checkMetaTypeConsistency mv mvb

    uncheckedInstantiateMeta mv mvb


checkMetaTypeConsistency :: (IsTerm t) => Meta -> MetaBody t -> TC_ t ()
checkMetaTypeConsistency mv mvb = do

 let msg = runNamesT C0$ do
      mvbDoc    <- prettyM mvb
      mvTypeDoc <- prettyM =<< getMetaType mv
      return$
         "metavar:" //> PP.pretty mv $$
         "body:"    //> mvbDoc $$
         "type:"    //> mvTypeDoc

 debugBracket DL.CheckMetaConsistency msg $ do
    mvType <- getMetaType mv

    let msg' err = runNamesT C0$ do
            mvTypeDoc <- prettyM mvType
            tDoc <- prettyM mvb
            return $
               "Inconsistent meta" $$
               "metavar:" <+> PP.pretty mv $$
               "type:" //> mvTypeDoc $$
               "term:" //> tDoc $$
               "err:" //> err

    t <- metaBodyToTerm mvb
    assert msg' $ check C0 t mvType
