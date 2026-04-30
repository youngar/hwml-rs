-- | Common error type for elaboration, unification, and type-checking.
module Tog.Error
  ( CheckError(..)
  , pattern TermsNotEqual
  , pattern BlockedTermsNotEqual
  , ppCheckError
  , ppGenericError
  , ppScopeError
  , ppParseError
  , noErrorCode
  , isOffsetedError
  , scopeErrorCode
  , parseErrorCode
  ) where

import           Prelude                          hiding (abs, pi)

import           Tog.Prelude
import           Tog.Names
import           Tog.Names.Sorts
import qualified Tog.Abstract                     as SA
import           Tog.Term.Types
import           Tog.PrettyPrint                  (($$), (<+>), (//>))
import qualified Tog.PrettyPrint                  as PP

-- Errors
---------

data CheckError t
    = ExpectingEqual (Type t)
    | ExpectingPi (Type t)
    | ExpectingTyCon (Maybe TyConName) (Type t)
    | FreeVariableInEquatedTerm Meta [Elim t] (Term t) Var
    | OccursCheckFailed Meta (MetaBody (Term t))
    | SpineNotEqual (Type t) [Elim t] (Type t) [Elim t]
    | TermsNotEqual' Bool (Type t) (Term t) (Type t) (Term t)
    | PatternMatchOnRecord SA.Pattern TyConName -- Record type constructor
    | MismatchingArgumentsForModule QName (Tel t) [SA.Expr]
    | UnsolvedMetas [Meta]
    | EmptyPatternWithClauseBody
    | NoClauseBodyWithoutEmptyPattern
    | EmptyPatternOnBadType (Type t)
    | NotWHNFType (Type t)
    | forall a. (PrettyM t a) => BoundTwinVariable Var a
    | FailedAudit [Nat] PP.Doc (Ctx t) ((Term t, Term t) :∈ Type t)

pattern TermsNotEqual  :: Type t -> Term t -> Type t -> Term t -> CheckError t
pattern TermsNotEqual t1 a t2 b = TermsNotEqual' False t1 a t2 b
pattern BlockedTermsNotEqual  :: Type t -> Term t -> Type t -> Term t -> CheckError t
pattern BlockedTermsNotEqual t1 a t2 b = TermsNotEqual' True t1 a t2 b

-- All errors should be smaller than 100; larger numbers
-- are reserved for system errors (e.g. timeouts etc.).
offsetError :: Int -> Int
offsetError = (0+)

isOffsetedError :: Int -> Bool
isOffsetedError = (> offsetError 0)

checkErrorCode :: CheckError t -> Int
checkErrorCode err = offsetError $ case err of
     ExpectingEqual{}                    ->  1
     ExpectingPi{}                       ->  2
     ExpectingTyCon{}                    ->  3
     FreeVariableInEquatedTerm{}         ->  4
     OccursCheckFailed{}                 ->  5
     SpineNotEqual{}                     ->  6
     TermsNotEqual{}                     ->  7
     BlockedTermsNotEqual{}              ->  8
     PatternMatchOnRecord{}              ->  9
     MismatchingArgumentsForModule{}     -> 10
     UnsolvedMetas{}                     -> 11
     EmptyPatternWithClauseBody{}        -> 12
     NoClauseBodyWithoutEmptyPattern{}   -> 13
     EmptyPatternOnBadType{}             -> 14
     NotWHNFType{}                       -> 15
     BoundTwinVariable{}                 -> 16
     FailedAudit{}                       -> 42

noErrorCode, scopeErrorCode, parseErrorCode :: Int
noErrorCode = offsetError 99
scopeErrorCode = offsetError 70  
parseErrorCode = offsetError 60  

instance PrettyM t (CheckError t) where
  prettyM err =
    case err of
      TermsNotEqual' blocked type1 t1 type2 t2 -> do
        t1Doc <- prettyM t1
        type1Doc <- prettyM type1
        t2Doc <- prettyM t2
        type2Doc <- prettyM type2
        return $
          (if blocked then "Blocked terms" else "Terms") <> " not equal:" $$
          "t:" //> t1Doc $$
          "A:" //> type1Doc $$
          "u:" //> t2Doc $$
          "B:" //> type2Doc
      SpineNotEqual type1 es1 type2 es2 -> do
        type1Doc <- prettyM type1
        es1Doc <- PP.list <$> mapM prettyM es1
        type2Doc <- prettyM type2
        es2Doc <- PP.list <$> mapM prettyM es2
        return $
          "Spines not equal:" $$
          "es:" //> es1Doc $$
          "A:" //> type1Doc $$
          "ds:" //> es2Doc $$
          "B:" //> type2Doc
      FreeVariableInEquatedTerm mv els rhs v -> do
        mvDoc <- prettyM =<< meta mv els
        rhsDoc <- prettyM rhs
        return $ "Free variable `" <> prettyVar v <> "' in term equated to metavariable application:" $$
                 mvDoc $$ PP.nest 2 "=" $$ rhsDoc
      OccursCheckFailed mv mvb -> do
        mvbDoc <- prettyM mvb
        return $ "Attempt at recursive instantiation:" $$ PP.pretty mv <+> mvbDoc
      PatternMatchOnRecord synPat tyCon -> do
        tyConDoc <- prettyM tyCon
        return $ "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> tyConDoc
      ExpectingPi type_ -> do
        typeDoc <- prettyM type_
        return $ "Expecting a pi type, not:" //> typeDoc
      ExpectingEqual type_ -> do
        typeDoc <- prettyM type_
        return $ "Expecting an identity type, not:" //> typeDoc
      ExpectingTyCon Nothing type_ -> do
        typeDoc <- prettyM type_
        return $ "Expecting a type constructor application, not:" //> typeDoc
      ExpectingTyCon (Just tyCon) type_ -> do
        tyConDoc <- prettyM tyCon
        typeDoc <- prettyM type_
        return $ "Expecting a" <+> tyConDoc <> ", not:" //> typeDoc
      UnsolvedMetas mvs -> do
        return $ "UnsolvedMetas" <+> PP.pretty (map PP.Verbose mvs)
      MismatchingArgumentsForModule n tel args -> do
        telDoc <- prettyM tel
        return $
          "MismatchingArgumentsForModule" $$
          "module:" //> PP.pretty n $$
          "tel:" //> telDoc $$
          "args:" //> PP.hsep (map PP.pretty args)
      EmptyPatternWithClauseBody -> do
        return "EmptyPatternWithClauseBody"
      NoClauseBodyWithoutEmptyPattern -> do
        return "NoClauseBodyWithoutEmptyPattern"
      EmptyPatternOnBadType type_ -> do
        typeDoc <- prettyM type_
        return $
          "EmptyPatternOnBadType" $$
          "type:" //> typeDoc
      BoundTwinVariable v a -> do
         vDoc <- prettyM v
         t1Doc <- prettyM a
         return$ "Bound twin variable:"$$
                 "var:" //> vDoc $$
                 "term:" //> t1Doc
      NotWHNFType t -> do
         tDoc <- prettyM t
         return$ "Type " //> tDoc //> "is not in WHNF" //> tDoc
      FailedAudit cs doc ctx ((t1, t2) :∈ ty) -> do
        csDoc <- pure$ PP.pretty cs
        ctxDoc <- prettyM ctx
        t1Doc <- prettyM t1
        t2Doc <- prettyM t2
        tyDoc <- prettyM ty
        return $
          "Audit failed:" <+> doc $$
          "ctx:" //> ctxDoc $$
          "t:" //> t1Doc $$
          "u:" //> t2Doc $$
          "type:" //> tyDoc $$
          "constraints:" //> csDoc

    where
      prettyVar = PP.pretty



ppCheckError :: (MonadTerm t m, PrettyM t t) => CheckError t -> m PP.Error
ppCheckError err = PP.Error (checkErrorCode err) <$> prettyM_ err

ppGenericError :: PP.Doc -> PP.Error 
ppGenericError = PP.Error noErrorCode

ppScopeError :: PP.Doc -> PP.Error
ppScopeError = PP.Error scopeErrorCode

ppParseError :: PP.Doc -> PP.Error
ppParseError = PP.Error parseErrorCode

