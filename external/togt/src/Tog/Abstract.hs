{-# OPTIONS_GHC -w -fno-warn-incomplete-patterns #-}
{-| Abstract syntax produced by scope checker, input for the type checker.
 -}
module Tog.Abstract where

import           Tog.Prelude
import           Tog.PrettyPrint
import qualified Tog.Names as N
import qualified Tog.Names.Sorts as NS
import           Tog.Names (HasSrcLoc(..),SrcLoc)
import           Control.Comonad

-- * Abstract syntax.
------------------------------------------------------------------------

type Name = N.Name :@ SrcLoc 
instance Pretty Name where pretty = pretty . annValue
data QName = QName {qNameId :: (), qNameName :: !Name, qNameModule :: ![Name]} deriving (Eq, Ord, Show)
instance Pretty QName where pretty = pretty . qNameToInternal

type ConName = NS.ConSorted QName                            
type DefName = NS.DefSorted QName                            
type TyConName = (NS.Sorted 'NS.TyConS QName)
type FDefName = (NS.Sorted 'NS.FDefS QName)
type RConName = (NS.Sorted 'NS.RConS QName)
type ProjName = (NS.Sorted 'NS.ProjS QName)

instance HasSrcLoc QName where
  srcLoc = srcLoc . qNameName

qName :: Name -> [Name] -> QName
qName = QName ()

qNameCons :: Name -> QName -> QName
qNameCons n (QName _ n' ns) = QName () n (n' : ns)

qNameToInternal = N.qName <$> (annValue . qNameName) <*> (map annValue . qNameModule)
internalToQName (NS.getQName -> N.QName _ n ns) = QName () (pure n) (map pure ns)

-- | Properties
--   prop> srcLoc . (\(q :@@ s) -> q :@@ s) == srcLoc
--   prop> ∀ f. (\(q :@@ s) -> f q s) (q :@@ s) == f q s
--
--   But, it is not true in general that  id == (\(q :@@ s) -> q :@@ s)
pattern (:@@) :: N.QName -> SrcLoc -> QName
pattern q :@@ loc <- (((,) <$> qNameToInternal <*> srcLoc) -> (q,loc))
  where (N.QName _ n ns) :@@ loc = QName () (n :@ loc) (map pure ns)

-- | Properties
--   prop> srcLoc . (\(q :@@ s) -> q :@@ s) == srcLoc
--   prop> ∀ f. (\(q :@@ s) -> f q s) (q :@@ s) == f q s
--
--   But, it is not true in general that  id == (\(q :@@ s) -> q :@@ s)
pattern (:@@@) :: (Comonad f, Functor f) => f N.QName -> SrcLoc -> f QName
pattern fq :@@@ loc <- (((,) <$> fmap qNameToInternal <*> srcLoc . extract) -> (fq,loc))
  where fq :@@@ loc = fmap (\(N.QName _ n ns) -> QName () (n :@ loc) (map pure ns)) fq

data Module = Module QName Params [QName] [Decl]

type Params = [(Name, Expr)]

data Decl
  = TypeSig (TypeSig 'NS.FDefS)
  | Postulate (TypeSig 'NS.PDefS)
  | Data (TypeSig 'NS.TyConS)
  | Record (TypeSig 'NS.TyConS)
  | FunDef FDefName [Clause]
  | DataDef TyConName [Name] [TypeSig 'NS.DConS]
  | RecDef TyConName [Name] RConName [TypeSig 'NS.ProjS]
  | Module_ Module
  | Import QName [Expr]
  | Open QName

data TypeSig sort = Sig
  { typeSigName :: NS.Sorted sort QName
  , typeSigType :: Expr
  }

data Clause = Clause [Pattern] ClauseBody

data ClauseBody
  = ClauseBody Expr [Decl]
  | ClauseNoBody

data Expr
  = Lam Name Expr
  | Pi Name Expr Expr
  | Fun Expr Expr
  | Equal Expr Expr Expr
  | App Head [Elim]
  | Set SrcLoc
  | Meta SrcLoc
  | Refl SrcLoc
  | Con ConName [Expr]

data Head
  = Var Name
  | Def DefName
  | J SrcLoc

data Elim
  = Apply Expr
  | Proj ProjName
  deriving Eq

data Pattern
  = VarP Name
  | WildP SrcLoc
  | ConP ConName [Pattern]
  | EmptyP SrcLoc

-- | Number of variables bound by a list of pattern.
patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- | Number of variables bound by a pattern.
patternBindings :: Pattern -> Int
patternBindings (VarP _)      = 1
patternBindings (WildP _)     = 1
patternBindings (ConP _ pats) = patternsBindings pats
patternBindings EmptyP{}      = 0

-- * Instances
------------------------------------------------------------------------

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Module where
  srcLoc (Module x _ _ _) = srcLoc x

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    Postulate sig  -> srcLoc sig
    Data sig       -> srcLoc sig
    Record sig     -> srcLoc sig
    FunDef x _     -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x
    Module_ x      -> srcLoc x
    Open x         -> srcLoc x
    Import x _     -> srcLoc x

instance HasSrcLoc (TypeSig k) where
  srcLoc (Sig x _) = srcLoc x

instance HasSrcLoc Expr where
  srcLoc e = case e of
    Lam x _     -> srcLoc x
    Pi x _ _    -> srcLoc x
    Fun a _     -> srcLoc a
    Equal _ a _ -> srcLoc a
    App h _     -> srcLoc h
    Set p       -> p
    Meta p      -> p
    Con c _     -> srcLoc c
    Refl p      -> p

instance HasSrcLoc Head where
  srcLoc h = case h of
    Var x       -> srcLoc x
    Def x       -> srcLoc x
    J loc       -> loc

instance HasSrcLoc Pattern where
  srcLoc p = case p of
    WildP p  -> p
    VarP x   -> srcLoc x
    ConP c _ -> srcLoc c
    EmptyP x -> x

instance HasSrcLoc Elim where
  srcLoc e = case e of
    Apply e -> srcLoc e
    Proj x  -> srcLoc x

-- | Syntactic equality (ignoring source locations).

instance Eq Expr where
  Lam x e     == Lam x' e'      = x == x' && e == e'
  Pi x a b    == Pi x' a' b'    = x == x' && a == a' && b == b'
  Fun a b     == Fun a' b'      = a == a' && b == b'
  Equal a x y == Equal a' x' y' = a == a' && x == x' && y == y'
  App h es    == App h' es'     = h == h' && es == es'
  Set _       == Set _          = True
  Meta _      == Meta _         = True
  _           == _              = False

instance Eq Head where
  Var x  == Var x' = x == x'
  Def f  == Def f' = f == f'
  J _    == J _    = True
  _      == _      = False

-- Pretty printing
------------------------------------------------------------------------

instance Show Decl    where showsPrec = defaultShow
instance Show (TypeSig k) where showsPrec = defaultShow
instance Show Elim    where showsPrec = defaultShow
instance Show Expr    where showsPrec = defaultShow
instance Show Head    where showsPrec = defaultShow
instance Show Pattern where showsPrec = defaultShow

instance Pretty Module where
  pretty (Module name pars exports decls) =
    let parsDoc =
          let ds = [parens (pretty n <+> ":" <+> pretty ty) | (n, ty) <- pars]
          in if null ds then [] else [mconcat ds]
    in hsep ([text "module", pretty name] ++ parsDoc ++ ["where"]) $$>
       vcat (map pretty decls)

instance Pretty (TypeSig sort) where
  pretty (Sig x e) =
    pretty x <+> text ":" //> pretty e

instance Pretty Decl where
  pretty d = case d of
    TypeSig sig ->
      pretty sig
    Postulate sig ->
      text "postulate" $$> pretty sig
    Data sig ->
      text "data" $$> pretty sig
    Record sig ->
      text "record" $$> pretty sig
    FunDef f clauses ->
      vcat $ map (prettyClause f) clauses
    DataDef d xs cs ->
      hsep (text "data" : pretty d : map pretty xs ++ [text "where"]) $$>
      vcat (map pretty cs)
    RecDef r xs con fs ->
      hsep (text "record" : pretty r : map pretty xs ++ [text "where"]) $$>
      text "constructor" <+> pretty con $$
      text "field" $$>
      vcat (map pretty fs)
    Module_ m ->
      pretty m
    Open m ->
      hsep [text "open", pretty m]
    Import m args ->
      hsep (text "import" : pretty m : map (prettyPrec 4) args)
    where
      prettyClause f (Clause ps (ClauseBody e [])) =
        group (hsep (pretty f : map pretty ps ++ ["="]) //> pretty e)
      prettyClause f (Clause ps (ClauseBody e wheres)) =
        group (hsep (pretty f : map pretty ps ++ ["="]) //> pretty e) $$
        indent 2 ("where" $$ indent 2 (vcat (map pretty wheres)))
      prettyClause f (Clause ps ClauseNoBody) =
        group (hsep (pretty f : map pretty ps))

instance Pretty ClauseBody where
  pretty cb = case cb of
    ClauseNoBody -> "<no body>"
    ClauseBody t wheres -> pretty t $$ indent 2 ("where" $$ indent 2 (vcat (map pretty wheres)))

instance Pretty Head where
  pretty h = case h of
    Var x       -> pretty x
    Def f       -> pretty f
    J _         -> text "J"

instance Pretty Pattern where
  pretty e = case e of
    WildP _   -> text "_"
    VarP x    -> pretty x
    ConP c es -> parens $ sep $ pretty c : map pretty es
    EmptyP _  -> text "()"

-- Pretty printing terms
------------------------------------------------------------------------

instance Pretty Elim where
  prettyPrec p (Apply e) = condParens (p > 0) $ "$" <+> prettyPrec p e
  prettyPrec _ (Proj x)  = "." <> pretty x

instance Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        prettyPrec 3 x <+> text "==" //> prettyPrec 2 y
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $ align $
        prettyPrec 1 a <+> text "->" // pretty b
    Pi{} ->
      condParens (p > 0) $ align $
        prettyTel tel <+> text "->" // pretty b
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      text "\\" <> hsep (map pretty xs) <+> text "->" <+> pretty b
      where
        (xs, b) = lamView e
        lamView (Lam x b) = (x :) *** id $ lamView b
        lamView e         = ([], e)
    App{} -> prettyApp p (pretty h) es
      where
        (h, es) = appView e
        appView (App h es) = buildApp h [] es
        appView e = error $ "impossible: pretty application"

        -- This should not escape this function
        unsafeProjToDef :: ProjName -> DefName
        unsafeProjToDef f = NS.DefName NS.SPDefS (NS.sTrustMe$ unTagged f)

        buildApp :: Head -> [Expr] -> [Elim] -> (Head, [Expr])
        buildApp h es0 (Apply e : es1) = buildApp h (es0 ++ [e]) es1
        buildApp h es0 (Proj f  : es1) =
          buildApp (Def (unsafeProjToDef f)) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)
    Refl{} -> text "refl"
    Con c args -> prettyApp p (pretty c) args

prettyTel :: [(Name, Expr)] -> Doc
prettyTel = group . prs . reverse
  where
    prs []       = empty
    prs [b]      = pr b
    prs (b : bs) = group (prs bs) $$ pr b

    pr (x, e) = parens (pretty x <+> text ":" <+> pretty e)
