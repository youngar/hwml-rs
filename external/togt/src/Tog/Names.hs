{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE DeriveAnyClass #-}
-- | Qualified and unqualified names with source locations.
module Tog.Names
  ( -- * SrcLoc
    SrcLoc(..)
  , noSrcLoc
  , HasSrcLoc(..)
    -- * Names
  , Name(..)
  , mkName
  , QName(..)
  , qName
  , qNameCons
  , qNameSingleton
  , internal
  ) where

import           Tog.Prelude
import           Tog.PrettyPrint                  (Pretty, pretty, text)
import qualified Tog.Raw                          as C
import           Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..))
import qualified Data.ISet as I

-- * Source locations.
------------------------------------------------------------------------

-- | Source locations (single file only).
data SrcLoc = SrcLoc { pLine :: !Int, pCol :: !Int }
  deriving (Show, Read, Generic, Eq)

instance NFData SrcLoc
instance ToJSON SrcLoc

noSrcLoc :: SrcLoc
noSrcLoc = SrcLoc 0 0

instance Pretty SrcLoc where
  pretty (SrcLoc line col) = text $ concat [show line, ":", show col]

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

instance HasSrcLoc a => HasSrcLoc (Tagged k a) where
  srcLoc = srcLoc . unTagged

instance HasSrcLoc (a :@ SrcLoc) where
  srcLoc = annotation

instance Hashable SrcLoc

instance Semigroup SrcLoc where
  (<>) = max

instance Monoid SrcLoc where
  mempty = noSrcLoc

instance Ord SrcLoc where
  a `compare` b = case pLine a `compare` pLine b of
    EQ -> pCol a `compare` pCol b
    r  -> r 

-- * Concrete names.
------------------------------------------------------------------------

-- | Concrete names coming from input.
data Name = Name { nameLoc :: !(), nameString :: !String }
    deriving (Show, Read, Typeable, Generic)

mkName :: String -> Name
mkName s = Name mempty s

instance IsString Name where
  fromString = mkName

instance Eq Name where
  Name _ x == Name _ y = x == y

instance Ord Name where
  Name _ x `compare` Name _ y = compare x y

instance Hashable Name where
  hashWithSalt s (Name _ x) = hashWithSalt s x

instance NFData Name

instance Semigroup Name where
  Name loc1 str1 <> Name loc2 str2 = Name (loc1 <> loc2) (
    case (str1,str2) of
      ("_",x) -> x
      (x,"_") -> x
      (x,y)   -> x ++ "‡" ++ y)

instance Monoid Name where
  mempty = "_"

-- | A qualified name is a non-empty list of names.  We store them
-- backwards, so that @M.N.f@ will be stored as @'QName' f [N, M]@.
data QName = QName {qNameId :: Id, qNameName :: !Name, qNameModule :: ![Name]}
  deriving (Show, Typeable, Generic)

instance Hashable QName where hashWithSalt s = hashWithSalt s . qNameId
instance NFData QName

instance ISetMember QName where         
  repr = qNameId

qName :: Name -> [Name] -> QName
qName = curry intern

qNameCons :: Name -> QName -> QName
qNameCons n (QName _ n' ns) = qName n (n' : ns)

qNameSingleton :: Name -> QName
qNameSingleton n = qName n []

instance Eq QName where (==) = (==) `on` qNameId
instance Ord QName where compare = compare `on` qNameId

deriving instance Eq (Description QName)
deriving instance Hashable (Description QName)
deriving instance Show (Description QName)
deriving instance Generic (Description QName)

instance Interned QName where
  type Uninterned QName = (Name, [Name])                         
  data Description QName = DQName Name [Name]

  describe = DQName <$> fst <*> snd
  identify = uncurry . QName
  cache = qNameCache

instance Uninternable QName where
  unintern = (,) <$> qNameName <*> qNameModule

{-# NOINLINE qNameCache #-}
qNameCache :: Cache QName
qNameCache = mkCache

------------------------------------------------------------------------
--  HasSrcLoc instances

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.QName where
  srcLoc (C.Qual n _) = srcLoc n
  srcLoc (C.NotQual n) = srcLoc n

instance HasSrcLoc C.Expr where
  srcLoc e = case e of
    C.Lam (x:_) _ -> srcLoc x
    C.Lam [] _    -> error $ "nullary lambda: " ++ show e
    C.Pi tel _    -> srcLoc tel
    C.Fun a _     -> srcLoc a
    C.Eq x _      -> srcLoc x
    C.App (e:_)   -> srcLoc e
    C.App []      -> error "empty application"
    C.Id x        -> srcLoc x

instance HasSrcLoc C.Arg where
  srcLoc (C.Arg e)  = srcLoc e
  srcLoc (C.HArg e) = srcLoc e

instance HasSrcLoc C.Telescope where
  srcLoc (C.Tel (b : _)) = srcLoc b
  srcLoc tel = error $ "empty telescope: " ++ show tel

instance HasSrcLoc C.Binding where
  srcLoc (C.Bind  (x:_) _) = srcLoc x
  srcLoc (C.HBind (x:_) _) = srcLoc x
  srcLoc b = error $ "binding no names: " ++ show b

instance HasSrcLoc C.TypeSig where
  srcLoc (C.Sig x _) = srcLoc x

instance HasSrcLoc C.Decl where
  srcLoc d = case d of
    C.Postulate (d:_)  -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x        -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _     -> srcLoc x
    C.OpenApp x _      -> srcLoc x
    C.Import x         -> srcLoc x
    C.Module_ x        -> srcLoc x
    C.OpenImport x _   -> srcLoc x
    C.ModuleApp x _    -> srcLoc x
    C.Pragma           -> noSrcLoc
    C.Mutual x         -> mconcat$ map srcLoc x

instance HasSrcLoc C.Import where
  srcLoc x = case x of
    C.ImportNoArgs x -> srcLoc x
    C.ImportArgs x _ -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.ConP x _ -> srcLoc x
    C.HideP p  -> srcLoc p
    C.EmptyP x -> srcLoc x

instance HasSrcLoc C.Empty where
  srcLoc (C.Empty ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.Module where
  srcLoc (C.Module x _ _) = srcLoc x

instance HasSrcLoc C.Params where
  srcLoc (C.ParamDecl (x : _)) = srcLoc x
  srcLoc (C.ParamDef (x : _)) = srcLoc x
  srcLoc _ = noSrcLoc

instance HasSrcLoc C.HiddenName where
  srcLoc (C.NotHidden n) = srcLoc n
  srcLoc (C.Hidden n) = srcLoc n

-- Pretty printing
------------------------------------------------------------------------

instance Pretty Name where
  pretty (Name _ x) = text x

instance Pretty QName where
  pretty (QName _ n ns) =
    mconcat $ intersperse "." $ map pretty $ reverse (n : ns)

-- Internal definitions
internal :: Name -> QName
internal s = qNameCons s$ qNameCons "Internal"$ qNameCons "Builtin"$ qNameSingleton "Tog"

