module Tog.Term.Impl.Hashed where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.PhysEq 

import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Prelude
import           Tog.Term.Subst
import           Tog.Unify.Common

type ITerm = Hashed
data Hashed = H Int (TermView Hashed)
  deriving (Typeable, Show, Generic)

instance FreeVars ITerm ITerm where freeVars = fastFreeVars

instance NFData Hashed

instance Hashable Hashed where
  hashWithSalt s (H i _) = s `hashWithSalt` i

instance Eq Hashed where
  H i1 t1 == H i2 t2 = i1 == i2 && t1 == t2

instance Metas Hashed Hashed where
  foldMetas = genericFoldMetas

instance ExpandMetas ITerm ITerm where
  expandMetas = genericExpandMetas

instance Nf Hashed Hashed where
  nf = genericNf

instance PrettyM Hashed Hashed where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst Hashed Hashed where
  safeApplySubst = genericSafeApplySubst
  applySubst = genericApplySubst
  safeStrengthen = genericSafeStrengthen

instance PhysEq Hashed where
  physEq (H i1 x) (H i2 y) = ((i1 == i2) &&) <$> genericPhysEq x y

instance SynEq Hashed Hashed where
  synEq x y = return (x == y)

instance IsTerm Hashed where
  shortName = "H"
  longName  = "Hashed"

  newtype Subst Hashed = HSubst (GenericSubst Hashed) deriving (IsSubst Hashed)

  whnf t = do
    t' <- fromMaybe t <$> liftIO (lookupWhnfTerm t)
    blockedT <- genericWhnf t'
    
    t'' <- ignoreBlocking blockedT
    unless (t == t'') $ liftIO $ do
      
      -- `lookupWhnfTerm'.
      insertWhnfTerm t t''
      insertWhnfTerm t' t''
    return blockedT

  whnfMeta = genericWhnfMeta

  view (H _ t) = return t
  unview tv = return $ H (hash tv) tv

  set = H (hash (Set :: Closed (TermView Hashed))) Set
  refl = H (hash (Refl :: Closed (TermView Hashed))) Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ genericTypeOfJ

-- Table

type TableKey = Hashed

{-# NOINLINE hashedTable #-}
hashedTable :: HT.CuckooHashTable TableKey Hashed
hashedTable = unsafePerformIO HT.new

lookupWhnfTerm :: Hashed -> IO (Maybe Hashed)
lookupWhnfTerm t0 = do
  HT.lookup hashedTable t0

insertWhnfTerm :: Hashed -> Hashed -> IO ()
insertWhnfTerm t1 t2 = HT.insert hashedTable t1 t2

instance Prune ITerm ITerm where

instance KillTwins ITerm ITerm where killTwinsE = fastKillTwinsE
