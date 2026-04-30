module Tog.Unify.Heterogeneous.Core where

import Tog.Prelude
import Tog.Term
import Tog.Names

data Constraint t where
  EqualTerm :: { loc :: SrcLoc
          , ctx :: Ctx_ t
          , lhs :: Type t :∋ Term t
          , rhs :: Type t :∋ Term t
          } -> Constraint t
  -- | Compares two terms in weak head-normal form at a WHNF type
  --   It will not try to instantiate metas
  EqualSpine :: {
      loc    :: SrcLoc
    , ctx    :: Ctx_ t
    , spine  :: Spine t
    } -> Constraint t
  EqualCanonical :: {
         loc :: SrcLoc
       , ctx :: Ctx_ t
       , lhs :: Type t :∋ Term t
       , rhs :: Type t :∋ Term t
       } -> Constraint t
  InstantiateMeta :: {
      loc    :: SrcLoc
    , mv     :: Meta
    , value  :: MetaBody t } -> Constraint t
  Conj :: [Constraint t] -> Constraint t
  (:>>:) :: (Constraint t) -> (Constraint t) -> Constraint t

--deriving instance Generic (Constraint t)
--deriving instance Eq t => Eq (Constraint t)

--instance Hashable t => Hashable (Constraint t)

instance HasSrcLoc (Constraint t) where
  srcLoc EqualTerm{loc} = loc
  srcLoc EqualSpine{loc} = loc
  srcLoc EqualCanonical{loc} = loc
  srcLoc InstantiateMeta{loc} = loc
  srcLoc (Conj cs) = mconcat $ map srcLoc cs
  srcLoc (a :>>: b) = srcLoc a <> srcLoc b

instance Nf t t => Nf t (Constraint t) where
  nf (EqualTerm loc ctx lhs rhs) = EqualTerm <$> pure loc <*> nf ctx <*> nf lhs <*> nf rhs
  nf (EqualSpine loc ctx spine) = EqualSpine <$> pure loc <*> nf ctx <*> nf spine
  nf (EqualCanonical loc ctx lhs rhs) = EqualCanonical <$> pure loc <*> nf ctx <*> nf lhs <*> nf rhs
  nf (InstantiateMeta loc mv value) = InstantiateMeta <$> pure loc <*> pure mv <*> nf value
  nf (Conj cs) = Conj <$> traverse nf cs
  nf (a :>>: b) = (:>>:) <$> nf a <*> nf b

instance Monoid (Constraint t) where
  mempty = Conj []

  Conj cs1 `mappend` Conj cs2 = Conj (cs1 <> cs2)
  Conj cs1 `mappend` c2       = Conj (c2 : cs1)
  c1       `mappend` Conj cs2 = Conj (c1 : cs2)
  c1       `mappend` c2       = Conj [c1, c2]

data AsYouWish (b :: Bool) a where
  No  :: AsYouWish 'False a
  Yes :: { yesIDo :: a } -> AsYouWish 'True a

deriving instance (Functor (AsYouWish b))
deriving instance (Foldable (AsYouWish b))
deriving instance (Traversable (AsYouWish b))

instance Nf t a => Nf t (AsYouWish b a) where
  nf = traverse nf

data Spine t where
  Spine :: { head1  :: AsYouWish b t :∈ Type t
           , head2  :: AsYouWish b t :∈ Type t
           , tail   :: Tail b t
           } -> Spine t

instance Nf t a => Nf t (Spine a) where
  nf (Spine headL headR tail) = Spine <$> nf headL <*> nf headR <*> nf tail

data Tail (needsHead :: Bool) t where
  ENil   :: Tail 'False t

  -- Applications do not need the head
  EApply :: { applyL :: Term t
            , applyR :: Term t
            , restA   :: Tail b t
            } -> Tail b t

  -- Projections do need the head
  EProj  :: { projL :: !(Opened Projection t)
            , projR :: !(Opened Projection t)
            , restNeedsHead :: SBool b -- Should be replaced by an implicit singleton
            , rest :: Tail b t
            } -> Tail 'True t

instance Nf t a => Nf t (Tail b a) where
  -- This is copied from the definition of  Nf t (Elim a)
  nf ENil = pure ENil
  nf (EApply applyL applyR rest) = EApply <$> nf applyL <*> nf applyR <*> nf rest
  nf (EProj p q b s) = EProj p q b <$> nf s

unpackSpine :: Spine t -> (Maybe (Term t, Term t), Type t :∋ Elims (Term t), Type t :∋ Elims (Term t))
unpackSpine (Spine (head1 :∈ ty1)
                   (head2 :∈ ty2)
                   tail) =
  let head = case (head1,head2) of
        (Yes a, Yes b) -> Just (a,b)
        (No   , No   ) -> Nothing

      (tail1, tail2) = unpackTail tail
  in
  (head, tail1 :∈ ty1, tail2 :∈ ty2)

unpackTail :: Tail b t -> (Elims (Term t), Elims (Term t))
unpackTail ENil = ([], [])
unpackTail (EProj p q _ s) | (tail1,tail2) <- unpackTail s  = (Proj p:tail1, Proj q:tail2)
unpackTail (EApply a b s) | (tail1,tail2) <- unpackTail s = (Apply a:tail1, Apply b:tail2)

tailApply :: [(Term t, Term t)] -> Tail 'False t 
tailApply = foldr (uncurry EApply) ENil

tailElim :: [Elim t] -> [Elim t] -> α -> (forall b. SBool b -> Tail b t -> α) → α
tailElim [] [] _ κ = κ SFalse ENil
tailElim (Apply a:as) (Apply b:bs) err κ = tailElim as bs err $ \need tail -> κ need  $ EApply a b tail
tailElim (Proj  p:as) (Proj  q:bs) err κ = tailElim as bs err $ \need tail -> κ STrue $ EProj  p q need tail
tailElim _ _ err _ = err

-- | We do not need to store the ends of the if they are syntactically equal
tailElimTrimmed :: (MonadTerm t m) => [Elim t] -> [Elim t] -> m α -> (forall b. SBool b -> Tail b t -> m α) → m α
tailElimTrimmed [] [] _ κ = κ SFalse ENil
tailElimTrimmed (Apply a:as) (Apply b:bs) err κ = tailElim as bs err $ \need tail -> do
  let κ' = κ need  $ EApply a b tail 
  case tail of
    ENil -> do
      eq <- synEq a b
      if eq then κ SFalse ENil
            else κ'
    _    -> κ'
tailElimTrimmed (Proj  p:as) (Proj  q:bs) err κ = tailElim as bs err $ \need tail -> do
  let κ' = κ STrue $ EProj  p q need tail
  case tail of
    ENil -> do
      eq <- synEq p q
      if eq then κ SFalse ENil 
            else κ'
    _    -> κ'
tailElimTrimmed _ _ err _ = err



instance PrettyM t t => PrettyM t (Tail b t) where
  prettyPrecM p = prettyPrecM p . unpackTail

-- Type level booleans --
-------------------------

data SBool b where
  STrue  :: SBool 'True
  SFalse :: SBool 'False
