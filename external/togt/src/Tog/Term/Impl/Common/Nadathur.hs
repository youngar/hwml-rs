{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | Taken from cite:nadathur2005practical
--   and        cite:gacek2007simplified
module Tog.Term.Impl.Common.Nadathur (
   module Tog.Term.Impl.Common.Nadathur
  ,StableName
  ) where

import Tog.Prelude
import Tog.Term.Core
import Tog.Term.Synonyms
import           Tog.PrettyPrint                  ((<+>), ($$), {- (</>),-} (//>), {- ($$>) -})
import qualified Tog.PrettyPrint                  as PP
import Tog.Instrumentation.Debug                  (fatalError)
import Tog.Term.Subst

import System.IO.Unsafe
import System.Mem.StableName

#include "impossible.h"



data Susp t a = Susp { term :: a
                     , ol   :: {- {-# UNPACK #-} -} !Nat
                       -- ^ How many elements are there in the environment
                     , nl   :: {- {-# UNPACK #-} -} !Nat
                       -- ^ ol + How much to weaken free variables by
                     , env  :: !(Env t)     {- We make it strict for:
                                               - Freeing memory 
                                               - Consistency of the stable name used for hashing
                                                 (it may change upon evaluation)
                                             -}
                     } deriving (Functor, Show, Typeable)

instance Hashable a => Hashable (Susp t a) where
  -- ol is determined by env
  hashWithSalt s Susp{term,ol=0,nl,env=_} = hashWithSalt s (term,nl,ENil)
  hashWithSalt s Susp{term,ol=_,nl,env} = hashWithSalt s (term,nl,env)

instance Eq a => Eq (Susp t a) where
  Susp{term=term1,ol=0,nl=nl1,env=_} ==
    Susp{term=term2,ol=0,nl=nl2,env=_} = (term1,nl1) == (term2,nl2)
  Susp{term=term1,ol=ol1,nl=nl1,env=env1} ==
    Susp{term=term2,ol=ol2,nl=nl2,env=env2} =
        (term1,ol1,nl1,envStableName env1) == (term2,ol2,nl2,envStableName env2)

instance PrettyM t a => PrettyM t (Susp t a) where
  prettyM Susp{term,ol,nl,env} = do
    termDoc <- prettyM term
    envDoc  <- prettyM env
    pure$ "⟦" <+> termDoc <+> "," <+> PP.pretty ol <+> "," <+> PP.pretty nl <+> "," <+> envDoc <+> "⟧"

instance PrettyM t a => PrettyM t (Env a) where
  prettyM (ECons (p,a) e)  = do
      termDoc  <-  prettyM (p, Pretty a)
      envDoc   <-  prettyM e
      return$ termDoc <+> "∷" //> envDoc

  prettyM  ENil = return "nil"

{- Observation 1:   weaken n t             corresponds to  [t, 0, n, ENil]
   Observation 2:   instantiate (Abs t) a  corresponds to  [t, 1, 0, ECons (a,0) ENil]
   Observation 3:   strengthening a weakened value is very fast
                    One could even consider making the weakened version
                    [t, 0, n, ENil] a normal form of a term.
   Observation 4:   closed terms are annotated in Teyjus (see gacek2017simplified)
-}

{-# NOINLINE eNil #-}
eNil :: Env t 
eNil = E Nil 

{-# INLINE idSusp #-}
-- | Monad
idSusp :: a -> Susp t a
idSusp = IdSusp

pattern IdSusp :: a -> Susp t a
pattern IdSusp term <- Susp{term, ol=0, nl=0} 
  where IdSusp term =  Susp{term, ol=0, nl=0, env = eNil}

{-# INLINE joinSusp #-}
joinSusp :: HasSusp t t => Susp t (Susp t a) -> Susp t a 
joinSusp (IdSusp s) = s
joinSusp Susp{term=IdSusp t,ol,nl,env} = Susp{term=t,ol,nl,env}
joinSusp Susp{term = Susp{term, ol=ol1, nl=nl1, env=env1},
                                ol=ol2, nl=nl2, env=env2}  =

         Susp{term, ol=ol', nl=nl', env = envComp EnvComp{env1, nl1, ol2, env2}}
  where
    ol' = ol1 + (ol2 `minus` nl1)
    nl' = nl2 + (nl1 `minus` ol2)
  
{-# INLINE weakenSusp #-}
weakenSusp :: Nat -> Term a -> Susp t a
weakenSusp      n term  = Susp{term, ol=0, nl=n,env=eNil}

{-# INLINE instantiateSusp #-}
instantiateSusp :: Term t -> Abs a -> Susp t a
instantiateSusp b Abs{unAbs} = Susp{term=unAbs, ol=1, nl=0, env=ECons (Just b,0) eNil}

liftSuspN :: (HasVar t) => Nat -> Susp t a -> Susp t a
liftSuspN 0 ς = ς
liftSuspN n ς =
  let Susp{term,ol,nl,env} = liftSuspN (n-1) ς
      nl' = nl+1
      ol' = ol+1
  in
  Susp{term, ol=ol', nl=nl',env=ECons (Just (varP Nothing 0), nl') env}
    
{-# INLINE strengthenSuspN #-}
strengthenSuspN :: Nat -> a -> Susp t a
strengthenSuspN = \n ->
  let env = envStrengthenSuspN !! n in 
  \a -> Susp{term=a, ol=n, nl=0, env}
  where
    envStrengthenSuspN :: [Env t]
    envStrengthenSuspN = iterate (ECons (Nothing, 0)) eNil 

-- p. 34   gacek2007simplified 
{-# INLINE substToSusp #-}
substToSusp :: forall t σ a. (HasSusp t t, IsSubst t σ, IsTerm t) => σ -> Susp t a -> Susp t a
substToSusp σ {- : Δ → Γ -}     t {- : Δ -} = joinSusp $ go σ t
  where
    go :: forall a. σ -> a -> Susp t a
    go σ a =
      case σ of
        Id               ->  idSusp a

        Weaken n σ       ->  joinSusp $ {- Γ;Ψ -} weakenSusp n $ go σ a {- : Γ   -}

        Instantiate b σ  ->  {- joinSusp $ instantiateSusp b . Abs_ $ go σ a -}
                             let Susp{term,ol,nl,env} = go σ a in
                             Susp{term,ol=ol+1,nl,env=E (Cons (Just b, nl) env)}

        Strengthen  n σ  ->  joinSusp $ strengthenSuspN n $ go σ a
         {-
          let Susp{term,ol,nl,env} = go σ {- : ? -} in 
                             Susp{term,ol=ol+n,nl,env= iterateN n (E . Cons (Nothing,nl)) env}
         -}
          
        Lift        n σ  ->  liftSuspN n $ go σ a

                             {-
                             let liftσ k | k == n = Weaken n σ {- wkσ : Γ;Ψσ → Δ -}
                                 liftσ k          = let ρ = (liftσ (k+1)) in              {-  pred : Γ;Ψσ → Δ;Ψ_n…Ψ_k+1   -}
                                                    Instantiate (varP Nothing k) ρ    {-  Γ;Ψσ → Δ;Ψ_n…Ψ_k            -}
                             in
                             substToSusp (liftσ 0) t    {-  Γ;Ψσ → Δ;Ψ_n-1…Ψ₀            -}
                             -}

class HasVar t => HasSusp t a where
  susp      :: Susp t a -> a
  viewSusp  :: a -> Susp t (TermView a)

data EnvView t = Nil
               | Cons {-# UNPACK #-} !(Maybe t, Nat) (Env t)
               deriving (Show)

pattern ENil :: Env t
pattern ENil = E Nil

pattern ECons :: (Maybe t, Nat) -> Env t -> Env t
pattern ECons a b = E (Cons a b)

envToList :: Env t -> [(Maybe t, Nat)]
envToList = \case
  ENil -> []
  ECons a b -> a:envToList b


-- We use Data to avoid strictness
data Env t = E (EnvView t) deriving (Show)

  {-
           | EComp { env1 :: Env t
                   , nl1  :: {-# UNPACK #-} !Nat
                   , ol2  :: {-# UNPACK #-} !Nat
                   , env2 :: Env t
                   }
   -}

data EnvComp t = EnvComp { env1 :: Env t
                         , nl1  :: {- {-# UNPACK #-} !-} Nat
                         , ol2  :: {- {-# UNPACK #-} !-} Nat
                         , env2 :: Env t
                         }

{-# INLINE minus #-}
minus :: Nat -> Nat -> Nat
minus a b | a >= b     = a - b
          | otherwise  = 0

{-# INLINE envView #-}
envView :: Env t -> EnvView t
envView t = case t of
  E ev -> ev

{-# INLINE envComp #-}
envComp :: forall t. HasSusp t t => EnvComp t -> Env t 
envComp
  EnvComp{env1, nl1, ol2, env2} = go env1 nl1 ol2 env2

  where
    go :: Env t -> Nat -> Nat -> Env t -> Env t
    go env1  nl1  ol2   env2  = case (envView env1, nl1, ol2, envView env2) of
      (_,     _, 0, ~Nil) -> env1
      (Nil,   0, _, _   ) -> env2
      (Nil,   _, _, (Cons _ env2)) {- nl1 > 0 -} ->
        let nl1' = nl1 - 1
            ol2' = ol2 - 1
        in
        -- We could decrement in one single go. Perhaps use sequences
        -- instead of list?
        go eNil  nl1'  ol2' env2

      (Cons (_t,n) _, _, _, Cons (_s,_l) env2)  |  nl1 > n ->     -- m5
        let nl1' = nl1 - 1
            ol2' = ol2 - 1
        in
        go env1  nl1'  ol2' env2

      (Cons (t,n) env1, _, _, Cons (_s,l) _)      |  nl1 == n ->   -- m4

        let m = l + (n `minus` ol2) in

        E$ Cons (fmap @Maybe
                   (\term -> susp Susp{ term
                       , ol    =  ol2
                       , nl    =  l
                       , env   =  env2
                       }) t, m) $

              go env1 n ol2 env2

commuteElim :: Susp t (Elim a) -> Elim (Susp t a)
commuteElim Susp{term=Proj  p}               =  Proj  p
commuteElim Susp{term=Apply term,ol,nl,env}  =  Apply Susp{term,ol,nl,env}

commuteAbs :: HasVar t => Susp t (Abs a) -> Abs (Susp t a)
commuteAbs Susp{term=Abs{absName,unAbs=term},nl,ol,env} =
                     Abs{absName,unAbs=
                            Susp{term, nl=nl', ol=ol'
                                ,env = ECons (Just (varP Nothing 0), nl') env}}
                        where
                          nl' = nl+1
                          ol' = ol+1

commuteOpened :: Susp t (Opened k a) -> Opened k (Susp t a)
commuteOpened Susp{nl,ol,env,term} = flip fmap term $ \arg -> Susp{nl,ol,env,term=arg}

envDrop :: Nat -> Env t -> Env t
envDrop 0 env          =  env 
envDrop i env | i > 0  =  let Cons _ env' = envView env in envDrop (i-1) env'

{-
suspLookup :: forall t. (HasSusp t t, IsTerm t) => Susp t (Maybe Dir, Var) -> TermView (Susp t t)
suspLookup Susp{term = (dir, unVar -> i), ol, nl, env} =
  -- Here we use 'ol' without looking at the environment
  if i >= ol then
    view$ varP dir $ i - ol + nl
  else
    let Cons (t,l) _ = envView $ envDrop i env in
    susp @t Susp{term = runIdentity$ view . atDir dir t, ol = 0, nl = nl - l, env = ENil}  
-}


{-# INLINE commuteApp #-}
commuteApp :: (HasSusp t t, IsTerm t) => Susp t (Head t) -> TermView (Susp t t)

commuteApp Susp{ol,nl,env, term=Var (unVar -> i)} =
  if i >= ol then
    App (Var (mkVar "_"$ i - ol + nl)) []
  else
    let Cons (Just t,l) _ = envView $ envDrop i env in
    commute$ joinSusp Susp{term = viewSusp t, ol = 0, nl = nl - l, env = ENil}

commuteApp Susp{ol,nl,env, term=Twin dir (unVar -> i)} =
  if i >= ol then
    App (Twin  dir $ (mkVar "_"$ i - ol + nl)) []
  else
    let Cons (Just t,l) _ = envView $ envDrop i env in
    -- Twin variables should only be substituted by other variables, not terms
    -- They can appear in contexts, but they cannot be bound
    case commute$ viewSusp t of
      App (Var (unVar -> j)) []   ->
        let nl' = nl - l in
        App (Twin dir (mkVar "_"$ j + nl')) []
      _ -> __IMPOSSIBLE__

commuteApp Susp{term=Meta mv}  = App (Meta mv) []

commuteApp Susp{term=J}        = App J []

commuteApp Susp{ol,nl,env, term=Def n}    =
  let n' = commuteOpened Susp{ol,nl,env, term=n} in
    App (Def n') []



commute :: (HasSusp t t, IsTerm t) => Susp t (TermView t) -> TermView (Susp t t)
commute = \case

    Susp{ol,nl,env, term=Con dataCon args} ->
      Con (commuteOpened Susp{term=dataCon,ol,nl,env})
          (fmap (\term -> Susp{term,ol,nl,env}) args)

    Susp{ol,nl,env, term=Lam abs} ->
      Lam$ commuteAbs Susp{term=abs,ol,nl,env}

    Susp{ol,nl,env, term=Pi dom cod} ->

      Pi Susp{term=dom,ol,nl,env} $ commuteAbs Susp{term=cod,ol,nl,env}
    
    Susp{ol,nl,env, term=Equal type_ x y}  ->
      Equal  Susp{term = type_ , ol,nl,env} 
             Susp{term = x     , ol,nl,env} 
             Susp{term = y     , ol,nl,env}

    Susp{term=Refl} -> Refl

    Susp{term=Set}  -> Set

    Susp{ol,nl,env, term=App h els} ->

      let els' = map (commuteElim . (\elim -> Susp{ol,nl,env,term=elim})) els in
      let hT = commuteApp Susp{ol,nl,env,term=h} in
      eliminateSusp hT els'


-- | Tries to apply the eliminators to the term.  Throws an error
-- when the term and the eliminators don't match.
eliminateSusp :: forall t. (HasSusp t t, PrettyM t t, IsTerm t) => TermView (Susp t t) -> [Elim (Susp t t)] -> TermView (Susp t t)
eliminateSusp t elims =
  let badElimination =
        let tDoc      = runUnsafeTermM @t $ prettyM_ @t $ fmap susp t
            elimsDoc  = runUnsafeTermM @t $ prettyM_ @t elims
        in
            error $ PP.render $
              "Bad elimination" $$
              "term:" //> tDoc $$
              "elims:" //> elimsDoc
  in
  case (t, elims) of

    (_, []) -> t

    (Con _c args, Proj proj : es) -> do
        let ix = pField proj
        if unField ix >= length args
          then badElimination
          else eliminateSusp (commute $ joinSusp $ fmap viewSusp $ args !! unField ix) es

    (Lam Abs{unAbs}, Apply argument : es) -> do
        let body = joinSusp$ Susp{env=E (Cons (Just (susp argument),0) ENil), ol=1, nl=0, term = joinSusp$ fmap viewSusp unAbs}
        eliminateSusp (commute body) es

    (App h es1, es2) ->
        App h (es1 ++ es2)

    (_, _) ->
        badElimination


-- Keeping the environment lazy
envStableName :: Env t -> StableName (Env t)
envStableName !e = unsafePerformIO$ makeStableName e

instance Eq (Env t) where (==) = (==) `on` envStableName
instance Hashable (Env t) where hashWithSalt s = hashWithSalt s . hashStableName . envStableName

