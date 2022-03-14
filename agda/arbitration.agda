{-# OPTIONS --cubical --guardedness #-}
open import Agda.Builtin.Nat
open import Data.Fin
open import Data.Bool.Base
open import Data.List
open import Data.Vec.Base
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Cubical.Core.Everything public




data PrimRec : Nat → Set where
  prconst : (k n : Nat) → PrimRec k
  prsucc : PrimRec 1
  proj : (k : Nat) → (i : Fin k) → PrimRec k
  prcomp : (k m : Nat) → (g : Vec (PrimRec k) m) → PrimRec m → PrimRec k
  prrec : (k : Nat) → PrimRec k → PrimRec (suc (suc k)) → PrimRec (suc k)


evalPR : (k : Nat) → PrimRec k → Vec Nat k → Nat
evalPR _ (prconst _ n) _ = n
evalPR 1 prsucc (x ∷ []) = suc x
evalPR k (proj _ i) xs = Data.Vec.Base.lookup xs i
evalPR k (prcomp _ m g h) xs =
  evalPR m h (mapcall g)
  where mapcall : {n : Nat} → Vec (PrimRec k) n → Vec Nat n
        mapcall [] = []
        mapcall (f ∷ fs) = evalPR k f xs ∷ mapcall fs
evalPR (suc k) (prrec _ g h) (y ∷ xs) = f y
  where f : Nat → Nat
        f 0 = evalPR k g xs
        f (suc n) = evalPR (suc (suc k)) h (n ∷ f n ∷ xs)
  

record TM : Set where
  field
    tminit : Nat -- state
    tmhalts : PrimRec 1 -- state -> zero if not halt; suc n if return n
    tmstep : PrimRec 1  -- state -> state'

open TM

data TMReturns' (tm : TM) : Nat → Nat → Set where
  retfirst : (s r : Nat) →  evalPR 1 (tmhalts tm) (s ∷ []) ≡ suc r → TMReturns' tm s r
  retrest : (s r : Nat) → evalPR 1 (tmhalts tm) (s ∷ []) ≡ 0 → TMReturns' tm (evalPR 1 (tmstep tm) (s ∷ [])) r → TMReturns' tm s r
  
TMReturns : TM → Nat → Set
TMReturns tm = TMReturns' tm (tminit tm)

TMReturnSatisfies : TM → (Nat → Bool) → Set
TMReturnSatisfies tm pred = Σ Nat (λ r → if pred r then TMReturns tm r else ⊥)

arbType : TM → (Nat → Bool) → Set
arbType tm pred = ¬ TMReturnSatisfies tm pred ⊎ ¬ TMReturnSatisfies tm (λ r → not (pred r)) 

