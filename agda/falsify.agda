open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin
open import Data.List


data ValueTerm (v : Nat) : Set where
  vvar : Fin v -> ValueTerm v
  vzero : ValueTerm v
  vsuc : ValueTerm v -> ValueTerm v
  vplus : ValueTerm v -> ValueTerm v -> ValueTerm v
  vtimes : ValueTerm v -> ValueTerm v -> ValueTerm v

constValue : {v : Nat} -> Nat -> ValueTerm v
constValue zero = vzero
constValue (suc n) = vsuc (constValue n)

finEq : {v : Nat} → Fin v → Fin v → Bool
finEq Fin.zero Fin.zero = true
finEq (Fin.suc x) (Fin.suc y) = finEq x y
finEq _ _ = false

finPred : {v : Nat} → (x : Fin (Nat.suc v)) → Fin′ x -> Fin v
finPred (suc n) _ = n

mapValue : {v1 v2 : Nat} → (Fin v1 → ValueTerm v2) → ValueTerm v1 → ValueTerm v2
mapValue f (vvar v) = f v
mapValue f vzero = vzero
mapValue f (vsuc x) = vsuc (mapValue f x)
mapValue f (vplus x y) = vplus (mapValue f x) (mapValue f y)
mapValue f (vtimes x y) = vtimes (mapValue f x) (mapValue f y)

incrVar : {v : Nat} -> Fin v → ValueTerm (suc v)
incrVar v = vvar (suc v)

substVar : {v : Nat} -> Fin (Nat.suc v) -> ValueTerm v -> Fin (Nat.suc v) -> ValueTerm v
substVar {v} var val vr with compare vr var
...  | less var' vr' = vvar (inject! vr')
...  | equal _ = val
...  | greater vr' var' = vvar (finPred vr' var')

data PropTerm (v : Nat) : Set where
  pand : PropTerm v -> PropTerm v -> PropTerm v
  por : PropTerm v → PropTerm v → PropTerm v
  pimpl : PropTerm v → PropTerm v → PropTerm v
  pbot : PropTerm v
  peq : ValueTerm v -> ValueTerm v -> PropTerm v
  pexists : PropTerm (Nat.suc v) -> PropTerm v
  pforall : PropTerm (Nat.suc v) -> PropTerm v


mapProp : {v1 v2 : Nat} → (Fin v1 → ValueTerm v2) → PropTerm v1 → PropTerm v2
mapBody : {v1 v2 : Nat} → (Fin v1 → ValueTerm v2) → PropTerm (suc v1) → PropTerm (suc v2)

mapProp f (pand x y) = pand (mapProp f x) (mapProp f y)
mapProp f (por x y) = por (mapProp f x) (mapProp f y)
mapProp f (pimpl x y) = pimpl (mapProp f x) (mapProp f y)
mapProp _ pbot = pbot
mapProp f (peq x y) = peq (mapValue f x) (mapValue f y)
mapProp f (pexists body) = pexists (mapBody f body)
mapProp f (pforall body) = pforall (mapBody f body)

mapBody {v1} {v2} f = mapProp g
  where g : Fin (suc v1) → ValueTerm (suc v2)
        g zero = vvar zero
        g (suc n) = mapValue incrVar (f n)

data Proof {v : Nat} (ctx : List (PropTerm v)) : PropTerm v → Set where
  assm : (i : Fin (length ctx)) → Proof ctx (lookup ctx i)

  andintro : (p1 p2 : PropTerm v) → Proof ctx p1 → Proof ctx p2 → Proof ctx (pand p1 p2)

  andeliml : (p1 p2 : PropTerm v) → Proof ctx (pand p1 p2) → Proof ctx p1
  andelimr : (p1 p2 : PropTerm v) → Proof ctx (pand p1 p2) → Proof ctx p2

  orintrol : (p1 p2 : PropTerm v) → Proof ctx p1 → Proof ctx (por p1 p2)
  orintror : (p1 p2 : PropTerm v) → Proof ctx p2 → Proof ctx (por p1 p2)

  orelim : (p1 p2 p3 : PropTerm v) → Proof (p1 ∷ ctx) p3 → Proof (p2 ∷ ctx) p3 → Proof ctx (por p1 p2) → Proof ctx p3

  implintro : (p1 p2 : PropTerm v) → Proof (p1 ∷ ctx) p2 → Proof ctx (pimpl p1 p2)

  implelim : (p1 p2 : PropTerm v) → Proof ctx (pimpl p1 p2) → Proof ctx p1 → Proof ctx p2

  botelim : (p : PropTerm v) → Proof ctx pbot → Proof ctx p

  witness : (val : ValueTerm v) (p : PropTerm (suc v)) → (n : Nat) -> Proof ctx (mapProp (substVar Fin.zero val) p) → Proof ctx (pexists p)

  opaque : (p : PropTerm (suc v)) → Proof (map (mapProp incrVar) ctx) p → Proof ctx (pforall p)

  eqrefl : (val : ValueTerm v) → Proof ctx (peq val val)

  eqsymm : (val1 val2 : ValueTerm v) → Proof ctx (pimpl (peq val1 val2) (peq val2 val1))

  zneqs : (val : ValueTerm v) → Proof ctx (pimpl (peq vzero (vsuc val)) pbot)

  induct : (pred : PropTerm (suc v)) →
           Proof ctx (mapProp (substVar Fin.zero vzero) pred) →
           Proof ctx (pforall (pimpl pred (mapProp (λ {
               zero → vsuc (vvar zero);
               other → vvar other
             }) pred))) →
           Proof ctx (pforall pred)

  forallelim : (p : PropTerm (suc v)) → (val : ValueTerm v) → Proof ctx (pforall p) → Proof ctx (mapProp (substVar zero val) p)

  existselim : (p : PropTerm (suc v)) (q : PropTerm v) → Proof ctx (pforall (pimpl p (mapProp incrVar q))) → Proof ctx q
