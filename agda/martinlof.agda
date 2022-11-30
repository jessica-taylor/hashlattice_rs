{-# OPTIONS --cubical --guardedness --rewriting #-}

module martinlof where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public
open import Relation.Nullary using (¬_)
open import Cubical.Data.Sigma

-- Semi : Semilattice
--   if A : Semi, a₁, a₂, a₂ : A
--   then we have _∨_ : A → A → A, ⊥ : A
--   such that a₁ ∨ a₂ = a₂ ∨ a₁
--   and (a₁ ∨ a₂) ∨ a₃ = a₁ ∨ (a₂ ∨ a₃)
--   and a₁ ∨ a₁ = a₁
--   and a₁ ∨ ⊥ = a₁
--   we define a₁ ≤ a₂ ⇔ a₁ ∨ a₂ = a₂
-- let A, B : Semi
--
-- A →ˢ B : Semilattice morphism
--   if a₁, a₂ : A, f : A →ˢ B
--   then f(a₁ ∨ a₂) = f(a₁) ∨ f(a₂)
--   and f(⊥) = ⊥
--   this forms a semilattice
--     in that, if g : A →ˢ B, then (f ∨ g)(a₁) = f a₁ ∨ g a₁
--
-- A →ᵈ Semi : Dependent semilattice
--   if d : A →ᵈ Semi,
--   then we have tr : (a₁ : A) → (a₂ : A) → {a₁ ≤ a₂} → (b : d a₁) → d a₂
--   and dmor : (a₁ : A) → (a₂ : A) → {a₁ ≤ a₂} → d a₁ →ˢ d a₂
--   such that if a₁, a₂, a₃ : A, a₁ ≤ a₂, a₂ ≤ a₃, b : d(a₁)
--   then tr a₁ a₁ = id
--   and tr a₂ a₃ (tr a₁ a₂ b₁) = tr a₁ a₃ b₁
-- let C : A →ᵈ Semi
--
-- Semi →ᵉ Semi : Semilattice endofunctor
--   if e : Semi →ᵉ Semi,
--   then we have map : (A B : Semi) → (A →ˢ B) → e A →ˢ e B
--   such that if A, B, C: Semi, ab : A →ˢ B, bc : B →ˢ C
--   then map A A idˢ = idˢ
--   and map B C bc (map A B ab) = bc ∘ˢ ab
-- let E : Semi →ᵉ Semi
--
-- gen E : Generic semilattice value
--   if g : gen E, represented by a function (A : Semi) → E A,
--   then we have tr : (A B : Semi) → (A →ˢ B) → g A → g B
--   such that if A, B, C : Semi, ab : A →ˢ B, bc : A →ˢ C,
--   then tr A A id = id
--   and tr B C ∘ tr A B = tr A C
--   this forms a semilattice
--     in that, if h : gen E, then (g ∨ h)(A) = g A ∨ h A
--  
--
-- tot (C : A →ᵈ Semi) : Total space (also a semilattice)
--   if t : tot C,
--   then we have π₁ : A
--   and π₂ : C π₁
--
-- mor (C : A →ᵈ Semi) : Dependent semilattice morphism
--   if f : mor C, represented by a function (a : A) → C a,
--     a₁, a₂ : A, b₁ : C a₁, b₂ : C a₂
--   then f(a₁ ∨ a₂) = tr a₁ (a₁ ∨ a₂) b₁ ∨ tr a₂ (a₁ ∨ a₂) b₂
--   and f(⊥) = ⊥
--   this forms a semilattice
--     in that, if g : mor D, then (f ∨ g)(a₁) = f(a₁) ∨ g(a₁)
--
-- can we generalize???
-- consider a function to some type
-- if f : B → tot C, we can split it into f₁ : B → A, f₂ : B → (a : A) → C a
-- if we continue splitting like this, we get a list of functions each of whose return value
-- is either Semi or some specific semilattice (which may depend on previous arguments)
-- the basic rule is:
--   if the last is some specific semilattice: we're making a dependent semilattice morphism
--     in this case, we care about the dependency of the joins of the result on the joins of the previous arguments that have joins
--   if the last is Semi: we're making a dependent semilattice / endofunctor combination
--     in this case, we don't care about joins of arguments, we consider the arguments as categories
--
-- hmm...can we collapse this somehow?
--  note that dependent semilattices are like generic semilattice morphisms
--  we only need the category structure, we can drop the semilattice structure, of the argument
--  

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- path-eq : {f : I → Type} → x ≡ y → PathP f x y

data PreCtx : ℕ → Type
data Expr : ℕ → Type

data PreCtx where
  ∅ : PreCtx zero
  _⊹_ : {n : ℕ} → (c : PreCtx n) → Expr n → PreCtx (suc n)

data Expr where
  U : {n : ℕ} → Expr n
  Var : {n : ℕ} → Fin n → Expr n
  Pi : {n : ℕ} → Expr n → Expr (suc n) → Expr n
  Sigma : {n : ℕ} → Expr n → Expr (suc n) → Expr n
  App : {n : ℕ} → Expr n → Expr n → Expr n
  Lambda : {n : ℕ} → Expr (suc n) → Expr n
  Pair : {n : ℕ} → Expr n → Expr (suc n) → Expr n
  MatchPair : {n : ℕ} → Expr n → Expr (suc (suc n)) → Expr n

-- preCtxTrunc : (c : PreCtx) → Fin (suc (preCtxLen c)) → PreCtx
-- preCtxTrunc c zero = c
-- preCtxTrunc (c ⊹ _) (suc n) = preCtxTrunc c n

finComplement : {n : ℕ} → Fin n → ℕ
finComplement {n = n} zero = n
finComplement {n = suc n} (suc k) = finComplement k

data Vec (A : Type) : ℕ → Type where
  ! : Vec A 0
  _⊕_ : {n : ℕ} → Vec A n → A → Vec A (suc n)

ix : {A : Type} {n : ℕ} → Vec A n → Fin n → A
ix (σ ⊕ t) zero = t
ix (σ ⊕ t) (suc n) = ix σ n

mapVec : {A B : Type} {n : ℕ} → (A → B) → Vec A n → Vec B n
mapVec _ ! = !
mapVec f (σ ⊕ t) = mapVec f σ ⊕ f t

data Subset : ℕ → ℕ → Type where
  done : Subset 0 0
  no : {n m : ℕ} → Subset n m → Subset (suc n) m
  yes : {n m : ℕ} → Subset n m → Subset (suc n) (suc m)

idSubset : (n : ℕ) → Subset n n
idSubset zero = done
idSubset (suc n) = yes (idSubset n)

transSubset : {x y z : ℕ} → Subset x y → Subset y z → Subset x z
transSubset done done = done
transSubset (no rest) s = no (transSubset rest s)
transSubset (yes r1) (no r2) = no (transSubset r1 r2)
transSubset (yes r1) (yes r2) = yes (transSubset r1 r2)

idTransSubset : {n m : ℕ} → (s : Subset n m) → transSubset (idSubset n) s ≡ s
idTransSubset done = refl
idTransSubset (no rest) = cong no (idTransSubset rest)
idTransSubset (yes rest) = cong yes (idTransSubset rest)

transIdSubset : {n m : ℕ} → (s : Subset n m) → transSubset s (idSubset m) ≡ s
transIdSubset done = refl
transIdSubset (no rest) = cong no (transIdSubset rest)
transIdSubset (yes rest) = cong yes (transIdSubset rest)

weakenVar : {n m : ℕ} → Subset n m → Fin m → Fin n
weakenVar (no rest) k = suc (weakenVar rest k)
weakenVar (yes rest) zero = zero
weakenVar (yes rest) (suc k) = suc (weakenVar rest k)

weakenVarId : {n : ℕ} → (v : Fin n) → weakenVar (idSubset n) v ≡ v
weakenVarId zero = refl
weakenVarId (suc n) = cong suc (weakenVarId n)

weakenVarTrans : {x y z : ℕ} → (sxy : Subset x y) → (syz : Subset y z) → (v : Fin z) → weakenVar sxy (weakenVar syz v) ≡ weakenVar (transSubset sxy syz) v
weakenVarTrans done done v with v
... | ()
weakenVarTrans (no restxy) syz v = cong suc (weakenVarTrans restxy syz v)
weakenVarTrans (yes restxy) (no restyz) v = cong suc (weakenVarTrans restxy restyz v)
weakenVarTrans (yes restxy) (yes restyz) zero = refl
weakenVarTrans (yes restxy) (yes restyz) (suc v) = cong suc (weakenVarTrans restxy restyz v)

weakenExpr : {n m : ℕ} → Subset n m → Expr m → Expr n
weakenExpr _ U = U
weakenExpr s (Var v) = Var (weakenVar s v)
weakenExpr s (Pi A B) = Pi (weakenExpr s A) (weakenExpr (yes s) B)
weakenExpr s (Sigma A B) = Sigma (weakenExpr s A) (weakenExpr (yes s) B)
weakenExpr s (App f x) = App (weakenExpr s f) (weakenExpr s x)
weakenExpr s (Lambda body) = Lambda (weakenExpr (yes s) body)
weakenExpr s (Pair fst snd) = Pair (weakenExpr s fst) (weakenExpr (yes s) snd)
weakenExpr s (MatchPair pair body) = MatchPair (weakenExpr s pair) (weakenExpr (yes (yes s)) body)

weakenExprId : {n : ℕ} → (e : Expr n) → weakenExpr (idSubset n) e ≡ e
weakenExprId U = refl
weakenExprId (Var v) = cong Var (weakenVarId v)
weakenExprId (Pi A B) = cong₂ Pi (weakenExprId A) (weakenExprId B)
weakenExprId (Sigma A B) = cong₂ Sigma (weakenExprId A) (weakenExprId B)
weakenExprId (App f x) = cong₂ App (weakenExprId f) (weakenExprId x)
weakenExprId (Lambda body) = cong Lambda (weakenExprId body)
weakenExprId (Pair fst snd) = cong₂ Pair (weakenExprId fst) (weakenExprId snd)
weakenExprId (MatchPair pair body) = cong₂ MatchPair (weakenExprId pair) (weakenExprId body)

weakenExprTrans : {x y z : ℕ} → (sxy : Subset x y) → (syz : Subset y z) → (e : Expr z) → weakenExpr sxy (weakenExpr syz e) ≡ weakenExpr (transSubset sxy syz) e
weakenExprTrans _ _ U = refl
weakenExprTrans sxy syz (Var v) = cong Var (weakenVarTrans sxy syz v)
weakenExprTrans sxy syz (Pi A B) = cong₂ Pi (weakenExprTrans sxy syz A) (weakenExprTrans (yes sxy) (yes syz) B)
weakenExprTrans sxy syz (Sigma A B) = cong₂ Sigma (weakenExprTrans sxy syz A) (weakenExprTrans (yes sxy) (yes syz) B)
weakenExprTrans sxy syz (App f x) = cong₂ App (weakenExprTrans sxy syz f) (weakenExprTrans sxy syz x)
weakenExprTrans sxy syz (Lambda body) = cong Lambda (weakenExprTrans (yes sxy) (yes syz) body)
weakenExprTrans sxy syz (Pair fst snd) = cong₂ Pair (weakenExprTrans sxy syz fst) (weakenExprTrans (yes sxy) (yes syz) snd)
weakenExprTrans sxy syz (MatchPair pair body) = cong₂ MatchPair (weakenExprTrans sxy syz pair) (weakenExprTrans (yes (yes sxy)) (yes (yes syz)) body)

preCtxIx' : {n : ℕ} → (k : Fin n) → PreCtx n → Expr (finComplement k)
preCtxIx' {n = suc n} zero (_ ⊹ t) = weakenExpr (no (idSubset n)) t
preCtxIx' (suc k) (c ⊹ _) = preCtxIx' k c

preCtxIx : {n : ℕ} → (k : Fin n) → PreCtx n → Expr n
preCtxIx {n = suc n} zero (_ ⊹ t) = weakenExpr (no (idSubset n)) t
preCtxIx {n = suc n} (suc k) (c ⊹ _) = weakenExpr (no (idSubset n)) (preCtxIx k c)

data PreCtxSubset : {n m : ℕ} → Subset n m → PreCtx m → PreCtx n → Type where
  ctx-done : PreCtxSubset done ∅ ∅
  ctx-no : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr n} → PreCtxSubset s c1 c2 → PreCtxSubset (no s) c1 (c2 ⊹ t)
  ctx-yes : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → PreCtxSubset s c1 c2 → PreCtxSubset (yes s) (c1 ⊹ t) (c2 ⊹ weakenExpr s t)

subsetPreCtxId : {n : ℕ} → (c : PreCtx n) → PreCtxSubset (idSubset n) c c
subsetPreCtxId ∅ = ctx-done
subsetPreCtxId {n = suc n} (c ⊹ t) = transport (cong (λ x → PreCtxSubset (yes (idSubset n)) (c ⊹ t) (c ⊹ x)) (weakenExprId _)) (ctx-yes (subsetPreCtxId c))

weakenPreCtxIx : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} → PreCtxSubset s c1 c2 → (v : Fin m) → preCtxIx (weakenVar s v) c2 ≡ weakenExpr s (preCtxIx v c1)
weakenPreCtxIx {n = suc n} {s = no s} {c1 = c1} {c2 = c2 ⊹ t2} (ctx-no rest) v =
  let inner = weakenPreCtxIx rest v in
  weakenExpr (no (idSubset n)) (preCtxIx (weakenVar s v) c2)
  ≡⟨ cong (λ x → weakenExpr _ x) inner ⟩ 
  weakenExpr (no (idSubset n)) (weakenExpr s (preCtxIx v c1))
  ≡⟨ weakenExprTrans _ _ _ ⟩
  weakenExpr (no (transSubset (idSubset n) s)) (preCtxIx v c1)
  ≡⟨ cong (λ x → weakenExpr (no x) _) (idTransSubset _) ⟩
  weakenExpr (no s) (preCtxIx v c1) ∎

weakenPreCtxIx {n = suc n} {m = suc m} {s = yes s} {c1 = c1 ⊹ e1} (ctx-yes _) zero =
  weakenExpr (no (idSubset n)) (weakenExpr s e1)
  ≡⟨ weakenExprTrans _ _ _ ⟩
  weakenExpr (no (transSubset (idSubset n) s)) e1
  ≡⟨ cong (λ x → weakenExpr (no x) _) (idTransSubset _) ⟩
  weakenExpr (no s) e1
  ≡⟨ cong (λ x → weakenExpr (no x) e1) (sym (transIdSubset _)) ⟩
  weakenExpr (no (transSubset s (idSubset m))) e1
  ≡⟨ sym (weakenExprTrans _ _ _) ⟩
  weakenExpr (yes s) (weakenExpr (no (idSubset m)) e1)
  ∎

weakenPreCtxIx {n = suc n} {m = suc m} {s = yes s} {c1 = c1 ⊹ _} {c2 = c2 ⊹ _} (ctx-yes rest) (suc v) =
  let inner = weakenPreCtxIx rest v in
  weakenExpr (no (idSubset n)) (preCtxIx (weakenVar s v) c2)
  ≡⟨ cong (λ x → weakenExpr _ x) inner ⟩
  weakenExpr (no (idSubset n)) (weakenExpr s (preCtxIx v c1))
  ≡⟨ weakenExprTrans _ _ _ ⟩
  weakenExpr (no (transSubset (idSubset n) s)) (preCtxIx v c1)
  ≡⟨ cong (λ x → weakenExpr (no x) _) (idTransSubset _) ⟩
  weakenExpr (no s) (preCtxIx v c1)
  ≡⟨ cong (λ x → weakenExpr (no x) _) (sym (transIdSubset _)) ⟩
  weakenExpr (no (transSubset s (idSubset m))) (preCtxIx v c1)
  ≡⟨ sym (weakenExprTrans _ _ _) ⟩
  weakenExpr (yes s) (weakenExpr (no (idSubset m)) (preCtxIx v c1))
  ∎

data IsCtx : {n : ℕ} → PreCtx n → Type

Ctx : ℕ → Type
Ctx n = Σ (PreCtx n) IsCtx


data IsTy : {n : ℕ} → (c : PreCtx n) → Expr n → Type

Ty : {n : ℕ} → PreCtx n → Type
Ty {n} c = Σ (Expr n) (IsTy c)


data IsCtx where
  ∅-is : IsCtx ∅
  ⊹-is : {n : ℕ} {t : Expr n} → (c : Ctx n) → IsTy (fst c) t → IsCtx (fst c ⊹ t)

∅ᶜ : Ctx 0
∅ᶜ = (∅ , ∅-is)

_⊹ᶜ_ : {n : ℕ} → (c : Ctx n) → (t : Ty (fst c)) → Ctx (suc n)
c ⊹ᶜ t = (fst c ⊹ fst t , ⊹-is c (snd t)) 

CtxSubset : {n m : ℕ} → Subset n m → Ctx m → Ctx n → Type
CtxSubset s (c1 , _) (c2 , _) = PreCtxSubset s c1 c2


IsVariable : {n : ℕ} → (c : PreCtx n) → Expr n → Fin n → Type
IsVariable c t k = preCtxIx k c ≡ t

Variable : {n : ℕ} → (c : PreCtx n) → Expr n → Type
Variable {n} c t = Σ (Fin n) (IsVariable c t)

weakenIsVariable : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → (cs : PreCtxSubset s c1 c2) → (v : Variable c1 t) → IsVariable c2 (weakenExpr s t) (weakenVar s (fst v))
weakenIsVariable {s = s} {c1 = c1} {c2 = c2} {t = t} cs (v , v-is) =
  preCtxIx (weakenVar s v) c2
  ≡⟨ weakenPreCtxIx cs v ⟩
  weakenExpr s (preCtxIx v c1)
  ≡⟨ cong (weakenExpr s) v-is ⟩
  weakenExpr s t
  ∎

weakenVariable : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → (cs : PreCtxSubset s c1 c2) → Variable c1 t → Variable c2 (weakenExpr s t)
weakenVariable {s = s} cs v = (weakenVar s (fst v) , weakenIsVariable cs v)

-- data IsTy : {n : ℕ} → (c : PreCtx n) → Expr n → Type
data IsTy where
  U-ty : {n : ℕ} {c : PreCtx n} → IsTy c U
  Var-ty : {n : ℕ} {c : PreCtx n} → (v : Variable c U) → IsTy c (Var (fst v))
  Pi-ty : {n : ℕ} {c : PreCtx n} {A : Expr n} {B : Expr (suc n)} → IsTy c A → IsTy (c ⊹ A) B → IsTy c (Pi A B)
  Sigma-ty : {n : ℕ} {c : PreCtx n} {A : Expr n} {B : Expr (suc n)} → IsTy c A → IsTy (c ⊹ A) B → IsTy c (Sigma A B)

weakenIsTy : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → PreCtxSubset s c1 c2 → IsTy c1 t → IsTy c2 (weakenExpr s t)
weakenIsTy cs U-ty = U-ty
weakenIsTy cs (Var-ty v) = Var-ty (weakenVariable cs v)
weakenIsTy cs (Pi-ty A-ty B-ty) = Pi-ty (weakenIsTy cs A-ty) (weakenIsTy (ctx-yes cs) B-ty)
weakenIsTy cs (Sigma-ty A-ty B-ty) = Sigma-ty (weakenIsTy cs A-ty) (weakenIsTy (ctx-yes cs) B-ty)

weakenTy : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} → PreCtxSubset s c1 c2 → Ty c1 → Ty c2
weakenTy {s = s} cs (t , t-ty) = (weakenExpr s t , weakenIsTy cs t-ty)

data Subst : {n m : ℕ} → Subset n m → PreCtx m → PreCtx n → Type where
  done-subst : Subst done ∅ ∅
  no-subst : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {e2 : Expr n} → Subst s c1 c2 → Expr n → Subst (no s) c1 (c2 ⊹ e2)
  yes-subst : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {e1 : Expr m} {e2 : Expr n} → Subst s c1 c2 → Subst (yes s) (c1 ⊹ e1) (c2 ⊹ e2)
  -- TODO in yes check e1 e2 relation??


-- substVar : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} → Subst s c1 c2 → Fin m → Expr n
-- substVar done-subst v with v
-- ... | ()
-- substVar {n = suc n} (no-subst rest e) zero = weakenExpr (no (idSubset n)) e
-- substVar (no-subst rest _) (suc v) = substVar rest v
-- substVar (yes-subst rest) zero = Var zero
-- substVar {m = suc m} (yes-subst rest) (suc v) = weakenExpr (no (idSubset m)) (substVar rest v)

--substExpr : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} → Subst s c1 c2 → Expr 

data HasType : {n : ℕ} → (c : PreCtx n) → Expr n → Expr n → Type where
  Var-has : {n : ℕ} {c : PreCtx n} {t : Expr n} → (v : Variable c t) → HasType c (Var (fst v)) t
  Lambda-has : {n : ℕ} {c : PreCtx n} {A : Expr n} {B : Expr (suc n)} {body : Expr (suc n)} →
    HasType (c ⊹ A) body B → HasType c (Lambda body) (Pi A B)
  -- App-has : {n : ℕ} {c : PreCtx n} {A C : Expr n} {B : Expr (suc n)} {f x : Expr n} →
  --   HasType c f (Pi A B) → HasType c x A → HasType c (App f x) ???
  Pair-has : {n : ℕ} {c : PreCtx n} {A : Expr n} {B : Expr (suc n)} {fst : Expr n} {snd : Expr (suc n)} →
    HasType c fst A → HasType (c ⊹ A) snd B → HasType c (Pair fst snd) (Sigma A B)
  MatchPair-has : {n : ℕ} {c : PreCtx n} {A C : Expr n} {B : Expr (suc n)} {pair : Expr n} {body : Expr (suc (suc n))} →
    HasType c pair (Sigma A B) → HasType ((c ⊹ A) ⊹ B) body (weakenExpr (no (no (idSubset n))) C) → HasType c (MatchPair pair body) C
      
weakenHasType : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {T e : Expr m} → PreCtxSubset s c1 c2 → HasType c1 e T → HasType c2 (weakenExpr s e) (weakenExpr s T)
weakenHasType cs (Var-has v) = Var-has (weakenVariable cs v)
weakenHasType cs (Lambda-has body-ty) = Lambda-has (weakenHasType (ctx-yes cs) body-ty)
weakenHasType cs (Pair-has fst-ty snd-ty) = Pair-has (weakenHasType cs fst-ty) (weakenHasType (ctx-yes cs) snd-ty)
weakenHasType {n = n} {m = m} {s = s} {T = T} cs (MatchPair-has pair-ty body-ty) =
  let inner = weakenHasType (ctx-yes (ctx-yes cs)) body-ty
      double-weaken =
        weakenExpr (yes (yes s)) (weakenExpr (no (no (idSubset m))) T)
        ≡⟨ weakenExprTrans _ _ _ ⟩
        weakenExpr (transSubset (yes (yes s)) (no (no (idSubset m)))) T
        ≡⟨ cong (λ x → weakenExpr x T) (transIdSubset _) ⟩
        weakenExpr (no (no s)) T
        ≡⟨ cong (λ x → weakenExpr (no (no x)) T) (sym (idTransSubset _)) ⟩
        weakenExpr (no (no (transSubset (idSubset n) s))) T
        ≡⟨ sym (weakenExprTrans _ _ _) ⟩
        weakenExpr (no (no (idSubset n))) (weakenExpr s T)
        ∎
  in MatchPair-has (weakenHasType cs pair-ty) {!!}
-- 
-- Uᵗ = (U , U-is)
-- 
-- Piᵗ : {n : ℕ} {c : Ctx n} → (A : Ty c) → Ty (c ⊹ᶜ A) → Ty c
-- Piᵗ (A , A-ty) (B , B-ty) = (Pi A B , Pi-is A-ty B-ty)
-- 
-- Sigmaᵗ : {n : ℕ} {c : Ctx n} → (A : Ty c) → Ty (c ⊹ᶜ A) → Ty c
-- Sigmaᵗ (A , A-ty) (B , B-ty) = (Sigma A B , Sigma-is A-ty B-ty)
-- 
