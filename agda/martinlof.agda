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
  Pair : {n : ℕ} → Expr n → Expr n → Expr n

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

subsetVar : {n m : ℕ} → Subset n m → Fin m → Fin n
subsetVar (no rest) k = suc (subsetVar rest k)
subsetVar (yes rest) zero = zero
subsetVar (yes rest) (suc k) = suc (subsetVar rest k)

subsetVarRefl : {n : ℕ} → (v : Fin n) → subsetVar (idSubset n) v ≡ v
subsetVarRefl zero = refl
subsetVarRefl (suc n) = cong suc (subsetVarRefl n)

subsetVarTrans : {x y z : ℕ} → (sxy : Subset x y) → (syz : Subset y z) → (v : Fin z) → subsetVar sxy (subsetVar syz v) ≡ subsetVar (transSubset sxy syz) v
subsetVarTrans done done v with v
... | ()
subsetVarTrans (no restxy) syz v = cong suc (subsetVarTrans restxy syz v)
subsetVarTrans (yes restxy) (no restyz) v = cong suc (subsetVarTrans restxy restyz v)
subsetVarTrans (yes restxy) (yes restyz) zero = refl
subsetVarTrans (yes restxy) (yes restyz) (suc v) = cong suc (subsetVarTrans restxy restyz v)

subsetExpr : {n m : ℕ} → Subset n m → Expr m → Expr n
subsetExpr _ U = U
subsetExpr s (Var v) = Var (subsetVar s v)
subsetExpr s (Pi A B) = Pi (subsetExpr s A) (subsetExpr (yes s) B)
subsetExpr s (Sigma A B) = Sigma (subsetExpr s A) (subsetExpr (yes s) B)
subsetExpr s (App A B) = App (subsetExpr s A) (subsetExpr s B)
subsetExpr s (Lambda A) = Lambda (subsetExpr (yes s) A)
subsetExpr s (Pair A B) = Pair (subsetExpr s A) (subsetExpr s B)

subsetExprRefl : {n : ℕ} → (e : Expr n) → subsetExpr (idSubset n) e ≡ e
subsetExprRefl U = refl
subsetExprRefl (Var v) = cong Var (subsetVarRefl v)
subsetExprRefl (Pi A B) = cong₂ Pi (subsetExprRefl A) (subsetExprRefl B)
subsetExprRefl (Sigma A B) = cong₂ Sigma (subsetExprRefl A) (subsetExprRefl B)
subsetExprRefl (App A B) = cong₂ App (subsetExprRefl A) (subsetExprRefl B)
subsetExprRefl (Lambda A) = cong Lambda (subsetExprRefl A)
subsetExprRefl (Pair A B) = cong₂ Pair (subsetExprRefl A) (subsetExprRefl B)

subsetExprTrans : {x y z : ℕ} → (sxy : Subset x y) → (syz : Subset y z) → (e : Expr z) → subsetExpr sxy (subsetExpr syz e) ≡ subsetExpr (transSubset sxy syz) e
subsetExprTrans _ _ U = refl
subsetExprTrans sxy syz (Var v) = cong Var (subsetVarTrans sxy syz v)
subsetExprTrans sxy syz (Pi A B) = cong₂ Pi (subsetExprTrans sxy syz A) (subsetExprTrans (yes sxy) (yes syz) B)
subsetExprTrans sxy syz (Sigma A B) = cong₂ Sigma (subsetExprTrans sxy syz A) (subsetExprTrans (yes sxy) (yes syz) B)
subsetExprTrans sxy syz (App A B) = cong₂ App (subsetExprTrans sxy syz A) (subsetExprTrans sxy syz B)
subsetExprTrans sxy syz (Lambda A) = cong Lambda (subsetExprTrans (yes sxy) (yes syz) A)
subsetExprTrans sxy syz (Pair A B) = cong₂ Pair (subsetExprTrans sxy syz A) (subsetExprTrans sxy syz B)


preCtxIx' : {n : ℕ} → (k : Fin n) → PreCtx n → Expr (finComplement k)
preCtxIx' {n = suc n} zero (_ ⊹ t) = subsetExpr (no (idSubset n)) t
preCtxIx' (suc k) (c ⊹ _) = preCtxIx' k c

preCtxIx : {n : ℕ} → (k : Fin n) → PreCtx n → Expr n
preCtxIx {n = suc n} zero (_ ⊹ t) = subsetExpr (no (idSubset n)) t
preCtxIx {n = suc n} (suc k) (c ⊹ _) = subsetExpr (no (idSubset n)) (preCtxIx k c)

data PreCtxSubset : {n m : ℕ} → Subset n m → PreCtx m → PreCtx n → Type where
  ctx-done : PreCtxSubset done ∅ ∅
  ctx-no : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr n} → PreCtxSubset s c1 c2 → PreCtxSubset (no s) c1 (c2 ⊹ t)
  ctx-yes : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → PreCtxSubset s c1 c2 → PreCtxSubset (yes s) (c1 ⊹ t) (c2 ⊹ subsetExpr s t)

subsetPreCtxRefl : {n : ℕ} → (c : PreCtx n) → PreCtxSubset (idSubset n) c c
subsetPreCtxRefl ∅ = ctx-done
subsetPreCtxRefl {n = suc n} (c ⊹ t) = transport (cong (λ x → PreCtxSubset (yes (idSubset n)) (c ⊹ t) (c ⊹ x)) (subsetExprRefl _)) (ctx-yes (subsetPreCtxRefl c))

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

subsetTy : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} → PreCtxSubset s c1 c2 → Ty c1 → Ty c2


Variable : {n : ℕ} → (c : PreCtx n) → Expr n → Type
Variable {n} c t = Σ (Fin n) (λ k → preCtxIx k c ≡ t)

subsetVariable : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → (cs : PreCtxSubset s c1 c2) → Variable c1 t → Variable c2 (subsetExpr s t)
subsetVariable {n = suc n} {s = no s} {c1 = c1} {c2 = c2 ⊹ t2} {t = t} (ctx-no rest) v =
  let (inner-k , inner-is-t) = subsetVariable rest v
  in (suc inner-k ,
        (subsetExpr (no (idSubset n)) (preCtxIx (fst (subsetVariable rest v)) c2)
        ≡⟨ cong (λ x → subsetExpr _ x) inner-is-t ⟩
        subsetExpr (no (idSubset n)) (subsetExpr s t)
        ≡⟨ {!!} ⟩
        subsetExpr (no s) t
        ∎))

-- data Variable : {n : ℕ} → (c : PreCtx n) → Expr n → Type where
--   vZ : {n : ℕ} {c : PreCtx n} {t : Expr n} → Variable (c ⊹ t) (subsetExpr (no (idSubset n)) t)
--   vS : {n : ℕ} {c : PreCtx n} {t t' : Expr n} → Variable c t → Variable (c ⊹ t') (subsetExpr (no (idSubset n)) t)

-- subsetVariable : {n m : ℕ} {s : Subset n m} {c1 : PreCtx m} {c2 : PreCtx n} {t : Expr m} → (cs : PreCtxSubset s c1 c2) → Variable c1 t → Variable c2 (subsetExpr s t)
-- subsetVariable {n = suc n} {s = s} {c2 = c2 ⊹ t2} {t = t} (ctx-no rest) v =
--   let substInner = subsetVariable rest v in
--   {!vS ?!}
-- subsetVariable {m = m} {c2 = c2 ⊹ t} (ctx-yes rest) vZ = {!!}
-- subsetVariable (ctx-yes rest) (vS v) =
--   let substInner = subsetVariable rest v in
--   {!!}

-- subsetVariable : {n m : ℕ} {s : Subset n m} {c1 : Ctx m} {c2 : Ctx n} {t : Ty c1} → (cs : CtxSubset s c1 c2) → Variable c1 t → Variable c2 (subsetTy cs t)
-- subsetVariable (ctx-no rest) k = {!vS ?!}
-- subsetVariable (ctx-yes rest) vZ = {!!}
-- subsetVar (no rest) k = suc (subsetVar rest k)
-- subsetVar (yes rest) zero = zero
-- subsetVar (yes rest) (suc k) = suc (subsetVar rest k)

-- Uᵗ : {n : ℕ} {c : Ctx n} → Ty c

-- data IsTy where
--   U-is : {n : ℕ} {c : Ctx n} → IsTy c U
--   Var-is : {n : ℕ} {c : Ctx n} → (v : Variable c Uᵗ) → IsTy c (Var (varToFin v))
--   Pi-is : {n : ℕ} {c : Ctx n} {t : Expr n} {t' : Expr (suc n)} → (t-ty : IsTy c t) → IsTy (c ⊹ᶜ (t , t-ty)) t' → IsTy c (Pi t t')
--   Sigma-is : {n : ℕ} {c : Ctx n} {t : Expr n} {t' : Expr (suc n)} → (t-ty : IsTy c t) → IsTy (c ⊹ᶜ (t , t-ty)) t' → IsTy c (Sigma t t')
-- 
-- Uᵗ = (U , U-is)
-- 
-- Piᵗ : {n : ℕ} {c : Ctx n} → (A : Ty c) → Ty (c ⊹ᶜ A) → Ty c
-- Piᵗ (A , A-ty) (B , B-ty) = (Pi A B , Pi-is A-ty B-ty)
-- 
-- Sigmaᵗ : {n : ℕ} {c : Ctx n} → (A : Ty c) → Ty (c ⊹ᶜ A) → Ty c
-- Sigmaᵗ (A , A-ty) (B , B-ty) = (Sigma A B , Sigma-is A-ty B-ty)
-- 
-- subsetTyExpr : {n m : ℕ} {s : Subset n m} {c1 : Ctx m} {c2 : Ctx n} → (cs : CtxSubset s c1 c2) → (t : Ty c1) → fst (subsetTy cs t) ≡ subsetExpr s (fst t)
-- 
-- subsetTy _ (U , _) = Uᵗ
-- subsetTy {s = s} {c1 = c1} {c2 = c2} cs (Pi A B , Pi-is A-ty B-ty) = Piᵗ (subsetTy cs (A , A-ty)) (subsetTy (transport (cong (λ e → PreCtxSubset (yes s) _ (fst c2 ⊹ e)) (sym (subsetTyExpr cs (A , A-ty)))) (ctx-yes cs)) (B , B-ty))
-- subsetTy {s = s} {c1 = c1} {c2 = c2} cs (Sigma A B , Sigma-is A-ty B-ty) = Sigmaᵗ (subsetTy cs (A , A-ty)) (subsetTy (transport (cong (λ e → PreCtxSubset (yes s) _ (fst c2 ⊹ e)) (sym (subsetTyExpr cs (A , A-ty)))) (ctx-yes cs)) (B , B-ty))
-- 
-- subsetTyExpr _ (U , _) = refl
-- subsetTy s (Pi A B , Pi-is A-ty B-ty) = (Pi (subsetExpr s A) (subsetExpr s B) , ?)
-- 
-- weakenTy : {c : Ctx} {t : Ty c} → Ty c → Ty (c ⊹ᶜ t)
-- weakenTy (U , U-is) = (U , U-is)
-- weakenTy (Var k , Var-is v) = {!!}
-- weakenTy (Pi A B , Pi-is (A , _) (B , _)) = {!!}
