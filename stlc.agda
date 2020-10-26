open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : (Γ : Ctx) → Set where
  same : ∀{Γ T} → InCtx (Γ , T)
  next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)


Tat : ∀{Γ} → InCtx Γ → Type
Tat (same {Γ} {T}) = T
Tat (next icx) = Tat icx

Γat : ∀{Γ} → InCtx Γ → Ctx
Γat (same {Γ} {T}) = Γ
Γat (next icx) = Γat icx

data Exp : Ctx → Type → Set where
  var : ∀{Γ} → (icx : InCtx Γ) → Exp Γ (Tat icx)
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  z : ∀{Γ} → Exp Γ Nat
  s : ∀{Γ} → Exp Γ (Nat ⇒ Nat)

subCtx : ∀{Γ} → (icx : InCtx Γ) → Ctx
subCtx (same {Γ}) =  Γ
subCtx (next {Γ} {T} icx) = subCtx icx , T

data Pre : Ctx → Set where
  same : ∀{Γ} → Pre Γ
  next : ∀{Γ T} → Pre Γ → Pre (Γ , T)

toCtx : ∀{Γ} → Pre Γ → Ctx
toCtx (same {Γ}) = Γ
toCtx (next pre) = toCtx pre

weakenΓ : ∀{Γ} → Pre Γ → Type → Ctx
weakenΓ (same {Γ}) A = Γ , A
weakenΓ (next {Γ} {T} pre) A = (weakenΓ pre A) , T

weakenICX : ∀{Γ} → (pre : Pre Γ) → (W : Type)
  → (icx : InCtx Γ) → Σ (InCtx (weakenΓ pre W)) (λ icx' → Tat icx' ≡ Tat icx)
weakenICX same W icx = next icx , refl
weakenICX (next pre) W same = same , refl
weakenICX (next pre) W (next icx) with weakenICX pre W icx
...                               | (i , p) = (next i , p)

weaken : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → Exp Γ T → Exp (weakenΓ pre W) T
weaken pre W (var icx) with weakenICX pre W icx
...                    | (i , p) = subst (λ T → Exp _ T) p (var i)
weaken pre W (lambda e) = lambda (weaken (next pre) W e)
weaken pre W (app e₁ e₂) = app (weaken pre W e₁) (weaken pre W e₂)
weaken pre W z = z
weaken pre W s = s

-- weakenMany : ∀{Γ T} → (pre : Pre Γ)
--   → Exp (toCtx pre) T → Exp Γ T
-- weakenMany same e = e
-- weakenMany (next {_} {T} pre) e = weaken same T (weakenMany pre e)
--
-- weakenMany' : ∀{Γ T} → (icx : InCtx Γ)
--    → Exp (Γat icx) T → Exp Γ T
-- weakenMany' (same {_} {T}) e = weaken same T e
-- weakenMany' (next {_} {T} icx) e = weaken same T (weakenMany' icx e)
--

weakenMany : ∀{Γ T} → (icx : InCtx Γ)
  → Exp (Γat icx) T → Exp (subCtx icx) T
weakenMany same e = e
weakenMany (next {_} {T} icx) e = weaken same T (weakenMany icx e)

-- -- left means use toSub, right means just adjust x for new context.
varSub : ∀{Γ} → (icx : InCtx Γ) → (toSub : Exp (Γat icx) (Tat icx))
  → (x : InCtx Γ) → (Tat icx ≡ Tat x) ⊎ (Σ (InCtx (subCtx icx)) (λ i → Tat i ≡ Tat x))
varSub same toSub same = inj₁ refl
varSub same toSub (next x) = inj₂ (x , refl)
varSub (next icx) toSub same = inj₂ (same , refl)
varSub (next icx) toSub (next x) with varSub icx toSub x
...                              | inj₁ p = inj₁ p
...                              | inj₂ (i , p) = inj₂ (next i , p)

-- alternatively to varSub, could put the cases in sub and use weaken on last case.
sub : ∀{Γ T} → (icx : InCtx Γ) → (toSub : Exp (Γat icx) (Tat icx))
  → Exp Γ T →  Exp (subCtx icx) T
sub icx toSub (var x) with varSub icx toSub x -- var {!   !}
...                   | inj₁ p = subst (λ T → Exp _ T) p (weakenMany icx toSub)
...                   | inj₂ (i , p) = subst (λ T → Exp _ T) p (var i)
-- sub same toSub (var same) = toSub
-- sub same toSub (var (next x)) = var x
-- sub (next icx) toSub (var same) = var same
-- sub (next icx) toSub (var (next x)) with sub icx toSub (var x)
-- ...                                 | e = weaken same _ e
sub icx toSub (app e₁ e₂) = app (sub icx toSub e₁) (sub icx toSub e₂)
sub icx toSub (lambda e) = lambda (sub (next icx) toSub e)
sub icx toSub z = z
sub icx toSub s = s


data V : Ctx → Type → Set
data U : Ctx → Type → Set

data V where
  lambda : ∀{Γ A B} → V (Γ , A) B → V Γ (A ⇒ B)
  fromU : ∀{Γ T} → U Γ T → V Γ T

data U where
  var : ∀{Γ} → (icx : InCtx Γ) → U Γ (Tat icx)
  z : ∀{Γ} → U Γ Nat
  s : ∀{Γ} → U Γ (Nat ⇒ Nat)
  app : ∀{Γ A B} → U Γ (A ⇒ B) → V Γ A → U Γ B

-- indExp : ∀{Γ T} → (P : ∀{Γ T} → Exp Γ T → Set)
--   → (∀{Γ} → (icx : InCtx Γ) → P (var icx))
--   → (∀{Γ A B} → (e : Exp (Γ , A) B) → P (lambda e))
--   → (∀{Γ} → P (s {Γ}))
--   → (∀{Γ} → P (z {Γ}))
--   → (∀{Γ A B} → (e₁ : Exp Γ (A ⇒ B)) → (e₂ : Exp Γ A) → P (app e₁ e₂))
--   → ∀ {Γ T} → (e : Exp Γ T) → P e
-- indExp P Pvar Plam Ps Pz Papp (var icx) = Pvar icx
-- indExp P Pvar Plam Ps Pz Papp (lambda e) = Plam e
-- indExp P Pvar Plam Ps Pz Papp (app e₁ e₂) = Papp e₁ e₂
-- indExp P Pvar Plam Ps Pz Papp z = Pz
-- indExp P Pvar Plam Ps Pz Papp s = Ps

recExp : ∀{Γ T} → Exp Γ T → (P : Set)
  → ((icx : InCtx Γ) → (Tat icx ≡ T) → P) -- var
  → ((A B : Type) → (T ≡ A ⇒ B) → (e : Exp (Γ , A) B) → P) -- lambda
  → ((Nat ⇒ Nat ≡ T) → P) -- s
  → ((Nat ≡ T) → P) -- z
  → (∀(A) → (e₁ : Exp Γ (A ⇒ T)) → (e₂ : Exp Γ A) → P) -- app
  → P
recExp (var icx) P Pv Pl Ps Pz Pa = Pv icx refl
recExp {Γ} {A ⇒ B} (lambda e) P Pv Pl Ps Pz Pa = Pl A B refl e
recExp (app e e₁) P Pv Pl Ps Pz Pa = Pa _ e e₁
recExp z P Pv Pl Ps Pz Pa = Pz refl
recExp s P Pv Pl Ps Pz Pa = Ps refl

lemma1 : ∀{Γ A B T₁ T₂} → (T₁ ⇒ T₂ ≡ A ⇒ B) → Exp (Γ , A) B → Exp (Γ , T₁) T₂
lemma1 refl e = e
lemma1' : ∀{Γ A B T₁ T₂} → (A ⇒ B ≡ T₁ ⇒ T₂) → V (Γ , A) B → V (Γ , T₁) T₂
lemma1' refl e = e

-- IDEA: I think that it will be necessary to do this where applications are
-- n args, so U has one constructor with a variable and args, rather than
-- two constructors Var and App. Then appv will do applications of n length,
-- and subv will be much simpler to code. Only one induction for each of
-- subv and appv.

-- tait : ∀{Γ} → (T : Type) → (e : Exp Γ T)
--   → ((A B : Type) → (T ≡ A ⇒ B) → Exp Γ A → Exp Γ B)
--   × ((icx : InCtx Γ) → (T ≡ Tat icx) → Exp (subCtx icx) T)
-- TODO: uncomment the following after fixing var case of sub above, use that for var case of subv here
subv : ∀{Γ} → (T : Type) → (e : V Γ T)
  → (∀{Γ' T'} → (icx : InCtx Γ') → (T ≡ Tat icx) → V Γ' T' → V (subCtx icx) T')
subv .(Tat icx₁) (fromU (var icx₁)) icx p subIn = {!   !}
subv .(_ ⇒ _) (lambda e) icx p subIn = {!   !}
-- TODO: how is this / can this be decreasing on T?
subv T (fromU (app e₁ e₂)) icx p subIn = {!   !} -- sub e₁ and e₂, then appv them?
subv .Nat (fromU z) icx p subIn = {!   !}
subv .(Nat ⇒ Nat) (fromU s) icx p subIn = {!   !}
-- ...         | test = ?
appv : ∀{Γ} → (T : Type) → (e : V Γ T)
  → ((A B : Type) → (T ≡ A ⇒ B) → V Γ A → V Γ B)
appv .(Tat icx) (fromU (var icx)) A B p e₂ = {!   !}
appv .(_ ⇒ _) (lambda e₁) A B p e₂ = subv A e₂ same refl (lemma1' p e₁)
appv {Γ} T (fromU (app e₁ e₂)) A B p e₃ = fromU (app (subst (λ T → U Γ T) p (app e₁ e₂)) e₃)
appv .(Nat ⇒ Nat) (fromU s) A B p e₂ = {!   !}


-- TODO: find correct theorem on type T on which to induct.

-- basically, want to define eval in naive way BUT
-- do it by induction on TYPES so that we can use types as ordering
-- eval : ∀{Γ} → (T : Type) → Exp Γ T → V Γ T
-- eval {Γ} (T₁ ⇒ T₂) e = recExp e _
--   (λ icx p → subst (λ T → V Γ T) p (fromU (var icx)) ) -- var
--   (λ A B p e → (lambda (eval T₂ (lemma1 p e))) ) -- lambda -- TODO: need to show T₂ ≡ B
--   (λ p → subst (λ T → V Γ T) p (fromU s) ) -- s
--   (λ p → subst (λ T → V Γ T) p (fromU z)) -- z
--   (λ A e₁ e₂ → recExp e₁ _
--     {!   !}
--     {!   !}
--     {!   !}
--     {!   !}
--     {!   !}
--     )
-- eval Nat e = {!   !}
