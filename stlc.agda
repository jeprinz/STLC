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

lemma1' : ∀{Γ A B T₁ T₂} → (A ⇒ B ≡ T₁ ⇒ T₂) → V (Γ , A) B → V (Γ , T₁) T₂
lemma1' refl e = e

-- IDEA: I think that it will be necessary to do this where applications are
-- n args, so U has one constructor with a variable and args, rather than
-- two constructors Var and App. Then appv will do applications of n length,
-- and subv will be much simpler to code. Only one induction for each of
-- subv and appv.

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
