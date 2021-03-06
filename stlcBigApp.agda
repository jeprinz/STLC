open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)
open import Data.List
open import Data.Unit

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

-- -- left output means use toSub, right means just adjust x for new context.
varSub : ∀{Γ} → (icx : InCtx Γ)
  → (x : InCtx Γ) → (Tat icx ≡ Tat x) ⊎ (Σ (InCtx (subCtx icx)) (λ i → Tat i ≡ Tat x))
varSub same same = inj₁ refl
varSub same (next x) = inj₂ (x , refl)
varSub (next icx) same = inj₂ (same , refl)
varSub (next icx) (next x) with varSub icx x
...                              | inj₁ p = inj₁ p
...                              | inj₂ (i , p) = inj₂ (next i , p)

-- This is not strictly speaking necessary to exist. Therefore, same for weaken and weakenMany.
sub : ∀{Γ T} → (icx : InCtx Γ) → (toSub : Exp (Γat icx) (Tat icx))
  → Exp Γ T →  Exp (subCtx icx) T
sub icx toSub (var x) with varSub icx x
...                   | inj₁ p = subst (λ T → Exp _ T) p (weakenMany icx toSub)
...                   | inj₂ (i , p) = subst (λ T → Exp _ T) p (var i)
sub icx toSub (app e₁ e₂) = app (sub icx toSub e₁) (sub icx toSub e₂)
sub icx toSub (lambda e) = lambda (sub (next icx) toSub e)
sub icx toSub z = z
sub icx toSub s = s

lToType : List Type → Type → Type
lToType [] T = T
lToType (A ∷ l) T = A ⇒ (lToType l T)

data V : Ctx → Type → Set

lToExps : Ctx → List Type → Set
lToExps Γ [] = ⊤
lToExps Γ (T ∷ l) = (V Γ T) × (lToExps Γ l)

data U : Ctx → Type → Set where
  z : ∀{Γ} → U Γ Nat
  s : ∀{Γ} → V Γ Nat → U Γ Nat
  varapp : ∀{Γ} → (l : List Type)
    → {out : Type}
    → (icx : InCtx Γ)
    → (Tat icx ≡ lToType l out)
    → lToExps Γ l
    → U Γ out

data V where
  lambda : ∀{Γ A B} → V (Γ , A) B → V Γ (A ⇒ B)
  fromU : ∀{Γ T} → U Γ T → V Γ T

weakenV : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → V Γ T → V (weakenΓ pre W) T

weakenVs : ∀{Γ} → (pre : Pre Γ) → (W : Type)
  → (Ts : List Type)
  → lToExps Γ Ts → lToExps (weakenΓ pre W) Ts
weakenVs pre W [] Vs = tt
weakenVs pre W (T ∷ Ts) (V , Vs) = weakenV pre W V , weakenVs pre W Ts Vs

weakenV pre W (lambda v) = lambda (weakenV (next pre) W v)
weakenV pre W (fromU z) = fromU z
weakenV pre W (fromU (s x)) = fromU (s (weakenV pre W x))
weakenV pre W (fromU (varapp Ts icx p Vs)) with weakenICX pre W icx
... | (i , p₁) = fromU (varapp Ts i (trans p₁ p) (weakenVs pre W Ts Vs) )

weakenManyV : ∀{Γ T} → (icx : InCtx Γ)
  → V (Γat icx) T → V (subCtx icx) T
weakenManyV same e = e
weakenManyV (next {_} {T} icx) e = weakenV same T (weakenManyV icx e)

lemma2 : ∀{A B C D} → (A ⇒ B ≡ C ⇒ D) → A ≡ C
lemma2 refl = refl
lemma3 : ∀{A B C D} → (A ⇒ B ≡ C ⇒ D) → B ≡ D
lemma3 refl = refl
lemma4 : ∀{argsT out} → Nat ≡ lToType argsT out → Nat ≡ out
lemma4 {[]} {out} p = p
lemma5 : ∀{Ts1 Ts2 out} → lToType Ts1 (lToType Ts2 out) ≡ lToType (Ts1 ++ Ts2) out
lemma5 {[]} {Ts2} = refl
lemma5 {T ∷ Ts1} {Ts2} {out} = cong (λ B → T ⇒ B) (lemma5 {Ts1} {Ts2} {out})
lemma6 : ∀{Γ} →  (Ts1 Ts2 : List Type) → lToExps Γ Ts1 → lToExps Γ Ts2 → lToExps Γ (Ts1 ++ Ts2)
lemma6 [] Ts2 Vs1 Vs2 = Vs2
lemma6 (T ∷ Ts1) Ts2 (V , Vs1) Vs2 = V , lemma6 Ts1 Ts2 Vs1 Vs2

-- TODO: why not just replace T with Tat icx and remove the equality? probably it would break prim recursion?
subv : ∀{Γ} → (T : Type) → ∀{T'} → (icx : InCtx Γ)
  → (toSub : V (subCtx icx) T) → (T ≡ Tat icx) → V Γ T' → V (subCtx icx) T'

-- TODO: make T : Type implicit in appv and subv
appv : ∀{Γ} → (T : Type) → (e : V Γ T)
  → (l : List Type) → (out : Type) → (T ≡ lToType l out)
  → lToExps Γ l → V Γ out
appv {Γ} .(_ ⇒ _) (lambda e) [] out p argsV = subst (λ T → V Γ T) p (lambda e)
appv {Γ} (A ⇒ B) (lambda e) (x ∷ argsT) out p (v , argsV) -- = {!   !} -- in terms of appv argsT, recurse!
  = let f = subv A same (subst _ (lemma2 (sym p)) v) refl e -- TODO: make there not be sym
    in appv B f argsT out (lemma3 p) argsV -- appv f argsT
appv {Γ} .Nat (fromU z) argsT out p argsV = subst (λ T → V Γ T) (lemma4 p) (fromU z)
appv {Γ} .Nat (fromU (s x)) argsT out p argsV = subst (λ T → V Γ T) (lemma4 p) (fromU (s x))
appv T (fromU (varapp Ts icx p₁ Vs)) argsT out p argsV
  = fromU (varapp (Ts ++ argsT) icx
    (subst (λ T → Tat icx ≡ T) (lemma5 {Ts} {argsT} {out}) (subst (λ T → Tat icx ≡ lToType Ts T) p p₁))
    (lemma6 _ _ Vs argsV) )

subMap : ∀{Γ} → (T : Type)
  → (icx : InCtx Γ) → (toSub : V (subCtx icx) T) → (T ≡ Tat icx)
  → (Ts : List Type)
  → lToExps Γ Ts → lToExps (subCtx icx) Ts
subMap T icx toSub p [] Vs = tt
subMap _ icx toSub p (T ∷ Ts) (V , Vs)
  = subv _ icx toSub p V , subMap _ icx toSub p Ts Vs

subv T icx toSub p (lambda v) = lambda (subv T (next icx) (weakenV same _ toSub) p v)
subv T icx toSub p (fromU z) = fromU z
subv T icx toSub p (fromU (s x)) = fromU (s (subv T icx toSub p x))
subv T icx toSub p (fromU (varapp Ts {out} x p₂ Vs))
  with varSub icx x
...  | inj₁ p₃ = appv T toSub Ts out (trans (trans p p₃) p₂) (subMap T icx toSub p Ts Vs)
...  | inj₂ (subx , p₃) = fromU (varapp Ts subx (trans p₃ p₂) (subMap T icx toSub p Ts Vs) )

normalize : ∀{Γ T} → Exp Γ T → V Γ T
normalize (var icx) = fromU (varapp [] icx refl tt )
normalize (lambda e) = lambda (normalize e)
normalize (app e e₁) = appv _ (normalize e) _ _ refl (normalize e₁ , tt )
normalize z = fromU z
normalize s = lambda (fromU (s (fromU (varapp [] same refl tt)))) -- a little janky, s ↦ λ x . s x


id : V ∅ (Nat ⇒ Nat)
id = lambda (fromU (varapp [] same refl tt ))

one : V ∅ Nat
one = fromU (s (fromU z))

idOne : V ∅ Nat
idOne = appv (Nat ⇒ Nat) id [ Nat ] Nat  refl ( one , tt)

test : idOne ≡ one
test = refl
