open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- TERMINATION

f g : ℕ → ℕ → ℕ
f (suc n) m = g n m
f _ _ = 0
g n (suc m) = f m n
g _ _ = 0



h k : ℕ → ℕ → ℕ ≡ ℕ → ℕ
h (suc n) m p = k (subst (λ T → T) p n) m p
h _ _ p = 0
k n (suc m) p = h m n p
k _ _ p = 0
