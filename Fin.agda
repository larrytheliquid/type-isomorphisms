module Fin where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
-- open import Data.Fin
open import Data.Vec

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

data Three : Set where
  one two three : Three

wut : Fin 3 → Three
wut (inj₁ x) = one
wut (inj₂ (inj₁ x)) = two
wut (inj₂ (inj₂ (inj₁ x))) = three
wut (inj₂ (inj₂ (inj₂ ())))

tabulate' : ∀ {n} {A : Set} → (Fin n → A) → Vec A n
tabulate' {zero}  f = []
tabulate' {suc n} f = f (inj₁ tt) ∷ tabulate' (λ x → f (inj₂ x))

allFin' : ∀ n → Vec (Fin n) n
allFin' _ = tabulate' (λ x → x)

-- --------------------------------------------------------------------------------

-- data ℕ : Set where
--   zero : ℕ
--   suc  : (n : ℕ) → ℕ

-- {-# BUILTIN NATURAL ℕ    #-}
-- {-# BUILTIN ZERO    zero #-}
-- {-# BUILTIN SUC     suc  #-}

-- data Fin : ℕ → Set where
--   zero : {n : ℕ} → Fin (suc n)
--   suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- data Vec (A : Set) : ℕ → Set where
--   []  : Vec A zero
--   _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

-- tabulate : ∀ {n} {A : Set} → (Fin n → A) → Vec A n
-- tabulate {zero}  f = []
-- tabulate {suc n} f = f zero ∷ tabulate (λ x → f (suc x))

-- allFin : ∀ n → Vec (Fin n) n
-- allFin _ = tabulate (λ x → x)

-- --------------------------------------------------------------------------------

-- zero1 : Fin 1
-- zero1 = zero

-- zero2 : Fin 2
-- zero2 = zero

-- one2 : Fin 2
-- one2 = suc zero1

-- zero3 : Fin 3
-- zero3 = zero

-- one3 : Fin 3
-- one3 = suc zero2

-- two3 : Fin 3
-- two3 = suc one2
