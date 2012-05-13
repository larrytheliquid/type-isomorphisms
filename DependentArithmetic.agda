module DependentArithmetic where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product

Four = Fin 4

data Even : Four → Set where
  zero : Even (# 0)
  two : Even (# 2)

data Odd : Four → Set where
  one : Odd (# 1)
  three : Odd (# 3)

Evenλ : Four → Set
Evenλ zero = ⊤
Evenλ (suc zero) = ⊥
Evenλ (suc (suc zero)) = ⊤
Evenλ (suc (suc (suc zero))) = ⊥
Evenλ (suc (suc (suc (suc ()))))

Oddλ : Four → Set
Oddλ zero = ⊥
Oddλ (suc zero) = ⊤
Oddλ (suc (suc zero)) = ⊥
Oddλ (suc (suc (suc zero))) = ⊤
Oddλ (suc (suc (suc (suc ()))))

3Odd : Odd (# 3)
3Odd = three
-- 3Odd = ⟨ two ⟩

∃Even : ∃ Even
∃Even = # 2 , two

∃Odd : ∃ Odd
∃Odd = # 3 , three



