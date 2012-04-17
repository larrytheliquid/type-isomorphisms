module BiProofs where
open import Data.Nat

infixr 4 _`+_

data Proofs : ℕ → ℕ → Set where
  `0 : Proofs 0 0
  `1 : Proofs 1 0
  `x : Proofs 0 1

  _`+_ : ∀ {x y χ γ} →
    Proofs x χ → Proofs y γ →
    Proofs (x + y) (χ + γ)

`bool : Proofs 2 0
`bool = `1 `+ `1

`three : Proofs 3 0
`three = `1 `+ `1 `+ `1

`nat : Proofs 1 1
`nat = `1 `+ `x

