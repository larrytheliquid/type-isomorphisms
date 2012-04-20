module BiProofs where
open import Data.Nat

infixr 6 _`+_

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

height : ℕ → ℕ → ℕ → ℕ
height zero x χ = x
height (suc n) x χ = χ * height n x χ

card : ℕ → ℕ → ℕ → ℕ
card n x χ = pred (χ * height n x χ)

depth : ℕ → ℕ → ℕ → ℕ
depth χ Χ zero = 1
depth χ Χ (suc zero) = χ
depth χ Χ (suc (suc d)) = χ * (Σ[ suc d ]depth ^ Χ ∸ Σ[ d ]depth ^ Χ)
  where
    Σ[_]depth : ℕ → ℕ
    Σ[ zero ]depth = depth χ Χ 0
    Σ[ suc d ]depth = depth χ Χ (suc d) + Σ[ d ]depth

data Proofs : ℕ → ℕ → Set where
  `0 : Proofs 0 0
  `1 : Proofs 1 0
  `x : Proofs 0 1

  _`+_ : ∀ {x y χ γ} →
    Proofs x χ → Proofs y γ →
    Proofs (x + y) (χ + γ)

data Card (h : ℕ) : ℕ → ℕ → Set where
  ∣_∣ : ∀ {x χ} → Proofs x χ → Card h (height 0 x χ) (height h x χ)

`bool : Proofs 2 0
`bool = `1 `+ `1

∣bool∣ : Card 4 2 0
∣bool∣ = ∣ `bool ∣

`three : Proofs 3 0
`three = `1 `+ `1 `+ `1

∣three∣ : Card 4 3 0
∣three∣ = ∣ `three ∣

`nat : Proofs 1 1
`nat = `1 `+ `x

∣nat∣ : Card 4 1 1
∣nat∣ = ∣ `nat ∣

`nat₂ : Proofs 1 2
`nat₂ = `1 `+ `x `+ `x

∣nat₂∣ : Card 4 1 16
∣nat₂∣ = ∣ `nat₂ ∣

