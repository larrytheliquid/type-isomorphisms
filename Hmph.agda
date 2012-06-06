module Hmph where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

Maybeℕ = Maybe ℕ

data ℕ₂ : Set where
  nothing zero : ℕ₂
  suc : ℕ₂ → ℕ₂

a00 : Maybeℕ
a00 = nothing

a01 : Maybeℕ
a01 = just zero

b00 : ℕ₂
b00 = nothing

b01 : ℕ₂
b01 = zero

a10 : Maybeℕ
a10 = just (suc zero)

b10 : ℕ₂
b10 = suc zero

b11 : ℕ₂
b11 = suc nothing
