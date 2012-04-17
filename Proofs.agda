module Proofs where
open import Data.Nat

data ∞ℕ : Set where
  [0] : ∞ℕ
  [∞] : ∞ℕ
  [_] : ℕ → ∞ℕ

_+∞_ : ∞ℕ → ∞ℕ → ∞ℕ
[0] +∞ [0] = [0]
[0] +∞ y = [∞]
x +∞ [0] = [∞]
[∞] +∞ y = [∞]
x +∞ [∞] = [∞]
[ m ] +∞ [ n ] = [ m + n ]

_*∞_ : ∞ℕ → ∞ℕ → ∞ℕ
[0] *∞ y = [0]
x *∞ [0] = [0]
[ 0 ] *∞ y = [ 0 ]
x *∞ [ 0 ] = [ 0 ]
[∞] *∞ y = [∞]
x *∞ [∞] = [∞]
[ m ] *∞ [ n ] = [ m * n ]

data Proofs : ∞ℕ → Set where
  `0 : Proofs [ 0 ]
  `1 : Proofs [ 1 ]
  `x : Proofs [0]

  _`+_ : ∀ {x y} →
    Proofs x → Proofs y →
    Proofs (x +∞ y)

  _`*_ : ∀ {x y} →
    Proofs x → Proofs y →
    Proofs (x *∞ y)

  `μ : ∀ {m} →
    Proofs m →
    Proofs m

`bool : Proofs [ 2 ]
`bool = `1 `+ `1

`nat : Proofs [∞]
`nat = `1 `+ `x

`natlist : Proofs [∞]
`natlist = `1 `+ (`μ `nat `* `x)

`list : ∀ {x} → Proofs x → Proofs [∞]
`list {[0]} x = `1 `+ (`μ x `* `x) -- WRONG [0]
`list {[∞]} x = `1 `+ (`μ x `* `x)
`list {[ _ ]} x = `1 `+ (`μ x `* `x)
