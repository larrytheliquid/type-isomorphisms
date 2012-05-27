module MonomialPoly where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List hiding ( [_] )
open import Relation.Binary.PropositionalEquality

_[+]_ : List ℕ → List ℕ → List ℕ
[] [+] ys = ys
xs [+] [] = xs
(x ∷ xs) [+] (y ∷ ys) = x + y ∷ xs [+] ys

_[*]_ : List ℕ → List ℕ → List ℕ
[] [*] ys = []
(x ∷ xs) [*] ys = map (_*_ x) ys [+] (xs [*] (zero ∷ ys))

--------------------------------------------------------------------------------

data Type : List ℕ → Set where
  `⊥ : Type (0 ∷ [])
  `⊤ : Type (1 ∷ [])
  `X : Type (0 ∷ 1 ∷ [])
  _`⊎_ : ∀ {xs ys} (S : Type xs) (T : Type ys) → Type (xs [+] ys)
  _`×_ : ∀ {xs ys} (S : Type xs) (T : Type ys) → Type (xs [*] ys)

El : ∀ {xs} → Type xs → Set → Set
El `⊥ X = ⊥
El `⊤ X = ⊤
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El `X X = X

data μ {xs} (R : Type xs) : Set where
  [_] : El R (μ R) → μ R

--------------------------------------------------------------------------------

`Bool : Type (2 ∷ [])
`Bool = `⊤ `⊎ `⊤

`ℕ : Type (1 ∷ 1 ∷ [])
`ℕ = `⊤ `⊎ `X

`zero : μ `ℕ
`zero = [ inj₁ tt ]

`suc : μ `ℕ → μ `ℕ
`suc n = [ inj₂ n ]

`Tree : Type (1 ∷ 0 ∷ 1 ∷ [])
`Tree = `⊤ `⊎ (`X `× `X)

`leaf : μ `Tree
`leaf = [ inj₁ tt ]

`node : μ `Tree → μ `Tree → μ `Tree
`node l r = [ inj₂ (l , r) ]

