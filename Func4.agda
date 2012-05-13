module Func4 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product


data Type : Set where
  `⊥ `⊤ `X : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El : Type → Set → Set
-- data μ (R : Type) : Set

El `⊥ X = ⊥
El `⊤ X = ⊤
El `X X = X
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El (S `→ T) X = El S X → El T X

-- data μ R where
--   [_] : El R (μ R) → μ R

`nat : Type
`nat = `⊤ `⊎ `X

`fin : Type
`fin = `nat `→ (`⊤ `⊎ `X)

`fzero+fsuc : El `fin ⊥
`fzero+fsuc (inj₁ tt) = inj₁ tt
`fzero+fsuc (inj₂ ())

-- `suc : El `nat Type
-- `suc = ?



