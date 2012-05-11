module Func4 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product


data Type : Set where
  `⊥ `⊤ `x : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El : Type → Set → Set
data μ (R : Type) : Set

El `⊥ X = ⊥
El `⊤ X = ⊤
El `x X = X
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El (S `→ T) X = El S X → El T X

data μ R where
  [_] : El R (μ R) → μ R



