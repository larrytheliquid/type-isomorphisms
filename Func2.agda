module Func2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

data Ind : Set
El : Ind → Set → Set
data μ (R : Ind) : Set

data Ind where
  `⊥ `⊤ `x : Ind
  _`⊎_ _`×_ : (S T : Ind) → Ind
  `Π : (S : Ind)(T : μ S → Ind) → Ind
  -- `[_] : (R : Ind) → Ind

El `⊥ X = ⊥
El `⊤ X = ⊤
El `x X = X
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El (`Π S T) X = (s : μ S) → El (T s) X
-- El `[ R ] X = μ R

data μ R where
  [_] : El R (μ R) → μ R
