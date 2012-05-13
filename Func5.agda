module Func5 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

data Type : Set where
  `⊥ `⊤ `X : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `μ : (R : Type) → Type

El : Type → Set → Set
data μ (R : Type) : Set

El `⊥ X = ⊥
El `⊤ X = ⊤
El `X X = X
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El (`μ R) X = μ R

data μ R where
  [_] : El R (μ R) → μ R

`nat : Type
`nat = `⊤ `⊎ `X

`fin : Type
`fin = (`μ `nat) `× (`⊤ `⊎ `X)

fzero : μ `fin
fzero = [ ([ (inj₁ tt) ] , (inj₁ tt)) ]

fzero+fsuc : μ `nat → μ `fin
fzero+fsuc [ inj₁ tt ] = fzero
fzero+fsuc [ inj₂ n ] = [ ([ inj₂ n ] , inj₂ (fzero+fsuc n)) ]

