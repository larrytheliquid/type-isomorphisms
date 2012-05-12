module Func3 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type
  `Π `Σ : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
-- El `X = Type
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
El (`Π S T) = (s : El S) → El (T s)
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

`bool : Type
`bool = `⊤ `⊎ `⊤

`nat : Type
`nat = `Σ `bool f where
  f : El `bool → Type
  f (inj₁ tt) = `⊤
  f (inj₂ tt) = `bool

`fauxfin : Type
`fauxfin = `Σ `bool f where
  f : El `bool → Type
  f (inj₁ tt) = `⊥
  f (inj₂ tt) = `bool
