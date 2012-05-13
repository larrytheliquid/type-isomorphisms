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
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
El (`Π S T) = (s : El S) → El (T s)
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

`bool : Type
`bool = `⊤ `⊎ `⊤

`threeR : Type
`threeR = `⊤ `⊎ (`⊤ `⊎ `⊤)

`threeL : Type
`threeL = (`⊤ `⊎ `⊤) `⊎ `⊤

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

-- 2 × (0 ∨ 1)

-- 2 * (2 -> 3) = 2 * 3^2 = 18
-- 1 * (1 -> 2) = 1 * 2^1 = 2
-- 2 * (2 -> 2) = 2 * 2^2 = 8
`Σarith : Type
`Σarith = `Σ `bool f where
  f : El `bool → Type
  f (inj₁ tt) = `threeL
  f (inj₂ tt) = `threeR

`four : Type
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`0 : El `four
`0 = (inj₁ tt)
`1 : El `four
`1 = (inj₂ (inj₁ tt))
`2 : El `four
`2 = (inj₂ (inj₂ (inj₁ tt)))
`3 : El `four
`3 = (inj₂ (inj₂ (inj₂ tt)))

`even : El `four → Type
`even (inj₁ tt) = `⊤
`even (inj₂ (inj₁ tt)) = `⊥
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥

`odd : El `four → Type
`odd (inj₁ tt) = `⊥
`odd (inj₂ (inj₁ tt)) = `⊤
`odd (inj₂ (inj₂ (inj₁ tt))) = `⊥
`odd (inj₂ (inj₂ (inj₂ tt))) = `⊤

2even : El (`even `2)
2even = tt

3odd : El (`odd `3)
3odd = tt

`∀even : Type
`∀even = `Π `four `even

`∃even : Type
`∃even = `Σ `four `even

`∃odd : Type
`∃odd = `Σ `four `odd

∃even : El `∃even
∃even = `2 , tt

∃odd : El `∃odd
∃odd = `3 , tt


