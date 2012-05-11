module Func where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

infix 1 `μ_

data Ind : Set where
  `⊥ `⊤ `x : Ind
  _`⊎_ _`×_ : (S T : Ind) → Ind
  `[_] : (R : Ind) → Ind

El : Ind → Set → Set
data μ (R : Ind) : Set

El `⊥ X = ⊥
El `⊤ X = ⊤
El `x X = X
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El `[ R ] X = μ R

data μ R where
  [_] : El R (μ R) → μ R

data Type : Set
⟦_⟧ : Type → Set

data Type where
  `Π `Σ : (S : Type)(T : ⟦ S ⟧ → Type) → Type
  `μ_ : (R : Ind) → Type

⟦ `Π S T ⟧ =  (s : ⟦ S ⟧) → ⟦ T s ⟧
⟦ `Σ S T ⟧ =  Σ[ s ∶ ⟦ S ⟧ ] ⟦ T s ⟧
⟦ `μ R ⟧ =  μ R

`bool : Type
`bool = `μ `⊤ `⊎ `⊤

`nat : Type
`nat = `μ `⊤ `⊎ `x

`zero : ⟦ `nat ⟧
`zero = [ inj₁ tt ]

`suc : ⟦ `nat ⟧ → ⟦ `nat ⟧
`suc n = [ inj₂ n ]

`suc′ : ⟦ `Π `nat (λ _ → `nat) ⟧
`suc′ n = [ inj₂ n ]

`fin : Type
`fin = `Π `nat (λ x → `μ `f x) where
  `f : ⟦ `nat ⟧ → Ind
  `f [ inj₁ tt ] = `⊥
  `f [ inj₂ n ] = `⊤ `⊎ `f n

`fin′ : ⟦ `nat ⟧ → Ind
`fin′ [ inj₁ tt ] = `⊥
`fin′ [ inj₂ n ] = `⊤ `⊎ `fin′ n

`vec⊤ : Type
`vec⊤ = `Π `nat (λ x → `μ `f x) where
  `f : ⟦ `nat ⟧ → Ind
  `f [ inj₁ tt ] = `⊤
  `f [ inj₂ n ] = `⊤ `× `f n

`vec : Ind → Type
`vec A = `Π `nat (λ x → `μ `f x) where
  `f : ⟦ `nat ⟧ → Ind
  `f [ inj₁ tt ] = `⊤
  `f [ inj₂ n ] = `[ A ] `× `f n
