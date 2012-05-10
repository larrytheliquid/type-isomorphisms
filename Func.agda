module Func where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

infix 1 `μ_

data Ind : Set where
  `0 `1 `x : Ind
  _`+_ _`*_ : (S T : Ind) → Ind

El : Ind → Set → Set
El `0 X = ⊥
El `1 X = ⊤
El `x X = X
El (S `+ T) X = El S X ⊎ El T X
El (S `* T) X = El S X × El T X

data μ (R : Ind) : Set where
  [_] : El R (μ R) → μ R

data Type : Set
⟦_⟧ : Type → Set

data Type where
  `Π : (S : Type)(T : ⟦ S ⟧ → Type) → Type
  `μ_ : (R : Ind) → Type

⟦ `Π S T ⟧ =  (s : ⟦ S ⟧) → ⟦ T s ⟧
⟦ `μ R ⟧ =  μ R

`bool : Type
`bool = `μ `1 `+ `1

`nat : Type
`nat = `μ `1 `+ `x

`zero : ⟦ `nat ⟧
`zero = [ inj₁ tt ]

`suc : ⟦ `nat ⟧ → ⟦ `nat ⟧
`suc n = [ inj₂ n ]

`suc′ : ⟦ `Π `nat (λ _ → `nat) ⟧
`suc′ n = [ inj₂ n ]

`fin : Type
`fin = `Π `nat (λ x → `μ `f x) where
  `f : ⟦ `nat ⟧ → Ind
  `f [ inj₁ tt ] = `0
  `f [ inj₂ n ] = `1 `+ `f n

-- `fin′ : ⟦ `nat ⟧ → Ind
-- `fin′ [ inj₁ tt ] = `0
-- `fin′ [ inj₂ n ] = `1 `+ `fin′ n

