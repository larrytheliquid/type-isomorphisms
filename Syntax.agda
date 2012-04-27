module Syntax where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

data Type : Set where
  `0 `1 : Type
  _`+_ _`*_ : (S T : Type) → Type

data Value : Set where
  tt : Value
  inj₁ inj₂ : (x : Value) → Value
  _,_ : (x y : Value) → Value

El : Type → Set
El `0 = ⊥
El `1 = ⊤
El (S `+ T) = El S ⊎ El T
El (S `* T) = El S × El T

val : {F : Type} → El F → Value
val {`0} ()
val {`1} tt = tt
val {S `+ T} (inj₁ x) = inj₁ (val {S} x)
val {S `+ T} (inj₂ y) = inj₂ (val {T} y)
val {S `* T} (x , y) = val {S} x , val {T} y

data ⟦_⟧ (F : Type) : Value → Set where
  [_] : (x : El F) → ⟦ F ⟧ (val {F} x)

