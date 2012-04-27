module Syntax where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Type : Set where
  `0 `1 : Type
  _`+_ _`*_ : (S T : Type) → Type

data Value : Set where
  tt : Value
  inj₁ inj₂ : (x : Value) → Value
  _,_ : (x y : Value) → Value

data Types : Value → Type → Set where
  tt : Types tt `1
  inj₁ : ∀ {s S T} →
    Types s S →
    Types (inj₁ s) (S `+ T)
  inj₂ : ∀ {S t T} →
    Types t T →
    Types (inj₂ t) (S `+ T)
  _,_ : ∀ {s S t T} →
    Types s S → Types t T →
    Types (s , t) (S `* T)

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

-- infer : val to Types

inject : ∀ {S T : Type} (s : El S) → Types (val {S} s) T → El T
inject {`0} () p
inject {`1} tt tt = tt
inject {S `+ T} (inj₁ s) (inj₁ p) = inj₁ (inject s p)
inject {S `+ T} (inj₂ t) (inj₂ p) = inj₂ (inject t p)
inject {S `* T} (s , t) (p₁ , p₂) = inject s p₁ , inject t p₂

`2 : Type
`2 = `1 `+ `1

`3 : Type
`3 = `1 `+ `2

one : El `3
one = inj₁ tt

two : El `3
two = inj₂ (inject {`3} {`2} one (inj₁ tt))

