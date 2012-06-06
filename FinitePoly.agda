module FinitePoly where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Type : ℕ → Set where
  `⊥ : Type 0
  `⊤ : Type 1

  _`⊎_ : ∀ {m n}
    (S : Type m) (T : Type n) →
    Type (m + n)

  _`×_ : ∀ {m n}
    (S : Type m) (T : Type n) →
    Type (m * n)

El : ∀ {n} → Type n → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T

