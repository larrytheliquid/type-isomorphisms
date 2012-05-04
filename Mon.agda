module Mon where
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Monoid : ℕ → Set where
  `0 : Monoid 0
  `1 : Monoid 1

  _`+_ : ∀ {x y}
    (S : Monoid x) (T : Monoid y) →
    Monoid (x + y)

  _`*_ : ∀ {x y}
    (S : Monoid x) (T : Monoid y) →
    Monoid (x * y)

El : ∀ {n} → Monoid n → Vec ⊤ n
El `0 = []
El `1 = tt ∷ []
El (S `+ T) = El S ++ El T
El (S `* T) = concat (map (λ _ → El T) (El S))
