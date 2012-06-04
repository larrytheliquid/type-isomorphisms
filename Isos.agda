module Isos where
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality

toMaybeℕ : ℕ → Maybe ℕ
toMaybeℕ zero = nothing
toMaybeℕ (suc n) = just n

toℕ : Maybe ℕ → ℕ
toℕ nothing = zero
toℕ (just n) = suc n

toℕ∘toMaybeℕ≡x : ∀ x → toℕ (toMaybeℕ x) ≡ x
toℕ∘toMaybeℕ≡x zero = refl
toℕ∘toMaybeℕ≡x (suc n) = refl

toMaybeℕ∘toℕ≡x : ∀ x → toMaybeℕ (toℕ x) ≡ x
toMaybeℕ∘toℕ≡x nothing = refl
toMaybeℕ∘toℕ≡x (just n) = refl

to2+ℕ : ℕ → Bool ⊎ ℕ
to2+ℕ zero = inj₁ true
to2+ℕ (suc zero) = inj₁ false
to2+ℕ (suc (suc n)) = inj₂ n

from2+ℕ : Bool ⊎ ℕ → ℕ
from2+ℕ (inj₁ true) = zero
from2+ℕ (inj₁ false) = suc zero
from2+ℕ (inj₂ n) = suc (suc n)

to∘from2+ℕ : ∀ x → to2+ℕ (from2+ℕ x) ≡ x
to∘from2+ℕ (inj₁ true) = refl
to∘from2+ℕ (inj₁ false) = refl
to∘from2+ℕ (inj₂ n) = refl

from∘to2+ℕ : ∀ x → from2+ℕ (to2+ℕ x) ≡ x
from∘to2+ℕ zero = refl
from∘to2+ℕ (suc zero) = refl
from∘to2+ℕ (suc (suc n)) = refl

-- data Even : ℕ → Set where
--   zero : Even 0
--   next : ∀ {n} → Even n → Even (2 + n)

-- data Odd : ℕ → Set where
--   one : Odd 1
--   next : ∀ {n} → Odd n → Odd (2 + n)

-- toOdd : ∀ {n} → Even n → Odd (suc n)
-- toOdd zero = one
-- toOdd (next x) = next (toOdd x)

-- lemma : ∀ {n} → Odd n → suc (pred n) ≡ n
-- lemma one = refl
-- lemma (next odd) = refl

-- toEven : ∀ {n} → Odd n → Even (pred n)
-- toEven one = zero
-- toEven (next x) with toEven x
-- ... | ih = {!!}

data Tree : Set where
  leaf : Tree
  node : (l r : Tree) → Tree

toTree : ℕ → Tree
toTree zero = leaf
toTree (suc zero) = node leaf leaf
toTree (suc (suc n)) = node (toTree n) (toTree (suc n))

fromTree : Tree → ℕ
fromTree leaf = 0
fromTree (node leaf leaf) = 1
fromTree (node (node a b) leaf) = 1 + fromTree (node a b)
fromTree (node leaf (node x y)) = 2 + fromTree (node x y)
fromTree (node (node a b) (node x y)) = fromTree (node a b) + fromTree (node x y)

to∘fromTree : ∀ x → toTree (fromTree x) ≡ x
to∘fromTree leaf = refl
to∘fromTree (node leaf leaf) = refl
to∘fromTree (node (node a b) leaf) with to∘fromTree (node a b)
... | ih = {!!}
to∘fromTree (node leaf (node x y)) = {!!}
to∘fromTree (node (node a b) (node x y)) = {!!}
