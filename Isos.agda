module Isos where
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

f : ℕ → Maybe ℕ
f zero = nothing
f (suc n) = just n

g : Maybe ℕ → ℕ
g nothing = zero
g (just n) = suc n

g∘f≡x : ∀ x → g (f x) ≡ x
g∘f≡x zero = refl
g∘f≡x (suc n) = refl

f∘g≡x : ∀ x → f (g x) ≡ x
f∘g≡x nothing = refl
f∘g≡x (just n) = refl
