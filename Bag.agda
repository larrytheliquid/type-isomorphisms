module Bag where
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality

-- record _⇔_ (A B : Set) : Set where
--   field to : A → B
--         from : B → A

infix 1 _↔_

record _↔_ (A B : Set) : Set where
  field to : A → B
        from : B → A
        from-to : ∀ x → from (to x) ≡ x
        to-from : ∀ x → to (from x) ≡ x
open _↔_

lookup : {A : Set} (xs : List A) → Fin (length xs) → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

record _≈′_ {A} (xs ys : List A) : Set where
  field bijection : Fin (length xs) ↔ Fin (length ys)
        related : ∀ i → lookup xs i ≡ lookup ys (to bijection i)

Any : ∀ {A : Set} → (A → Set) → List A → Set
Any P [] = ⊥
Any P (x ∷ xs) = P x ⊎ Any P xs

_∈_ : {A : Set} → A → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

_≈_ : {A : Set} → List A → List A → Set
xs ≈ ys = ∀ z → z ∈ xs ↔ z ∈ ys


