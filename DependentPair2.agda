module DependentPair2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List
open import Relation.Binary.PropositionalEquality

lookup : {A : Set} (xs : List A) → Fin (length xs) → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

image : {A : Set}
  (m : ℕ) → (xs : List A) →
  List (List A)
image zero xs = [] ∷ []
image (suc m) xs = concat (map (λ x → map (_∷_ x) (image m xs)) xs)

--------------------------------------------------------------------------------

data Type : Set where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El : Type → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T

enum : (R : Type) → List (El R)
postulate
  toFin : {R : Type} → El R → Fin (length (enum R))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = map (λ ts s → lookup ts {!toFin {S} s!}) (image (length (enum S)) (enum T))
-- map (λ ts s → lookup (toFin {S} s) ts ) (image (count S) (enum T))

count : Type → ℕ
count R = length (enum R)



