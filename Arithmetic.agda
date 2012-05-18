module Arithmetic where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.List
open import Relation.Binary.PropositionalEquality

lookup : {A : Set} → (xs : List A) → Fin (length xs) → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

image : {A : Set}
  (m : ℕ) → (xs : List A) →
  List (List A)
image zero xs = [] ∷ []
image (suc m) xs = concat (map (λ x → map (_∷_ x) (image m xs)) xs)

fconcat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
fconcat {zero} {n} () j
fconcat {suc m} {zero} zero ()
fconcat {suc m} {suc n} zero j = inject+ _ j
fconcat {suc m} {n} (suc i) j = raise n (fconcat i j)

fimage : ∀ {n} → (xs : List (Fin n)) → Fin (n ^ length xs)
fimage [] = zero
fimage (x ∷ xs) = fconcat x (fimage xs)

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S

toFin : {R : Type} → El R → ∃ Fin
enum : (R : Type) → List (El R)

toFin {`⊥} ()
toFin {`⊤} tt = 1 , zero
toFin {S `⊎ T} (inj₁ x) = _ , inject+ (count T) (proj₂ (toFin {S} x))
toFin {S `⊎ T} (inj₂ y) = _ , raise (count S) (proj₂ (toFin {T} y))
toFin {S `× T} (x , y) = _ , fconcat (proj₂ (toFin {S} x)) (proj₂ (toFin {T} y))
toFin {S `→ T} f = {!!} -- fimage (map (λ t → {!proj₂ (toFin {T} t)!}) (map f (enum S)))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = ? -- map (λ ts s → lookup ts (proj₂ (toFin {S} s))) (image (count S) (enum T))


