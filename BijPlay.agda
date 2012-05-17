module BijPlay where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

exp : ∀ {m n} {A B : Set} →
      (Vec A m) →
      (Vec B n) →
      Vec (Vec A m) (m ^ n)
exp xs [] = xs ∷ []
exp xs (y ∷ ys) = concat (map (λ _ → exp xs ys) xs)

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

postulate toFin : {R : Type} → El R → Fin (count R)

enum : (R : Type) → Vec (El R) (count R)
enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) with enum S | enum T
... | xs | ys with exp xs ys
... | hm = {!!}

-- enum : (R : Type) → Vec (El R) (count R)
-- enum `⊥ = []
-- enum `⊤ = tt ∷ []
-- enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
-- enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
-- enum (S `→ T) with enum S | enum T
-- ... | xs | ys = map (λ _ (s : El S) → lookup (toFin {S} s) xs) xs
