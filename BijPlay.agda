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

-- graph [] (1 ∷ 2 ∷ 3 ∷ [])
-- graph (1 ∷ []) (2 ∷ 3 ∷ 4 ∷ [])
-- graph (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ 5 ∷ [])
graph : ∀ {m n} {A B : Set} →
      (Vec A m) →
      (Vec B n) →
      Vec (Vec (A × B) m) (n ^ m)
graph [] ys = [] ∷ []
graph (x ∷ xs) ys = concat (map (λ y → map (_∷_ (x , y)) (graph xs ys)) ys)

data Type : Set
El : Type → Set
count : Type → ℕ

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = Vec (El S × El T) (count S)

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
... | xs | ys = graph xs ys

