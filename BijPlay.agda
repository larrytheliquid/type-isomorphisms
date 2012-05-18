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

fconcat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
fconcat {zero} {n} () j
fconcat {suc m} {zero} zero ()
fconcat {suc m} {suc n} zero j = inject+ _ j
fconcat {suc m} {n} (suc i) j = raise n (fconcat i j)

fimage : ∀ {m n} → Fin m → Fin n → Fin (n ^ m)
fimage {zero} i j = zero
fimage {suc zero} i j = fconcat j zero
fimage {suc (suc n)} i j = fconcat j (fimage {suc n} zero j)

graph : ∀ {m n} {A B : Set} →
      (Vec A m) →
      (Vec B n) →
      Vec (Vec (A × B) m) (n ^ m)
graph [] ys = [] ∷ []
graph (x ∷ xs) ys = concat (map (λ y → map (_∷_ (x , y)) (graph xs ys)) ys)

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

toFin : {R : Type} → El R → Fin (count R)
toλ : ∀ {S T} → Vec (El S × El T) (count S) → El S → El T
enum : (R : Type) → Vec (El R) (count R)

toFin {`⊥} ()
toFin {`⊤} tt = zero
toFin {S `⊎ T} (inj₁ x) = inject+ (count T) (toFin {S} x)
toFin {S `⊎ T} (inj₂ y) = raise (count S) (toFin {T} y)
toFin {S `× T} (x , y) = fconcat (toFin {S} x) (toFin {T} y)
toFin {S `→ T} f = {!!}

toλ {S} xys x = proj₂ (lookup (toFin {S} x) xys)

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = map (toλ {S} {T}) (graph (enum S) (enum T))


