module ArithmeticFin where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

fconcat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
fconcat {zero} {n} () j
fconcat {suc m} {zero} zero ()
fconcat {suc m} {suc n} zero j = inject+ _ j
fconcat {suc m} {n} (suc i) j = raise n (fconcat i j)

∣Σ∣ : ∀ {n} {B : ℕ → Set} (f : Fin n → ∃ B) → ℕ
∣Σ∣ {n} f = sum (map proj₁ (map f (allFin n)))

--------------------------------------------------------------------------------

data Type : ℕ → Set where
  `⊥ : Type 0
  `⊤ : Type 1

  _`⊎_ : ∀ {m n}
    (S : Type m) (T : Type n) →
    Type (m + n)

  _`×_ : ∀ {m n}
    (S : Type m) (T : Type n) →
    Type (m * n)

  `Σ : ∀ {m} →
    (S : Type m) (T : Fin m → ∃ Type) →
    Type (∣Σ∣ T)

El : ∀ {n} → Type n → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ {n} S T) = Σ[ i ∶ Fin n ] El (proj₂ (T i))

-- toFin : {R : Type n} → El R → Fin n
-- toFin {`⊥} ()
-- toFin {`⊤} tt = zero
-- toFin {S `⊎ T} (inj₁ x) = inject+ (count T) (toFin {S} x)
-- toFin {S `⊎ T} (inj₂ y) = raise (count S) (toFin {T} y)
-- toFin {S `× T} (x , y) = fconcat (toFin {S} x) (toFin {T} y)
-- toFin {`Σ S T} (x , y) = ?

--------------------------------------------------------------------------------

`two : Type 2
`two = `⊤ `⊎ `⊤

`four : Type 4
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`even : Fin 4 → ∃ Type
`even zero = _ , `⊤
`even (suc zero) = _ , `⊥
`even (suc (suc zero)) = _ , `⊤
`even (suc (suc (suc zero))) = _ , `⊥
`even (suc (suc (suc (suc ()))))

`∃even : Type 2
`∃even = `Σ `four `even
