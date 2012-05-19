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

∣Σ∣ : ∀ {n} (f : Fin n → ℕ) → ℕ
∣Σ∣ {n} f = sum (map f (allFin n))

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
    Type (∣Σ∣ λ s → proj₁ (T s))

El : ∀ {n} → Type n → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ {n} S T) = Σ[ i ∶ Fin n ] El (proj₂ (T i))

toFin : ∀ {n} {R : Type n} → El R → Fin n
toFin {R = `⊥} ()
toFin {R = `⊤} tt = zero
toFin {R = S `⊎ T} (inj₁ s) = inject+ _ (toFin {R = S} s)
toFin {R = _`⊎_ {m} S T} (inj₂ t) = raise m (toFin {R = T} t)
toFin {R = S `× T} (s , t) = fconcat (toFin {R = S} s) (toFin {R = T} t)
toFin {R = `Σ S T} (s , t) with toFin {R = proj₂ (T s)} t
... | ih = {!!}

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
