module Semiring where
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding ( _+_ ; toℕ ; inject )
open import Data.Vec hiding ( [_] )
open import Relation.Binary.PropositionalEquality

data Semiring : ℕ → Set where
  -- `0 : Semiring 0
  `1 : Semiring 1

  _`+_ : ∀ {x y}
    (S : Semiring x) (T : Semiring y) →
    Semiring (x + y)

  _`*_ : ∀ {x y}
    (S : Semiring x) (T : Semiring y) →
    Semiring (x * y)

data ⟦_⟧ {A : Set} (a : A) : Set where
  [] : ⟦ a ⟧

toℕ : ∀ {n} → Semiring n → ℕ
-- toℕ `0 = 0
toℕ `1 = 1
toℕ (S `+ T) = toℕ S + toℕ T
toℕ (S `* T) = toℕ S * toℕ T

plus : ∀ {m n} → Fin m → Fin n → Fin (m + n)
plus {suc m} zero j = raise (suc m) j
plus (suc i) j = suc (plus i j)

times : ∀ {m n} → Fin m → Fin n → Fin (m * n)
times {zero} {n} () j
times {suc m} {zero} zero ()
times {suc m} {suc n} zero j = inject+ _ j
times {suc m} {n} (suc i) j = raise n (times i j)

toFin : ∀ {n} → Semiring n → Fin n
toFin `1 = zero
toFin (S `+ T) = plus (toFin S) (toFin T)
toFin (S `* T) = times (toFin S) (toFin T)

soundℕ : ∀ {n} (R : Semiring n) → toℕ R ≡ n
soundℕ `1 = refl
soundℕ (S `+ T) rewrite soundℕ S | soundℕ T = refl
soundℕ (S `* T) rewrite soundℕ S | soundℕ T = refl

soundℕ₂ : ∀ {n} (S T : Semiring n) → toℕ S ≡ toℕ T
soundℕ₂ S T rewrite soundℕ S | soundℕ T = refl

-- +-comm : ∀ {m n} (S : Semiring m) (T : Semiring n) →
--   S `+ T ≡ T `+ S
-- +-comm S T = ?

--------------------------------------------------------------------------------

toVec : ∀ {n} → Semiring n → Vec ⊤ n
-- toVec `0 = []
toVec `1 = tt ∷ []
toVec (S `+ T) = toVec S ++ toVec T
toVec (S `* T) = concat (map (λ _ → toVec T) (toVec S))

-- soundFin : ∀ {n} → (R : Semiring n) → toVec R ≡ replicate tt
-- soundFin `1 = refl
-- soundFin (S `+ T) rewrite soundFin S | soundFin T = {!!}
-- soundFin (S `* T) rewrite soundFin S | soundFin T = {!!}

