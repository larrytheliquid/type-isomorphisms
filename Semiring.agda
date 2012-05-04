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

sound : ∀ {n} → (R : Semiring n) → toℕ R ≡ n
sound `1 = refl
sound (S `+ T) rewrite sound S | sound T = refl
sound (S `* T) rewrite sound S | sound T = refl

sound₂ : ∀ {n} → (S T : Semiring n) → toℕ S ≡ toℕ T
sound₂ S T rewrite sound S | sound T = refl

postulate
  toℕ[x]≡n : ∀ {n} → (R : Semiring n) → toℕ R ≡ n

toVec : ∀ {n} → Semiring n → Vec ⊤ n
-- toVec `0 = []
toVec `1 = tt ∷ []
toVec (S `+ T) = toVec S ++ toVec T
toVec (S `* T) = concat (map (λ _ → toVec T) (toVec S))

-- toFin : ∀ {n} {F : Semiring n} → ⟦ toVec F ⟧ → Fin n
-- toFin {F = `0} x = {!!}
-- toFin {F = `1} x = zero
-- toFin {F = S `+ T} x with toFin {F = S} [] | toFin {F = T} []
-- ... | xs | ys = {!!}
-- toFin {F = S `* T} x = {!!} -- times (toFin {F = S} []) (toFin {F = T} [])

