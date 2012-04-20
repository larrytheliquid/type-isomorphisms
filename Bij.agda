module Bij where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Fin hiding ( _+_ )
open import Relation.Binary.PropositionalEquality

concat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
concat {zero} {n} () j
concat {suc m} {zero} zero ()
concat {suc m} {suc n} zero j = inject+ (m * suc n) j
concat {suc m} {n} (suc i) j = raise n (concat i j)

--------------------------------------------------------------------------------

data Type : ℕ → Set where
  `0 : Type 0
  `1 : Type 1

  _`+_ : ∀ {x y}
    (S : Type x) (T : Type y) →
    Type (x + y)

  _`*_ : ∀ {x y}
    (S : Type x) (T : Type y) →
    Type (x * y)

⟦_⟧ : ∀ {n} → Type n → Set
⟦ `0 ⟧ = ⊥
⟦ `1 ⟧ = ⊤
⟦ S `+ T ⟧ = ⟦ S ⟧ ⊎ ⟦ T ⟧
⟦ S `* T ⟧ = ⟦ S ⟧ × ⟦ T ⟧

toFin : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
toFin {.0} {`0} ()
toFin {.1} {`1} tt = zero
toFin {.(x + y)} {_`+_ {x} {y} S T} (inj₁ a)
  with toFin {x} {S} a
... | ih = inject+ y ih
toFin {.(x + y)} {_`+_ {x} {y} S T} (inj₂ b)
  with toFin {y} {T} b
... | ih = raise x ih
toFin {.(x * y)} {_`*_ {x} {y} S T} (a , b)
  with toFin {x} {S} a | toFin {y} {T} b
... | ih₁ | ih₂ = concat ih₁ ih₂

toFin′ : ∀ {n} (F : Type n) → ⟦ F ⟧ → Fin n
toFin′ F ⟦F⟧ = toFin {F = F} ⟦F⟧

syntax toFin′ F ⟦F⟧ = ⟦F⟧ ∶ F

--------------------------------------------------------------------------------

`ThreeL = `1 `+ (`1 `+ `1)
`ThreeR = (`1 `+ `1) `+ `1

2:ThreeL : ⟦ `ThreeL ⟧
2:ThreeL = inj₂ (inj₁ tt)

2:ThreeR : ⟦ `ThreeR ⟧
2:ThreeR = inj₁ (inj₂ tt)

2:ThreeL≡2:ThreeR : (2:ThreeL ∶ `ThreeL) ≡ (2:ThreeR ∶ `ThreeR)
2:ThreeL≡2:ThreeR = refl








