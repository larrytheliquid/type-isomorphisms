module Bij where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Fin hiding ( _+_ )

concat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
concat {zero} {n} () j
concat {suc m} {zero} zero ()
concat {suc m} {suc n} zero j = inject+ (m * suc n) j
concat {suc m} {n} (suc i) j = raise n (concat i j)

data U : ℕ → Set where
  `0 : U 0
  `1 : U 1

  _`+_ : ∀ {x y}
    (S : U x) (T : U y) →
    U (x + y)

  _`*_ : ∀ {x y}
    (S : U x) (T : U y) →
    U (x * y)

El : ∀ {n} → U n → Set
El `0 = ⊥
El `1 = ⊤
El (S `+ T) = El S ⊎ El T
El (S `* T) = El S × El T

toFin : ∀ {n} {F : U n} → El F → Fin n
toFin {.0} {`0} ()
toFin {._} {`1} tt = zero
toFin {.(x + y)} {_`+_ {x} {y} S T} (inj₁ a)
  with toFin {x} {S} a
... | ih = inject+ y ih
toFin {.(x + y)} {_`+_ {x} {y} S T} (inj₂ b)
  with toFin {y} {T} b
... | ih = raise x ih
toFin {.(x * y)} {_`*_ {x} {y} S T} (a , b)
  with toFin {x} {S} a | toFin {y} {T} b
... | ih₁ | ih₂ = concat ih₁ ih₂







