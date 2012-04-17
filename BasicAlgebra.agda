module BasicAlgebra where

infixr 4 _`+_
infixr 4 _,_

data ⊥ : Set where

record ⊤ : Set where constructor tt

data _⊎_ (S T : Set) : Set where
  inj₁ : (s : S) → S ⊎ T
  inj₂ : (t : T) → S ⊎ T

record _×_ (S T : Set) : Set where
  constructor _,_
  field
    proj₁ : S
    proj₂ : T

data _==_ {X : Set}(x : X) : X → Set where
  refl : x == x

--------------------------------------------------------------------------------

data U : Set where
  `0 `1 : U
  _`+_ _`*_ : (S T : U) → U

simplify : U → U

simplify (`0 `* T) = `0
simplify (S `* `0) = `0

simplify (`0 `+ T) = T
simplify (S `+ `0) = S

simplify (`1 `* T) = T
simplify (S `* `1) = S

-- simplify ((S `+ T) `+ U) = S `+ (T `+ U)
-- simplify ((S `* T) `* U) = S `* (T `* U)

simplify F = F

El : U → Set
El `0       = ⊥
El `1       = ⊤
El (S `+ T) = El S ⊎ El T
El (S `* T) = El S × El T

-- sound : ∀ {u} → El u → El (simplify u)
-- sound {`0} ()
-- sound {`1} x = x

-- sound {`0 `+ T} (inj₁ ())
-- sound {`0 `+ T} (inj₂ t) = t

-- sound {`1 `+ `0} (inj₁ s) = s
-- sound {(S `+ T) `+ `0} (inj₁ s) = s
-- sound {S `* T `+ `0} (inj₁ s) = s
-- sound {S `+ `0} (inj₂ ())

-- sound {`1 `+ `1} x = x
-- sound {`1 `+ S `+ T} x = x
-- sound {`1 `+ S `* T} x = x
-- sound {(S `+ T) `+ `1} x = x
-- sound {(S `+ T) `+ S' `+ T'} x = x
-- sound {(S `+ T) `+ S' `* T'} x = x
-- sound {S `* T `+ `1} x = x
-- sound {S `* T `+ S' `+ T'} x = x
-- sound {S `* T `+ S' `* T'} x = x

-- sound {S `* T} x = {!!}
