module Algebraic where

-- (1 + 1) * (1 + 1 + 1) = (1 + 1 + 1 + 1 + 1 + 1)

infixr 4 _`+_

data U : Set where
  `f `0 `1 : U
  _`+_ : (a b : U) → U
  -- _`*_ : (a b : U) → U
  -- `μ : (a : U) → U

data Alg : U → Set where
  `0 : Alg `0
  `1 : Alg `1
  `f : Alg `f

  _`a*0_ : ∀ {a} →
    Alg a → Alg `0 →
    Alg `0

  _`0*b_ : ∀ {b} →
    Alg `0 → Alg b →
    Alg `0
  
  _`1+f_ :
    Alg `1 → Alg `f →
    Alg (`1 `+ `f)

  _`1+1_ :
    Alg `1 → Alg `1 →
    Alg (`1 `+ `1)

  -- _`1+b+c_ : ∀ {b c} →
  --   Alg `1 → Alg (b `+ c) →
  --   Alg (`1 `+ b `+ c)

  _`1+b+c_ : ∀ {b c} →
    Alg (b `+ c) →
    Alg (`1 `+ b `+ c)

  _`f+b+c_ : ∀ {b c} →
    Alg `f → Alg (b `+ c) →
    Alg (`f `+ b `+ c)

test : Alg (`1 `+ `1 `+ `1 `+ `1)
test = `1 `1+b+c (`1 `1+b+c (`1 `1+1 `1))

test₂ : Alg (`1 `+ `f `+ `1 `+ `1)
test₂ = `1 `1+b+c (`f `f+b+c (`1 `1+1 `1))

toAlg : (u : U) → Alg u
toAlg `f = `f
toAlg `0 = `0
toAlg `1 = `1
toAlg (`f `+ b) = {!!}
toAlg (`0 `+ b) = {!!}
toAlg (`1 `+ b) = {!!}
toAlg ((a `+ b) `+ b') = {!!}









-- data Alg : U → Set where
--   `0 : Alg `0
--   `1 : Alg `1
  
--   _`0+_ : ∀ {b} →
--     Alg `0 → Alg b →
--     Alg b

--   _`+0_ : ∀ {a} →
--     Alg a → Alg `0 →
--     Alg a
