module VecStuff where
open import Data.Nat
open import Data.Vec

-- _+_ : ℕ → ℕ → ℕ
-- zero  + n = n
-- suc m + n = suc (m + n)

-- _++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
-- []       ++ ys = ys
-- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- _*_ : ℕ → ℕ → ℕ
-- zero  * n = zero
-- suc m * n = n + m * n
  
-- concat : ∀ {a m n} {A : Set a} →
--          Vec (Vec A n) m → Vec A (m * n)
-- concat []         = []
-- concat (xs ∷ xss) = xs ++ concat xss

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)
-- container vec is m, and recursion is its contents

image : ∀ {n} {A : Set} →
      (m : ℕ) →
      (Vec A n) →
      Vec (Vec A m) (n ^ m)
image zero xs = [] ∷ []
image (suc n) xs = concat (map (λ x → map (_∷_ x) (image n xs)) xs)

wut : ∀ {m n} {A : Set} →
  A → Vec (Vec A m) n → Vec A (n ^ m)
wut a [] = {!!}
wut a (x ∷ xs) = {!!}


-- group : ∀ {A : Set} m n (xs : Vec A (m * n)) → Vec (Vec A n) m

-- cluster : ∀ {A : Set} m n (xs : Vec A (n ^ m)) → Vec (Vec A k) n
