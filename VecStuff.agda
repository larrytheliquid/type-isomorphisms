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

exp : ∀ {m} {A : Set} →
      (Vec A m) →
      (n : ℕ) →
      Vec (Vec A m) (m ^ n)
exp xs zero = xs ∷ []
exp xs (suc n) = concat (map (λ _ → exp xs n) xs)

-- maybe pass an A and nest a function taking A's?
-- exp [] = (λ()) ∷ []
-- exp (x ∷ xs) = {!!}


