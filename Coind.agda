module Coind where
open import Coinduction
open import Data.Conat
open import Data.Nat using (ℕ; zero; suc)

_*_ : Coℕ → Coℕ → Coℕ
zero  * n = n
suc m * n = ♭ m + n -- suc (♯ (♭ m + n))
