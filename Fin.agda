module Fin where
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n
