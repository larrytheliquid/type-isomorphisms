module MonomialPolys where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List hiding ( [_] )
open import Relation.Binary.PropositionalEquality

_[+]_ : List ℕ → List ℕ → List ℕ
[] [+] ys = ys
xs [+] [] = xs
(x ∷ xs) [+] (y ∷ ys) = x + y ∷ xs [+] ys

_[[+]]_ : List (List ℕ) → List (List ℕ) → List (List ℕ)
[] [[+]] ys = ys
xs [[+]] [] = xs
(xs ∷ xss) [[+]] (ys ∷ yss) = xs [+] ys ∷ xss [[+]] yss

[[μ]] : List (List ℕ) → List (List ℕ)
[[μ]] xss = xss

--------------------------------------------------------------------------------

data Type : List (List ℕ) → Set where
  `⊥ : Type ((0 ∷ []) ∷ [])
  `⊤ : Type ((1 ∷ []) ∷ [])
  `X : Type ((0 ∷ []) ∷ (1 ∷ []) ∷ [])
  _`⊎_ : ∀ {xss yss} (S : Type xss) (T : Type yss) → Type (xss [[+]] yss)
  `μ : ∀ {xss} → Type xss → Type ([[μ]] xss)

El : ∀ {xss} → Type xss → Set → Set
data μ {xss} (R : Type xss) : Set

El `⊥ X = ⊥
El `⊤ X = ⊤
El (S `⊎ T) X = El S X ⊎ El T X
El `X X = X
El (`μ R) X = μ R

data μ {xss} R where
  [_] : El R (μ R) → μ R

--------------------------------------------------------------------------------

`ℕ : Type ((1 ∷ []) ∷ (1 ∷ []) ∷ [])
`ℕ = `⊤ `⊎ `X

-- ((2 ∷ []) ∷ (1 ∷ []) ∷ [])
-- ((1 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ [])
`Maybeℕ : Type _
`Maybeℕ = `⊤ `⊎ `μ `ℕ
