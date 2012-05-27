module MonomialPoly where
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

_[*]_ : List ℕ → List ℕ → List ℕ
[] [*] ys = []
(x ∷ xs) [*] ys = map (_*_ x) ys [+] (xs [*] (zero ∷ ys))

--------------------------------------------------------------------------------

data Type : Set where
  `⊥ `⊤ `X : Type
  _`⊎_ _`×_ : (S T : Type) → Type

El : Type → Set → Set
El `⊥ X = ⊥
El `⊤ X = ⊤
El (S `⊎ T) X = El S X ⊎ El T X
El (S `× T) X = El S X × El T X
El `X X = X

data μ (F : Type) : Set where
  [_] : El F (μ F) → μ F

mon : Type → List ℕ
mon `⊥ = 0 ∷ []
mon `⊤ = 1 ∷ []
mon (S `⊎ T) = mon S [+] mon T
mon (S `× T) = mon S [*] mon T
mon `X = 0 ∷ 1 ∷ []

