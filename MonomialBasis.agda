module MonomialBasis where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List
open import Relation.Binary.PropositionalEquality

data W (S : Set) (T : S → Set) : Set where
  _,_ : (s : S) → (T s → W S T) → W S T

-- zipWith but preserve longer list
combine : (ℕ → ℕ → ℕ) → List ℕ → List ℕ → List ℕ
combine f [] ys = ys
combine f xs [] = xs
combine f (x ∷ xs) (y ∷ ys) = f x y ∷ combine f xs ys

poly : (xs : List ℕ) → List ℕ
poly [] = []
poly (x ∷ xs) = {!!}

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ `W : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)
El (`W S T) = W (El S) λ s → El (T s)

enum : (R : Type) → List (El R)
enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = concat (map (λ s → map (_,_ s) (enum (T s))) (enum S))
enum (`W S T) = {!!}

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (`Σ S T) = sum (map (λ s → count (T s)) (enum S))
count (`W S T) with map (λ s → count (T s)) (enum S)
... | ih = {!!}

mon : Type → List ℕ
mon `⊥ = 0 ∷ []
mon `⊤ = 1 ∷ []
mon (S `⊎ T) = combine _+_ (mon S) (mon T)
mon (S `× T) = combine _*_ (mon S) (mon T)
mon (`Σ S T) with map (λ s → mon (T s)) (enum S)
... | ih = foldr (combine _+_) [] ih
mon (`W S T) with map (λ s → mon (T s)) (enum S)
... | ih = {!!}




