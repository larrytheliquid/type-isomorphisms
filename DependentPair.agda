module DependentPair where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

sumWith : ∀ {n} {A : Set} → (A → ℕ) → Vec A n → ℕ
sumWith f [] = zero
sumWith f (x ∷ xs) = f x + sumWith f xs

postulate
  Πconcat : ∀ {n} {A : Set} {B : A → Set} →
    (f : A → ℕ) (xs : Vec A n) (ys : (a : A) →
    Vec (B a) (f a)) →
    Vec (Σ A B) (sumWith f xs)

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

count : Type → ℕ
enum : (R : Type) → Vec (El R) (count R)

count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (`Σ S T) = sumWith (λ s → count (T s)) (enum S)

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = Πconcat (λ s → count (T s)) (enum S) (λ s → enum (T s))

--------------------------------------------------------------------------------

`four : Type
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`even : El `four → Type
`even (inj₁ tt) = `⊤
`even (inj₂ (inj₁ tt)) = `⊥
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥

`∃even : Type
`∃even = `Σ `four `even
