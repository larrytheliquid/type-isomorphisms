module WPoly where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

Uncurry : ℕ → Set → Set
Uncurry zero A = ⊤
Uncurry (suc n) A = A × Uncurry n A

W₁[_]_ : ∀ {n} {A : Set} → Vec A n → (A → ℕ) → ℕ
W₁[ [] ] f = zero
W₁[ x ∷ xs ] f with f x
... | zero = suc (W₁[ xs ] f)
... | suc n = W₁[ xs ] f

W₂[_]_ : ∀ {n} {A : Set} → Vec A n → (A → ℕ) → ℕ
W₂[ [] ] f = zero
W₂[ x ∷ xs ] f with f x
... | zero = W₂[ xs ] f
... | suc n = suc n + W₂[ xs ] f

data W (S : Set) (T : S → Set) : Set where
  _,_ : (s : S) → (T s → W S T) → W S T

data Type : ℕ → ℕ → Set
El : ∀ {n x} → Type n x → Set
postulate
  enum : ∀ {n x} (R : Type n x) → Vec (El R) n -- axioms
  enum₂ : ∀ {n x} (R : Type n x) → Uncurry x (El R) → El R -- inference rules

data Type where
  `⊥ : Type 0 0 
  `⊤ : Type 1 0
  _`⊎_ : ∀ {m n x y} (S : Type m x) (T : Type n y) →
    Type (m + n) (x + y)
  _`×_ : ∀ {m n x y} (S : Type m x) (T : Type n y) →
    Type (m * n) (x * y)
  `W : ∀ {n x} (S : Type n x) (T : El S → ∃₂ Type) →
    Type (W₁[ enum S ] (λ s → proj₁ (T s))) (W₂[ enum S ] (λ s → proj₁ (proj₂ (T s))))

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`W S T) = W (El S) (λ s → El (proj₂ (proj₂ (T s))))

