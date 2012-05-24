module FiniteInductive where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

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

W[_]_ : ∀ {n} {A : Set} → Vec A n → (A → ℕ) → ℕ
W[ [] ] f = zero
W[ x ∷ xs ] f = f x + W[ xs ] f

data W (S : Set) (T : S → ℕ → Set) : Set where
  _,_ : ∀ {n} (s : S) → (T s n → W S T) → W S T

data Type : ℕ → Set
El : ∀ {n} → Type n → Set
enum : ∀ {n} (R : Type n) → Vec (El R) n

data Type where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) →
    Type (m + n)
  _`×_ : ∀ {m n} (S : Type m) (T : Type n) →
    Type (m * n)
  `W : ∀ {n} (S : Type n) (T : El S → ∃ Type) →
    Type (W[ enum S ] (λ s → proj₁ (T s)))

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`W S T) = {!!} -- W (El S) (λ s → El (proj₂ (T s)))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`W S T) = {!!}
