module Bij2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

data Type : ℕ → Set
El : ∀ {n} → Type n → Set

data Type where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m + n)
  _`×_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m * n)
  _`→_ : ∀ {m n} (S : Type m) (T : Type n) → Type (n ^ m)
  -- `Σ : ∀ {m n} (S : Type m) (T : El S → Type n) → Type 0
  `Σ : ∀ {m} (S : Type m) (f : El S → ℕ) (T : (m′ : El S) → Type (f m′)) → Type 0
  -- `Σ : ∀ {m} (S : Type m) (T : El S → Σ ℕ λ n → Type n) → Type 0
  `Π : ∀ {m} (S : Type m) (T : El S → Σ ℕ λ n → Type n) → Type 0

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
El (`Σ S f T) = {!!}
-- El (`Σ S T) = Σ[ s ∶ El S ] El (proj₂ (T s))
El (`Π S T) = (s : El S) → El (proj₂ (T s))

`bool : Type 2
`bool = `⊤ `⊎ `⊤

`unit : Type 1
`unit = `bool `→ `⊤

`tt : El `unit
`tt (inj₁ tt) = tt
`tt (inj₂ tt) = tt
