module Bij2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product

data Type : ℕ → Set
El : ∀ {n} → Type n → Set

data Type where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m + n)
  _`×_ _`→_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m * n)
  -- `Π : ∀ {m n} (S : Type m)(T : El S → Type n) → Type 0
  -- `Σ : ∀ {m n} (S : Type m) (T : El S → Type n) → Type 0

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
-- El (`Π S T) = (s : El S) → El (T s)
-- El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

`bool : Type 2
`bool = `⊤ `⊎ `⊤

`light : Type 2
`light = `bool `→ `⊤

`on+off : El `light
`on+off (inj₁ tt) = tt
`on+off (inj₂ tt) = tt
