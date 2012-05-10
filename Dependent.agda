module Dependent where
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Data.Product

-- data Type (I : Set) : Set₁
-- ⟦_⟧ : {I : Set} → Type I → (I → Set) → Set

-- data Type I where
--   `1 : Type I
--   `# : ℕ → Type I
--   `X : (i : I) → Type I
--   _`×_ : (l r : Type I) → Type I
--   _`+_ : (l r : Type I) → Type I
--   `Σ : (S : Type I)(X : I → Set)(T : ⟦ S ⟧ X → Type I) → Type I

-- ⟦ `1 ⟧ X = ⊤
-- ⟦ `# n ⟧ X = Fin n
-- ⟦ `X i ⟧ X = X i
-- ⟦ T `× T' ⟧ X = ⟦ T ⟧ X × ⟦ T' ⟧ X
-- ⟦ T `+ T' ⟧ X = ⟦ T ⟧ X ⊎ ⟦ T' ⟧ X
-- ⟦ `Σ S Χ T ⟧ X =  Σ[ s ∶ ⟦ S ⟧ Χ ] ⟦ T s ⟧ X

data Type (I : Set) : Set₁
⟦_⟧ : {I : Set} → Type I → (I → Set) → Set
-- data μ {I : Set} (S : Type I) (X : I → Set) : Set

data Type I where
  `1 : Type I
  `# : ℕ → Type I
  `X : (i : I) → Type I
  _`×_ : (l r : Type I) → Type I
  _`+_ : (l r : Type I) → Type I
  `Σ : (S : Type I)(T : {X : I → Set} → ⟦ S ⟧ X → Type I) → Type I
  -- `μ : (S : Type I) → Type I

⟦ `1 ⟧ X = ⊤
⟦ `# n ⟧ X = Fin n
⟦ `X i ⟧ X = X i
⟦ T `× T' ⟧ X = ⟦ T ⟧ X × ⟦ T' ⟧ X
⟦ T `+ T' ⟧ X = ⟦ T ⟧ X ⊎ ⟦ T' ⟧ X
⟦ `Σ S T ⟧ X = Σ[ s ∶ ⟦ S ⟧ X ] ⟦ T s ⟧ X
-- ⟦ `μ S ⟧ X = μ S X

-- data μ {I} S X where
--   con : ⟦ S ⟧ (μ S) → μ S X
