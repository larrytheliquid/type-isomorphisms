module Codomain where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.List
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Σ+ : {A : Set} → List A → (A → ℕ) → ℕ
Σ+ [] f = zero
Σ+ (x ∷ xs) f = f x + Σ+ xs f

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ : (S : Type)(Ts : List Type)(F : El S → ∃ (λ T → T ∈ Ts)) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S Ts F) = Σ[ s ∶ El S ] El (proj₁ (F s))

`four : Type
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`evenCo : List Type
`evenCo = `⊤ ∷ `⊥ ∷ `⊤ ∷ `⊥ ∷ []

`even : El `four → ∃ λ T → T ∈ `evenCo
`even (inj₁ tt) = `⊤ , here
`even (inj₂ (inj₁ tt)) = `⊥ , there here
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤ , there (there here)
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥ , there (there (there here))

`∃even : Type
`∃even = `Σ `four `evenCo `even
