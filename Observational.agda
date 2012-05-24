module Observational where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Sig (S : Set) (T : S → Set) : Set where
  _,_ : (s : S) → T s → Sig S T

Π : (S : Set) (T : S → Set) → Set
Π S T = (s : S) → T s

data V (S : Set) (T : Set) : Set where
  _,_ : (s : S) → (T → V S T) → V S T

data W (S : Set) (T : S → Set) : Set where
  _,_ : (s : S) → (T s → W S T) → W S T

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type
  `V : (S T : Type) → Type
  `Σ `Π `W : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
El (`V S T) = V (El S) (El T)
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)
El (`Π S T) = (s : El S) → El (T s)
El (`W S T) = W (El S) λ s → El (T s)

--------------------------------------------------------------------------------

`Bool : Type
`Bool = `⊤ `⊎ `⊤

`true : El `Bool
`true = inj₁ tt

`false : El `Bool
`false = inj₂ tt

`if_then_else_ : El `Bool → Type → Type → Type
`if inj₁ tt then x else y = x
`if inj₂ tt then x else y = y

`T : (b : El `Bool) → Type
`T b = `if b then `⊤ else `⊥

`Light : Type
`Light = `W `Bool (λ _ → `⊥)

`on : El `Light
`on = `true , λ()

`off : El `Light
`off = `false , λ()

`ℕ : Type
`ℕ = `W `Bool `T

`zero : El `ℕ
`zero = `false , λ ()

`suc : El `ℕ → El `ℕ
`suc n = `true , λ _ → n
