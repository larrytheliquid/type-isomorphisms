module Containers where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Data.Container
open import Relation.Binary.PropositionalEquality

data Type : Set
El : Type → (X : Set) → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type
  `Σ `Π `W : (S : Type)(T : El S → Type) → Type

El `⊥ X = ⊥
El `⊤ X = ⊤
El (S `⊎ T) X = El S ⊎ El T
El (S `× T) X = El S × El T
El (S `→ T) X = El S → El T
El (`Σ S T) X = Σ[ s ∶ El S ] El (T s)
El (`Π S T) X = (s : El S) → El (T s)
El (`W S T) X = {!!} -- W (El S) λ s → El (T s)
