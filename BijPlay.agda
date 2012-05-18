{-# OPTIONS --no-positivity-check #-}
module BijPlay where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec hiding ( [_] )
open import Relation.Binary.PropositionalEquality

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

graph : ∀ {m n} {A B : Set} →
      (Vec A m) →
      (Vec B n) →
      Vec (Vec (A × B) m) (n ^ m)
graph [] ys = [] ∷ []
graph (x ∷ xs) ys = concat (map (λ y → map (_∷_ (x , y)) (graph xs ys)) ys)

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set
data ⟦_⟧ (R : Type) : Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = ⟦ S ⟧ ⊎ ⟦ T ⟧
El (S `× T) = ⟦ S ⟧ × ⟦ T ⟧
El (S `→ T) = ⟦ S ⟧ → ⟦ T ⟧

data ⟦_⟧ R where
  [_] : El R → ⟦ R ⟧

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S

toλ : ∀ {S T} → Vec ⟦ T ⟧ (count S) → ⟦ S ⟧ → ⟦ T ⟧
toλ {`⊥} ys [ () ]
toλ {`⊤} (x ∷ []) [ tt ] = x
toλ {S `⊎ T} ys [ inj₁ a ] = toλ (take (count S) ys) a
toλ {S `⊎ T} ys [ inj₂ b ] = toλ (drop (count S) ys) b
toλ {S `× T} ys [ a , b ] with group (count S) (count T) ys
... | xss , p = toλ (map (λ xs → toλ xs b) xss) a
toλ {S `→ T} ys [ x ] = {!!}

enum : (R : Type) → Vec ⟦ R ⟧ (count R)
enum `⊥ = []
enum `⊤ = [ tt ] ∷ []
enum (S `⊎ T) = map (λ s → [ inj₁ s ]) (enum S) ++ map (λ t → [ inj₂ t ]) (enum T)
enum (S `× T) = concat (map (λ s → map (λ t → [ (s , t) ]) (enum T)) (enum S))
enum (S `→ T) with graph (enum S) (enum T)
... | hm = map (λ g → [ toλ (map proj₂ g) ]) hm



