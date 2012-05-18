{-# OPTIONS --no-positivity-check #-}
module BijPlay2 where
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

image : ∀ {n} {A : Set} →
      (m : ℕ) →
      (Vec A n) →
      Vec (Vec A m) (n ^ m)
image zero xs = [] ∷ []
image (suc n) xs = concat (map (λ x → map (_∷_ x) (image n xs)) xs)
-- concat Vec (Vec A m) (n ^ m) = Vec A (n ^ m * m) = Vec A (m * n ^ m)
-- = Vec (Vec A (n ^ m)) m

postulate
  inv : ∀ {m n} {A : Set} →
        Vec (Vec A m) (n ^ m) →
        (Vec A n)

  wut : ∀ {m n} {A : Set} →
    Vec (Vec (Vec A m) m) n → Vec A (n ^ m)

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

postulate
  try : ∀ {m n} {A : Set} → Vec A (n ^ m) → Vec A n

toλ : ∀ {S T} → Vec ⟦ T ⟧ (count S) → ⟦ S ⟧ → ⟦ T ⟧
enum : (R : Type) → Vec ⟦ R ⟧ (count R)

toλ {`⊥} ys [ () ]
toλ {`⊤} (x ∷ []) [ tt ] = x
toλ {S `⊎ T} ys [ inj₁ a ] = toλ (take (count S) ys) a
toλ {S `⊎ T} ys [ inj₂ b ] = toλ (drop (count S) ys) b
toλ {S `× S₂} {T} ys [ a , b ] with group (count S) (count S₂) ys
-- ... | xss , p = toλ (map (λ xs → toλ xs b) xss) a
... | xss , p with map (λ xs → toλ xs b) xss
... | hm = {!!}
toλ {S `→ S₂} {T} ys [ f ] with enum S
... | ss with map f ss
... | ss' = {!!}

-- need: Vec (Vec ⟦ T ⟧ (count S)) (count S₂)

-- have: Vec ⟦ T ⟧ (count S₂ ^ count S)
-- try to get: (xs : Vec ⟦ T ⟧ (count S)) (b : ⟦ S ⟧)
-- then get: (ys : Vec ⟦ T ⟧ (count S₂)) (a : ⟦ S₂ ⟧)

-- try to get: (xs : Vec ⟦ T ⟧ (count S)) (b : Vec ⟦ S ⟧ k)


-- with map (λ s → toλ (try {count S} ys) (f s)) (enum S)
-- ... | hm = {!!}

-- with count S
-- ... | zero = head ys
-- ... | suc n with group (count S₂) (count S₂ ^ n) ys
-- ... | xss , p with map f (enum S)
-- ... | hm = {!!}

enum `⊥ = []
enum `⊤ = [ tt ] ∷ []
enum (S `⊎ T) = map (λ s → [ inj₁ s ]) (enum S) ++ map (λ t → [ inj₂ t ]) (enum T)
enum (S `× T) = concat (map (λ s → map (λ t → [ (s , t) ]) (enum T)) (enum S))
enum (S `→ T) = map (λ ts → [ toλ ts ]) (image (count S) (enum T))

