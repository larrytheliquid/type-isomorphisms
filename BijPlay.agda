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

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S

postulate toFin : {R : Type} → El R → Fin (count R)

toλ : ∀ {S T} → Vec (El S × El T) (count S) → El S → El T
toλ {S} xys x = proj₂ (lookup (toFin {S} x) xys)

wut : ∀ {S T} → Vec (El T) (count S) → El S → El T
wut {`⊥} ys ()
wut {`⊤} (x ∷ []) tt = x
wut {S `⊎ T} {T′} ys (inj₁ a) = wut {S} {T′} (take (count S) ys) a
wut {S `⊎ T} {T′} ys (inj₂ b) = wut {T} {T′} (drop (count S) ys) b
wut {S `× T} {T′} ys (a , b) with group (count S) (count T) ys
wut {S `× T} .(concat xss) (a , b) | xss , refl = {!!} -- wut (concat xss) (a , b)
wut {S `→ T} {T′} ys x = {!!}

enum : (R : Type) → Vec (El R) (count R)
enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = map (toλ {S} {T}) (graph (enum S) (enum T))


