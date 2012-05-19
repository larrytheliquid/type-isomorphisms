module DependentPair where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

count : Type → ℕ
enum : (R : Type) → Vec (El R) (count R)

count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (`Σ S T) = count S * sum (map (λ s → count (T s)) (enum S))

postulate
  cheat : ∀ {S} {T : El S → Type} → (s : El S) →
    (count (T s)) ≡ (sum (map (λ s → count (T s)) (enum S)))

lemma : ∀ {S} {T : El S → Type} → (s : El S) →
  Vec (Σ[ s₁ ∶ El S ] El (T s₁)) (count (T s)) →
  Vec (Σ[ s₁ ∶ El S ] El (T s₁)) (sum (map (λ s → count (T s)) (enum S)))
lemma {S} {T} s xs rewrite cheat {S} {T} s = xs

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = concat (map (λ s → lemma {S} {T} s (map (_,_ s) (enum (T s)))) (enum S))
-- concat (map (λ s → {!!}) (enum S))
-- (map (λ s → {!(map (_,_ s) (enum (T s)))!}) (enum S))
-- enum (`Σ S T) = concat (map (λ s → lemma {S} {T} s (map (_,_ s) (enum (T s)))) (enum S))
-- with map (λ s → enum (T s)) (enum S)
-- ... | hm = ?

--------------------------------------------------------------------------------

`four : Type
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`even : El `four → Type
`even (inj₁ tt) = `⊤
`even (inj₂ (inj₁ tt)) = `⊥
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥

`∃even : Type
`∃even = `Σ `four `even
