module Bij2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec hiding ( map ; sum )
open import Relation.Binary.PropositionalEquality

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

map : ∀ {n} {A : Set} {B : Set} →
      (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sum : ∀ {n} → Vec ℕ n → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

postulate
  lemma : {n : ℕ}{A : Set} (f : A → ℕ) (a : A) (xs : Vec A n) →
    f a ≡ (sum (map f xs))

data Type : ℕ → Set
El : ∀ {n} → Type n → Set
enum : ∀ {n} (R : Type n) → Vec (El R) n

Σ[_] : ∀ {m} {S : Type m} (f : El S → Σ ℕ Type) → ℕ
Σ[_] {S = S} f = sum (map (λ s → proj₁ (f s)) (enum S))

data Type where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m + n)
  _`×_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m * n)
  -- _`→_ : ∀ {m n} (S : Type m) (T : Type n) → Type (n ^ m)
  `Σ : ∀ {m} (S : Type m) (T : El S → Σ ℕ Type) → Type (m * Σ[ T ])
  -- Type (m * Σ[ T ])
  -- `Π : ∀ {m} (S : Type m) (T : El S → Σ ℕ λ n → Type n) → Type 0

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
-- El (S `→ T) = El S → El T
El (`Σ S T) = Σ[ s ∶ El S ] El (proj₂ (T s))
-- El (`Π S T) = (s : El S) → El (proj₂ (T s))

-- postulate
--   lemma : ∀ {n} → (s : Type n) (t : El s)
--     (proj₁ (T s)) != (sum (map (λ s → proj₁ (T s)) (enum S)))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = {!!}
  where
  -- f : (s : El S) → Vec (El (proj₂ (T s))) (proj₁ (T s))
  -- f s = enum (proj₂ (T s))

  -- concat (map {!f2!} (enum S))
  -- goal = El S       → Vec (Σ (El S) (λ s' → El (proj₂ (T s'))))    (sum (map (λ s → proj₁ (T s)) (enum S)))
  -- have = (s : El S) → Vec (Σ (El S) (λ s' → El (proj₂ (T s'))))    (                proj₁ (T s)           )

  f2 : (s : El S) → Vec (Σ (El S) (λ s' → El (proj₂ (T s')))) (proj₁ (T s))
  f2 s = map (_,_ s) (enum (proj₂ (T s)))
-- enum (`Σ S T) = concat (map {!!} (enum S)) where
--   f : (s : El S) → Vec (El (proj₂ (T s))) (Σ[_] {S = S} T)
--   f s = {!!} -- enum (proj₂ (T s))





