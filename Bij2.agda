module Bij2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

Σ[_]_ : (ℕ → ℕ) → ℕ → ℕ
Σ[ f ] zero = 0
Σ[ f ] suc n = f n + Σ[ f ] n

-- postulate
--   toFin : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
--   inject : ∀ {n} (F : Type n) → Fin n → ⟦ F ⟧
--   enum : ∀ {n} (F : Type n) → Vec ⟦ F ⟧ n

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
  -- `Π : ∀ {m} (S : Type m) (T : El S → Σ ℕ λ n → Type n) → Type 0

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
-- El (S `→ T) = El S → El T
El (`Σ S T) = Σ[ s ∶ El S ] El (proj₂ (T s))
-- El (`Π S T) = (s : El S) → El (proj₂ (T s))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = concat (map ? (enum S)) where
  -- -- f s = map (λ t → s , t) (enum (proj₂ (T s)))
  -- f : (s : El S) → Vec (Σ[ s' ∶ El S ] El (proj₂ (T s'))) (Σ[_] {S = S} T)
  -- f s = map (_,_ s) (enum (proj₂ (T s)))

  f : (s : El S) → Vec (El (proj₂ (T s))) (Σ[_] {S = S} T)
  f s = enum (proj₂ (T s))





