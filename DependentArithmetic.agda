module DependentArithmetic where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

Σ+ : ∀ {n} {A : Set} → Vec A n → (A → ℕ) → ℕ
Σ+ [] f = zero
Σ+ (x ∷ xs) f = f x + Σ+ xs f

fconcat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
fconcat {zero} {n} () j
fconcat {suc m} {zero} zero ()
fconcat {suc m} {suc n} zero j = inject+ _ j
fconcat {suc m} {n} (suc i) j = raise n (fconcat i j)

fimage : ∀ {m n} → Vec (Fin n) m → Fin (n ^ m)
fimage [] = zero
fimage (x ∷ xs) = fconcat x (fimage xs)

Σfconcat : ∀ {n} {A : Set}
  (f : A → ℕ) (xs : Vec A n)
  (i : Fin n) (j : Fin (f (lookup i xs))) →
  Fin (Σ+ xs f)
Σfconcat f [] () j
Σfconcat f (x ∷ xs) zero j = inject+ (Σ+ xs f) j
Σfconcat f (x ∷ xs) (suc i) j = raise (f x) (Σfconcat f xs i j)

image : ∀ {n} {A : Set}
  (m : ℕ) → (Vec A n) →
  Vec (Vec A m) (n ^ m)
image zero xs = [] ∷ []
image (suc m) xs = concat (map (λ x → map (_∷_ x) (image m xs)) xs)

Σconcat : ∀ {n} {A : Set} {B : A → Set} →
  (f : A → ℕ) (xs : Vec A n) (g : (a : A) →
  Vec (B a) (f a)) →
  Vec (Σ A B) (Σ+ xs f)
Σconcat f [] g = []
Σconcat f (x ∷ xs) g = map (_,_ x) (g x) ++ Σconcat f xs g

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type
  `Σ : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

count : Type → ℕ
toFin : {R : Type} → El R → Fin (count R)
enum : (R : Type) → Vec (El R) (count R)

count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S
count (`Σ S T) = Σ+ (enum S) (λ s → count (T s))

postulate
  grr : ∀ {n} {A : Set}
    (f : A → ℕ) (a : A) (xs : Vec A n)
    (i : Fin n) (j : Fin (f a)) →
    Fin (Σ+ xs f)

-- grr f a [] () j
-- grr f a (x ∷ xs) zero j with f a
-- grr f a (x ∷ xs) zero () | zero
-- grr f a (x ∷ xs) zero j | suc _ with grr f a xs {!zero {_}!} _
-- ... | ih = {!!} -- raise (f x) ih
-- grr f a (x ∷ xs) (suc i) j = {!!}

toFin {`⊥} ()
toFin {`⊤} tt = zero
toFin {S `⊎ T} (inj₁ s) = inject+ (count T) (toFin {S} s)
toFin {S `⊎ T} (inj₂ t) = raise (count S) (toFin {T} t)
toFin {S `× T} (s , t) = fconcat (toFin {S} s) (toFin {T} t)
toFin {S `→ T} f = fimage (map (λ s → toFin {T} (f s)) (enum S))
toFin {`Σ S T} (s , t) with enum S | toFin {S} s | toFin {T s} t
... | xs | i | j = {!!} -- grr (λ x → (count (T x))) s xs i j

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = map (λ ts s → lookup (toFin {S} s) ts ) (image (count S) (enum T))
enum (`Σ S T) = Σconcat (λ s → count (T s)) (enum S) (λ s → enum (T s))


