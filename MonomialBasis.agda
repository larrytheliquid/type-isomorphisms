module MonomialBasis where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List
open import Relation.Binary.PropositionalEquality

0+x : List ℕ
0+x = 0 ∷ 2 ∷ []

1+x : List ℕ
1+x = 1 ∷ 2 ∷ []

3+8x : List ℕ
3+8x = 3 ∷ 8 ∷ []

Curry : ℕ → Set → Set
Curry zero A = A
Curry (suc n) A = A → Curry n A

Cons : Set → List ℕ → Set
Cons A [] = ⊤
Cons A (x ∷ xs) = Cons A xs × Curry (length (x ∷ xs)) A

data W (S : Set) (T : S → Set) : Set where
  _,_ : (s : S) → (T s → W S T) → W S T

Σconcat : {A : Set} {B : A → Set} →
  (xs : List A)
  (g : (a : A) → List (B a)) →
  List (Σ A B)
Σconcat [] g = []
Σconcat (x ∷ xs) g = map (_,_ x) (g x) ++ Σconcat xs g

_[+]_ : List ℕ → List ℕ → List ℕ
[] [+] ys = ys
xs [+] [] = xs
(x ∷ xs) [+] (y ∷ ys) = x + y ∷ xs [+] ys

_[*]_ : List ℕ → List ℕ → List ℕ
[] [*] ys = []
(x ∷ xs) [*] ys = map (_*_ x) ys [+] (xs [*] (zero ∷ ys))

[Σ] : {A : Set} → List A → (A → List ℕ) → List ℕ
[Σ] [] f = []
[Σ] (x ∷ xs) f = f x [+] [Σ] xs f

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ : (S : Type)(T : El S → Type) → Type
  -- `Σ : (S : Type)(T : ((El S ⊎ (El S → El S)) → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S T) = Σ[ s ∶ El S ] El (T s)

enum : (R : Type) → List (El R)
enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = Σconcat (enum S) (λ s → enum (T s))

-- enum₂ : (R : Type) → List (El R → El R)
-- enum₂ `⊥ = (λ()) ∷ []
-- enum₂ `⊤ = (λ {tt → tt}) ∷ []
-- enum₂ (R `⊎ R₁) = {!!}
-- enum₂ (R `× R₁) = {!!}
-- enum₂ (`Σ R T) = {!!}

mon : Type → List ℕ
mon `⊥ = 0 ∷ []
mon `⊤ = 1 ∷ []
mon (S `⊎ T) = mon S [+] mon T
mon (S `× T) = mon S [*] mon T
mon (`Σ S T) = [Σ] (enum S) (λ s → mon (T s))

-- count : Type → ℕ
-- count `⊥ = 0
-- count `⊤ = 1
-- count (S `⊎ T) = count S + count T
-- count (S `× T) = count S * count T
-- count (`Σ S T) = sum (map (λ s → count (T s)) (enum S))
-- count (`W S T) with map (λ s → count (T s)) (enum S)
-- ... | ih = {!!}
