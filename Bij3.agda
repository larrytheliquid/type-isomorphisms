module Bij3 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.List
open import Relation.Binary.PropositionalEquality

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

enum : (R : Type) → List (El R)
enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = concat (map (λ s → map (_,_ s) (enum (T s))) (enum S))

Σ[_⊢_] : (R : Type) (f : El R → ℕ) → ℕ
Σ[ R ⊢ f ] = sum (map f (enum R))

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (`Σ S T) = count S * Σ[ S ⊢ (λ s → count (T s)) ]

--------------------------------------------------------------------------------

`four : Type
`four = `⊤ `⊎ (`⊤ `⊎ (`⊤ `⊎ `⊤))

`eight : Type
`eight = `four `⊎ `four

`0 : El `four
`0 = (inj₁ tt)
`1 : El `four
`1 = (inj₂ (inj₁ tt))
`2 : El `four
`2 = (inj₂ (inj₂ (inj₁ tt)))
`3 : El `four
`3 = (inj₂ (inj₂ (inj₂ tt)))

`even : El `four → Type
`even (inj₁ tt) = `⊤
`even (inj₂ (inj₁ tt)) = `⊥
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥

`odd : El `four → Type
`odd (inj₁ tt) = `⊥
`odd (inj₂ (inj₁ tt)) = `⊤
`odd (inj₂ (inj₂ (inj₁ tt))) = `⊥
`odd (inj₂ (inj₂ (inj₂ tt))) = `⊤

2even : El (`even `2)
2even = tt

3odd : El (`odd `3)
3odd = tt

`∃even : Type
`∃even = `Σ `four `even

`∃odd : Type
`∃odd = `Σ `four `odd

∃even⇔∃odd : count `∃even ≡ count `∃odd
∃even⇔∃odd = refl

∃even⇔eight : count `∃even ≡ count `eight
∃even⇔eight = refl

∃even : El `∃even
∃even = `2 , tt

∃odd : El `∃odd
∃odd = `3 , tt
