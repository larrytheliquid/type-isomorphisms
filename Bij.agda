module Bij where
open import Data.Empty
open import Data.Unit hiding ( _≟_ )
open import Data.Nat hiding ( _≟_ )
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ ; lift ; inject )
open import Data.Fin.Props
open import Data.Vec hiding ( concat ; [_] )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PreorderReasoning
open import Function

concat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
concat {zero} {n} () j
concat {suc m} {zero} zero ()
concat {suc m} {suc n} zero j = inject+ (m * suc n) j
concat {suc m} {n} (suc i) j = raise n (concat i j)

case : ∀ {m} {n} → Fin (m + n) → Fin m ⊎ Fin n
case {zero} {n} i = inj₂ i
case {suc m} {n} zero = inj₁ zero
case {suc m} {n} (suc i) with case i
... | (inj₁ j) = inj₁ (suc j)
... | (inj₂ k) = inj₂ k

split : ∀ {m} {n} → Fin (m * n) → Fin m × Fin n
split {zero} {n} ()
-- TODO Fin (suc m) * 0 should be ⊥
split {suc m} {zero} i = zero , proj₂ (split {m} i)
split {suc m} {suc n} zero = zero , zero
split {suc m} {suc n} (suc i) with case i
... | (inj₁ j) = zero , suc j
... | (inj₂ k) with split k
... | (x , y) = suc x , y

--------------------------------------------------------------------------------

infix 5 [_]

data Type : ℕ → Set where
  `0 : Type 0
  `1 : Type 1

  _`+_ : ∀ {x y}
    (S : Type x) (T : Type y) →
    Type (x + y)

  _`*_ : ∀ {x y}
    (S : Type x) (T : Type y) →
    Type (x * y)

El : ∀ {n} → Type n → Set
data ⟦_⟧ {n} (F : Type n) : Set

El `0 = ⊥
El `1 = ⊤
El (S `+ T) = ⟦ S ⟧ ⊎ ⟦ T ⟧
El (S `* T) = ⟦ S ⟧ × ⟦ T ⟧

data ⟦_⟧ {n} F where
  [_] : El F → ⟦ F ⟧

toFin : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
toFin {F = `0} [ () ]
toFin {F = `1} [ tt ] = zero
toFin {F = S `+ T} [ inj₁ a ] = inject+ _ (toFin a)
toFin {F = _`+_ {x = x} S T} [ inj₂ b ] = raise x (toFin b)
toFin {F = S `* T} [ a , b ] = concat (toFin a) (toFin b)

∣_∣ : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
∣_∣ = toFin

case-raise : ∀ {n} m → (i : Fin n) →
  case {m = m} (raise m i) ≡ inj₂ i
case-raise zero i = refl
case-raise (suc m) i with case-raise m i
... | ih rewrite ih = refl

case-inject : ∀ {m} n → (i : Fin m) →
  case (inject+ n i) ≡ inj₁ i
case-inject n zero = refl
case-inject n (suc i) with case-inject n i
... | ih rewrite ih = refl

-- -- split-concat₁ : ∀ m n → (i : Fin (suc m)) (j : Fin (suc n)) →
-- --   proj₁ (split (suc m) (suc n) (concat i j)) ≡ i
-- -- split-concat₁ m n zero zero = refl
-- -- split-concat₁ m n zero (suc i) with split-concat₁ _ _ zero i
-- -- ... | ih = ?
-- -- split-concat₁ m n (suc i) j = {!!}

-- -- split-concat₁ : ∀ m n → (i : Fin m) (j : Fin n) →
-- --   proj₁ (split m n (concat i j)) ≡ i
-- -- split-concat₁ .(suc m) zero (zero {m}) ()
-- -- split-concat₁ .(suc m) (suc n) (zero {m}) j
-- --   -- TODO could we split j and use ih here instead?
-- --   with inject+ (m * suc n) j
-- -- ... | zero = refl
-- -- ... | suc ij with case n (m * suc n) ij
-- -- ... | inj₁ ij₁ = refl
-- -- ... | inj₂ ij₂ with split m (suc n) ij₂
-- -- ... | x , y = {!-d !}
-- -- split-concat₁ .(suc m) n (suc {m} i) j = {!!}

postulate
  split-concat : ∀ m n → (i : Fin m) (j : Fin n) →
    split (concat i j) ≡ (i , j)

inject : ∀ {n} (F : Type n) → Fin n → ⟦ F ⟧
inject `0 ()
inject `1 i = [ tt ]
inject (S `+ T) i with case i
... | inj₁ j = [ inj₁ (inject S j) ]
... | inj₂ k = [ inj₂ (inject T k) ]
inject (S `* T) i with split i
... | j , k = [ (inject S j , inject T k) ]

lift : ∀ {m n} {S T : Type m} {U V : Type n} →
  (⟦ S ⟧ → ⟦ U ⟧) → ⟦ T ⟧ → ⟦ V ⟧
lift {m} {n} {S} {T} {U} {V} f t =
  inject V ∣ f (inject S ∣ t ∣) ∣

⟪_⟫ : ∀ {m n} {S T : Type m} {U V : Type n} →
  (⟦ S ⟧ → ⟦ U ⟧) → ⟦ T ⟧ → ⟦ V ⟧
⟪_⟫ = lift

⟨_⟩ : ∀ {n} {S T : Type n} → ⟦ S ⟧ → ⟦ T ⟧
⟨_⟩ {S = S} s = lift (λ (x : ⟦ S ⟧) → x) s

enum : ∀ {n} (F : Type n) → Vec ⟦ F ⟧ n
enum = tabulate ∘ inject

fins : ∀ {n} (F : Type n) → Vec ℕ n
fins = map (toℕ ∘ toFin) ∘ enum

--------------------------------------------------------------------------------

bijection₁ : ∀ {n} {S : Type n} (s : ⟦ S ⟧) → inject S (toFin s) ≡ s
bijection₁ {S = `0} [ () ]
bijection₁ {S = `1} [ tt ] = refl

bijection₁ {S = _`+_ {y = y} S T} [ inj₁ a ]
  with case-inject y (toFin a) | bijection₁ a
... | p | ih rewrite p | ih = refl

bijection₁ {S = _`+_ {x = x} S T} [ inj₂ b ]
  with case-raise x (toFin b) | bijection₁ b
... | p | ih rewrite p | ih = refl

bijection₁ {S = _`*_ {x} {y} S T} [ (a , b) ]
  with split-concat x y (toFin a) (toFin b) |
       bijection₁ a | bijection₁ b
... | p | ih₁ | ih₂ rewrite p | ih₁ | ih₂ = refl

--------------------------------------------------------------------------------

`Bool = `1 `+ `1
Bool = ⟦ `Bool ⟧

false : Bool
false = [ inj₁ [ tt ] ]

true : Bool
true = [ inj₂ [ tt ] ]

neg : Bool → Bool
neg [ inj₁ [ tt ] ] = true
neg [ inj₂ [ tt ] ] = false

--------------------------------------------------------------------------------

`Light = `1 `* (`1 `+ `1)
Light = ⟦ `Light ⟧

off : Light
off = [ ([ tt ] , [ inj₁ [ tt ] ]) ]

on : Light
on = [ ([ tt ] , [ inj₂ [ tt ] ]) ]

switch : Light → Light
switch = ⟪ neg ⟫

--------------------------------------------------------------------------------

`ThreeL = (`1 `+ `1) `+ `1
ThreeL =  ⟦ `ThreeL ⟧
`ThreeR = `1 `+ (`1 `+ `1)
ThreeR = ⟦ `ThreeR ⟧
`Three = `ThreeL

2:ThreeL : ThreeL
2:ThreeL = [ inj₁ [ inj₂ [ tt ] ] ]

2:ThreeR : ThreeR
2:ThreeR = [ inj₂ [ inj₁ [ tt ] ] ]

2:ThreeR′ : ThreeR
2:ThreeR′ = ⟨ 2:ThreeL ⟩

∣2:ThreeL∣≡#2 : ∣ 2:ThreeL ∣ ≡ # 1
∣2:ThreeL∣≡#2 = refl

2:ThreeL≡⟨2:ThreeR⟩ : 2:ThreeL ≡ ⟨ 2:ThreeR ⟩
2:ThreeL≡⟨2:ThreeR⟩ = refl

⟨2:ThreeL⟩≡2:ThreeR : ⟨ 2:ThreeL ⟩ ≡ 2:ThreeR
⟨2:ThreeL⟩≡2:ThreeR = refl

--------------------------------------------------------------------------------

`Six = (`1 `+ `1) `* `Three
`Six₂ = `Three `+ `Three

5:Six : ⟦ `Six ⟧
5:Six = [ ([ inj₂ [ tt ] ] , [ inj₁ [ inj₂ [ tt ] ] ]) ]

5:Six₂ : ⟦ `Six₂ ⟧
5:Six₂ = [ inj₂ [ inj₁ [ inj₂ [ tt ] ] ] ]

∣5:Six∣≡#4 : ∣ 5:Six ∣ ≡ # 4
∣5:Six∣≡#4 = refl

5:Six≡⟨5:Six₂⟩ : 5:Six ≡ ⟨ 5:Six₂ ⟩
5:Six≡⟨5:Six₂⟩ = refl

--------------------------------------------------------------------------------

