module Bij where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Fin hiding ( _+_ ; lift ; inject )
open import Data.Vec hiding ( concat ; [_] )
open import Relation.Binary.PropositionalEquality

concat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
concat {zero} {n} () j
concat {suc m} {zero} zero ()
concat {suc m} {suc n} zero j = inject+ (m * suc n) j
concat {suc m} {n} (suc i) j = raise n (concat i j)

case : ∀ m n → Fin (m + n) → Fin m ⊎ Fin n
case zero n i = inj₂ i
case (suc m) n zero = inj₁ zero
case (suc m) n (suc i) with case m n i
... | (inj₁ j) = inj₁ (suc j)
... | (inj₂ k) = inj₂ k

split : ∀ m n → Fin (m * n) → Fin m × Fin n
split zero n ()
split (suc m) zero i = zero , proj₂ (split m zero i)
split (suc m) (suc n) zero = zero , zero
split (suc m) (suc n) (suc i) with case n (m * suc n) i
... | (inj₁ j) = zero , suc j -- TODO maybe zero
... | (inj₂ k) with split m (suc n) k
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
El `0 = ⊥
El `1 = ⊤
El (S `+ T) = El S ⊎ El T
El (S `* T) = El S × El T

data ⟦_⟧ {n} (F : Type n) : Set where
  [_] : El F → ⟦ F ⟧

proj : ∀ {n} {F : Type n} → ⟦ F ⟧ → El F
proj [ x ] = x

toFin : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
toFin {.0} {`0} [ () ]
toFin {.1} {`1} [ tt ] = zero
toFin {.(x + y)} {_`+_ {x} {y} S T} [ inj₁ a ]
  with toFin {x} {S} [ a ]
... | ih = inject+ y ih
toFin {.(x + y)} {_`+_ {x} {y} S T} [ inj₂ b ]
  with toFin {y} {T} [ b ]
... | ih = raise x ih
toFin {.(x * y)} {_`*_ {x} {y} S T} [ a , b ]
  with toFin {x} {S} [ a ] | toFin {y} {T} [ b ]
... | ih₁ | ih₂ = concat ih₁ ih₂

⟨_⟩ : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
⟨_⟩ = toFin

inject : ∀ {n} (F : Type n) → Fin n → ⟦ F ⟧
inject {.0} `0 ()
inject {.1} `1 i = [ tt ]
inject {.(x + y)} (_`+_ {x} {y} S T) i
  with case x y i
... | inj₁ j = [ inj₁ (proj (inject S j)) ]
... | inj₂ k = [ inj₂ (proj (inject T k)) ]
inject {.(x * y)} (_`*_ {x} {y} S T) i
  with split x y i
... | j , k = [ (proj (inject S j) , proj (inject T k)) ]

lift : ∀ {m n} {S T : Type m} {U V : Type n} →
  (⟦ S ⟧ → ⟦ U ⟧) → ⟦ T ⟧ → ⟦ V ⟧
lift {m} {n} {S} {T} {U} {V} f t =
  inject V ⟨ f (inject S ⟨ t ⟩) ⟩

--------------------------------------------------------------------------------

`Bool = `1 `+ `1
Bool = ⟦ `Bool ⟧

false : Bool
false = [ inj₁ tt ]

true : Bool
true = [ inj₂ tt ]

neg : Bool → Bool
neg [ inj₁ tt ] = true
neg [ inj₂ tt ] = false

--------------------------------------------------------------------------------

`Light = `1 `* (`1 `+ `1)
Light = ⟦ `Light ⟧

off : Light
off = [ (tt , inj₁ tt) ]

on : Light
on = [ (tt , inj₂ tt) ]

switch : Light → Light
switch = lift neg

--------------------------------------------------------------------------------

`ThreeL = (`1 `+ `1) `+ `1
ThreeL =  ⟦ `ThreeL ⟧
`ThreeR = `1 `+ (`1 `+ `1)
ThreeR = ⟦ `ThreeR ⟧
`Three = `ThreeL

2:ThreeL : ThreeL
2:ThreeL = [ inj₁ (inj₂ tt) ]

2:ThreeR : ThreeR
2:ThreeR = [ inj₂ (inj₁ tt) ]

2:ThreeR′ : ThreeR
2:ThreeR′ = lift (λ (x : ThreeR) → x) 2:ThreeL

2:ThreeL≡2:ThreeR : # 1 ≡ ⟨ 2:ThreeL ⟩ × ⟨ 2:ThreeL ⟩ ≡ ⟨ 2:ThreeR ⟩
2:ThreeL≡2:ThreeR = refl , refl

--------------------------------------------------------------------------------

`Six = (`1 `+ `1) `* `Three
`Six₂ = `Three `+ `Three

5:Six : ⟦ `Six ⟧
5:Six = [ (inj₂ tt , inj₁ (inj₂ tt)) ]

5:Six₂ : ⟦ `Six₂ ⟧
5:Six₂ = [ inj₂ (inj₁ (inj₂ tt)) ]

5:Six≡5:Six₂ : # 4 ≡ ⟨ 5:Six ⟩ × ⟨ 5:Six ⟩ ≡ ⟨ 5:Six₂ ⟩
5:Six≡5:Six₂ = refl , refl

--------------------------------------------------------------------------------

