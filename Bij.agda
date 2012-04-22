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
... | (inj₁ j) = zero , suc j
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

∣_∣ : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
∣_∣ = toFin

raise-case : ∀ m n → (i : Fin (suc n)) →
  case m (suc n) (raise m i) ≡ inj₂ i
raise-case zero n i = refl
raise-case (suc m) n i with raise-case m n i
... | ih rewrite ih = refl

inject-case : ∀ m n → (i : Fin (suc m)) →
  case (suc m) n (inject+ n i) ≡ inj₁ i
inject-case zero n zero = refl
inject-case zero n (suc ())
inject-case (suc m) n zero = refl
inject-case (suc m) n (suc i) with inject-case m n i
... | ih rewrite ih = refl

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

x+y≡0 : ∀ x y → x + y ≡ 0 → x ≡ 0 × y ≡ 0
x+y≡0 zero y p = refl , p
x+y≡0 (suc x) y ()

x*y≡0 : ∀ x y → x * y ≡ 0 → x ≡ 0 ⊎ y ≡ 0
x*y≡0 zero y p = inj₁ refl
x*y≡0 (suc x) zero p = inj₂ refl
x*y≡0 (suc x) (suc y) ()

⟦Type0⟧⇒⊥ : ∀ {n} {S : Type n} → n ≡ 0 → ⟦ S ⟧ → ⊥
⟦Type0⟧⇒⊥ {.0} {`0} p [ () ]
⟦Type0⟧⇒⊥ {.1} {`1} () [ s ]
⟦Type0⟧⇒⊥ {.(x + y)} {_`+_ {x} {y} S T} p [ (inj₁ a) ]
  with x+y≡0 x y p
... | px , py = ⟦Type0⟧⇒⊥ {S = S} px [ a ]
⟦Type0⟧⇒⊥ {.(x + y)} {_`+_ {x} {y} S T} p [ (inj₂ b) ]
  with x+y≡0 x y p
... | px , py = ⟦Type0⟧⇒⊥ {S = T} py [ b ]
⟦Type0⟧⇒⊥ {.(x * y)} {_`*_ {x} {y} S T} p [ (a , b) ]
  with x*y≡0 x y p
... | inj₁ px = ⟦Type0⟧⇒⊥ {S = S} px [ a ]
... | inj₂ py = ⟦Type0⟧⇒⊥ {S = T} py [ b ]

bijection₁ : ∀ {n} {S : Type n} (s : ⟦ S ⟧) → inject S (toFin s) ≡ s
bijection₁ {.0} {`0} [ () ]
bijection₁ {.1} {`1} [ tt ] = refl

bijection₁ {.y} {_`+_ {zero} {y} S T} [ inj₁ a ] =
  ⊥-elim $ ⟦Type0⟧⇒⊥ {S = S} refl [ a ]

bijection₁ {.(suc (x + y))} {_`+_ {suc x} {y} S T} [ inj₁ a ]
  with toFin {F = S} [ a ] | bijection₁ {S = S} [ a ]
... | zero | ih rewrite ih = refl
... | suc i | ih with inject-case x y (suc i)
... | p rewrite p | ih = refl

bijection₁ {.(x + 0)} {_`+_ {x} {zero} S T} [ inj₂ b ] =
  ⊥-elim $ ⟦Type0⟧⇒⊥ {S = T} refl [ b ]

bijection₁ {.(x + suc y)} {_`+_ {x} {suc y} S T} [ inj₂ b ]
  with toFin {F = T} [ b ] | bijection₁ {S = T} [ b ]
... | i | ih with raise-case x y i
... | p rewrite p | ih = refl

bijection₁ {.(x * y)} {_`*_ {x} {y} S T} [ s ] = {!!}

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
switch = ⟪ neg ⟫

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
5:Six = [ (inj₂ tt , inj₁ (inj₂ tt)) ]

5:Six₂ : ⟦ `Six₂ ⟧
5:Six₂ = [ inj₂ (inj₁ (inj₂ tt)) ]

∣5:Six∣≡#4 : ∣ 5:Six ∣ ≡ # 4
∣5:Six∣≡#4 = refl

5:Six≡⟨5:Six₂⟩ : 5:Six ≡ ⟨ 5:Six₂ ⟩
5:Six≡⟨5:Six₂⟩ = refl

--------------------------------------------------------------------------------

