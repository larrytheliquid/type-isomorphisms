module Syntax where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

infix 1 _∶_
infix 2 _as_

data Type : Set where
  `0 `1 : Type
  _`+_ _`*_ : (S T : Type) → Type

data Value : Set where
  tt : Value
  inj₁ inj₂ : (x : Value) → Value
  _,_ : (x y : Value) → Value

data _∶_ : Value → Type → Set where
  tt : tt ∶ `1
  inj₁ : ∀ {s S T} →
    s ∶ S →
    inj₁ s ∶ S `+ T
  inj₂ : ∀ {S t T} →
    t ∶ T →
    inj₂ t ∶ S `+ T
  _,_ : ∀ {s S t T} →
    s ∶ S → t ∶ T →
    s , t ∶ S `* T

El : Type → Set
data ⟦_⟧ (F : Type) : Set

El `0 = ⊥
El `1 = ⊤
El (S `+ T) = ⟦ S ⟧ ⊎ ⟦ T ⟧
El (S `* T) = ⟦ S ⟧ × ⟦ T ⟧

data ⟦_⟧ F where
  [_] : (x : El F) → ⟦ F ⟧

val : {F : Type} → ⟦ F ⟧ → Value
val {`0} [ () ]
val {`1} [ tt ] = tt
val {S `+ T} [ inj₁ x ] = inj₁ (val x)
val {S `+ T} [ inj₂ y ] = inj₂ (val y)
val {S `* T} [ x , y ] = val x , val y

_as_ : (s : Value) (S : Type) → Maybe (s ∶ S)
tt as `1 = just tt
tt as _ = nothing
inj₁ s as S `+ T with s as S
... | just ih = just (inj₁ ih)
... | nothing = nothing
inj₁ s as _ = nothing
inj₂ t as S `+ T with t as T
... | just ih = just (inj₂ ih)
... | nothing = nothing
inj₂ t as _ = nothing
s , t as S `* T with s as S | t as T
... | just ih₁ | just ih₂ = just (ih₁ , ih₂)
... | _ | _ = nothing
s , t as _ = nothing

toWit : {P : Set} {Q : Maybe P} → T (maybeToBool Q) → P
toWit {Q = just p} _  = p
toWit {Q = nothing} ()

inject : ∀ {S T : Type} (s : ⟦ S ⟧) → val s ∶ T → ⟦ T ⟧
inject {`0} [ () ] p
inject {`1} [ tt ] tt = [ tt ]
inject {S `+ T} [ inj₁ s ] (inj₁ p) = [ inj₁ (inject s p) ]
inject {S `+ T} [ inj₂ t ] (inj₂ p) = [ inj₂ (inject t p) ]
inject {S `* T} [ s , t ] (p₁ , p₂) = [ (inject s p₁ , inject t p₂) ]

⟨_⟩ : ∀ {A B : Type} (a : ⟦ A ⟧) {a∶B : T (maybeToBool (val a as B))} → ⟦ B ⟧
⟨_⟩ a {a∶B} = inject a (toWit a∶B)

--------------------------------------------------------------------------------

`2 : Type
`2 = `1 `+ `1

`3 : Type
`3 = `1 `+ `2

one : ⟦ `3 ⟧
one = [ inj₁ [ tt ] ]

two : ⟦ `3 ⟧
two =  [ inj₂ ⟨ one ⟩ ]

three : ⟦ `3 ⟧
three = [ inj₂ [ inj₂ [ tt ] ] ]


