module Eg where
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Bij

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

∣2:ThreeL∣≡#2 : (toFin 2:ThreeL) ≡ # 1
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

∣5:Six∣≡#4 : (toFin 5:Six) ≡ # 4
∣5:Six∣≡#4 = refl

5:Six≡⟨5:Six₂⟩ : 5:Six ≡ ⟨ 5:Six₂ ⟩
5:Six≡⟨5:Six₂⟩ = refl

--------------------------------------------------------------------------------

`2 = `1 `+ `1
`3 = `1 `+ `2

one : ⟦ `3 ⟧
one = [ inj₁ [ tt ] ]

two : ⟦ `3 ⟧
two = [ inj₂ ∣ one ∣ ]

snd : ⟦ `2 ⟧
snd = [ inj₂ [ tt ] ]

5:Six′ : ⟦ `Six ⟧
5:Six′ = [ (∣ snd ∣ , [ inj₁ ∣ snd ∣ ]) ]

--------------------------------------------------------------------------------

twoR : ThreeR
twoR = [ inj₂ [ inj₁ [ tt ] ] ]

middleR : ThreeR → Bool
middleR [ inj₂ [ inj₁ [ tt ] ] ] = true
middleR _ = false

middleL : ThreeL → Bool
middleL = ⟪ middleR ⟫
