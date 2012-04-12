module Deriving where

infixr 4 _+'_

data Zero : Set where

record One : Set where constructor <>

data _+_ (S T : Set) : Set where
  inl : (s : S) → S + T
  inr : (t : T) → S + T

record _*_ (S T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T

--------------------------------------------------------------------------------

open import Data.Nat hiding ( _+_ ; _*_ )
open import Data.Fin hiding ( _+_ )
open import Data.Vec hiding ( [_] )

--------------------------------------------------------------------------------

data _⊎_ : (S T : Set) → Set₁ where
  inl : {S T : Set} (s : S) → S ⊎ T
  inr : {S T : Set} (t : T) → S ⊎ T

-- hm : One ⊎ (One ⊎ One)
-- hm = inl <>

-- hm : One ⊎ One
-- hm = inl <>

--------------------------------------------------------------------------------

data U : Set where
  rec' zero' one' : U
  _+'_ _*'_ : U → U → U
  mu' : U → U

fin' : ℕ → U
fin' zero = zero'
fin' (suc n) = one' +' fin' n

bool' : U
bool' = one' +' one'

nat' : U
nat' = one' +' rec'

list' : U → U
list' a' = one' +' (mu' a' *' rec')

natTree' : U
natTree' = mu' nat' +' (rec' *' rec')

day' : U
day' = fin' 7

three' : U
three' = one' +' (one' +' one')

three2' : U
three2' = (one' +' one') +' one'

--------------------------------------------------------------------------------

El : U → Set → Set
data Mu (F : U) : Set

El rec'      X = X
El zero'     X = Zero
El one'      X = One
El (S +' T)  X = El S X + El T X
El (S *' T)  X = El S X * El T X
El (mu' F)   X = Mu F

data Mu F where
  [_] : El F (Mu F) → Mu F

--------------------------------------------------------------------------------

three : Mu three'
three = [ inl <> ]

three2 : Mu three2'
three2 = [ inr <> ]

true : Mu bool'
true = [ inl <> ]

false : Mu bool'
false = [ inr <> ]

-- cannot use "true" here
`zero : Mu nat'
`zero = [ inl <> ]

`suc : Mu nat' → Mu nat'
`suc n = [ inr n ]

nil : {a' : U} → Mu (list' a')
nil = [ inl <> ]

cons : {a' : U} → Mu a' → Mu (list' a') → Mu (list' a')
cons x xs = [ inr (x , xs) ]

leaf : Mu nat' → Mu natTree'
leaf n = [ inl n ]

node : Mu natTree' → Mu natTree' → Mu natTree'
node s t = [ inr (s , t) ]

-- monday : El day' (Mu day')
-- monday = inl <>

-- tuesday : El day' (Mu day')
-- tuesday = inr monday

extend : ∀ a' b' → El a' (Mu b') → El a' (Mu (one' +' b'))
extend rec' b' [ X ] = [ inr (extend b' b' X) ]
extend zero' b' ()
extend one' b' X = X
extend (S +' T) b' (inl s) = inl (extend S b' s)
extend (S +' T) b' (inr t) = inr (extend T b' t)
extend (S *' T) b' (s , t) = extend S b' s , extend T b' t
extend (mu' F) b' X = X

tabulate' : ∀ {n} {A : Set} → (Mu (fin' n) → A) → Vec A n
tabulate' {zero}  f = []
tabulate' {suc n} f =
  f [ inl <> ] ∷ tabulate' (λ { [ X ] → f [ inr (extend (fin' n) _ X) ] })

all⟦fin'⟧ : ∀ n → Vec (Mu (fin' n)) n
all⟦fin'⟧ _ = tabulate' (λ x → x)

days : Vec (Mu day') _
days = all⟦fin'⟧ _

monday : Mu day'
monday = [ inl <> ]

tuesday : Mu day'
tuesday = [ inr (inl <>) ]

wednesday : Mu day'
wednesday = [ inr (inr (inl <>)) ]

thursday = lookup (# 3) days
friday   = lookup (# 4) days
saturday = lookup (# 5) days
sunday   = lookup (# 6) days

--------------------------------------------------------------------------------

-- Fin : Mu nat' → Set
-- Fin [ inl s ] = Zero
-- Fin [ inr t ] = One + Fin t

-- List : (a' : U) → Mu a' → Set
-- List a' 

-- fin' : Mu nat' → U
-- fin' [ inl s ] = zero'
-- fin' [ inr t ] = one' +' fin' t

-- fzero : Mu nat' → Mu fin'

--------------------------------------------------------------------------------

data Decide (X : Set) : Set where
  yes : X → Decide X
  no : (X → Zero) → Decide X

data _==_ {X : Set}(x : X) : X → Set where
  refl : x == x

DecEq : Set → Set
DecEq X = (x y : X) → Decide (x == y)

--------------------------------------------------------------------------------

QTYPE : Set → Set₁
QTYPE A = Set → A → A → Set

qTYPE : {A : Set} → QTYPE A → Set₁
qTYPE {A} Q = {X : Set}{a b : A} → Q X a b → a == b → X

--------------------------------------------------------------------------------

QSum : (S T : Set) → QTYPE (S + T)
QSum S T X (inl s) (inl s') = s == s' → X
QSum S T X (inl s) (inr t) = One
QSum S T X (inr t) (inl s) = One
QSum S T X (inr t) (inr t') = t == t' → X

qSum : {S T : Set} → qTYPE (QSum S T)
qSum {a = inl _} q refl = q refl
qSum {a = inr _} q refl = q refl

--------------------------------------------------------------------------------

QProd : (S T : Set) → QTYPE (S * T)
QProd S T X (s , t) (s' , t') = s == s' → t == t' → X

qProd : {S T : Set} → qTYPE (QProd S T)
qProd {a = _ , _} q refl = q refl refl

--------------------------------------------------------------------------------

QMu : (F : U) → QTYPE (Mu F)
QMu F X [ a ] [ b ] = a == b → X

qMu : {F : U} → qTYPE (QMu F)
qMu {a = [ _ ]} q refl = q refl

--------------------------------------------------------------------------------

decEq : {F : U} → DecEq (Mu F)
decEqU : (F G : U) → DecEq (El F (Mu G))

decEq {F} [ a ] [ b ] with decEqU F F a b
decEq {F} [ a ] [ .a ] | yes refl = yes refl
decEq {F} [ a ] [ b ]  | no bad = no (qMu bad)

decEqU rec' G a b = decEq a b
decEqU zero' G () b
decEqU one' G a b = yes refl
decEqU (S +' T) G (inl s) (inl s') with decEqU S G s s'
decEqU (S +' T) G (inl s) (inl .s) | yes refl = yes refl
decEqU (S +' T) G (inl s) (inl s') | no bad = no (qSum bad)
decEqU (S +' T) G (inl s) (inr t) = no (qSum <>)
decEqU (S +' T) G (inr t) (inl s) = no (qSum <>)
decEqU (S +' T) G (inr t) (inr t') with decEqU T G t t'
decEqU (S +' T) G (inr t) (inr .t) | yes refl = yes refl
decEqU (S +' T) G (inr t) (inr t') | no bad = no (qSum bad)
decEqU (S *' T) G (s , t) (s' , t') with decEqU S G s s' | decEqU T G t t'
decEqU (S *' T) G (s , t) (.s , .t) | yes refl | yes refl = yes refl
decEqU (S *' T) G (s , t) (.s , t') | yes refl | no bad = no (qProd \ _ q → bad q)
decEqU (S *' T) G (s , t) (s' , t') | no bad | _ = no (qProd \ q _ → bad q)
decEqU (mu' F) G a b = decEq a b

--------------------------------------------------------------------------------

-- decEq (node (leaf zero) (leaf (suc zero))) (node (leaf zero) (leaf (suc zero)))
-- yes refl

-- decEq (node (leaf (suc zero)) (leaf zero)) (node (leaf zero) (leaf (suc zero)))
-- no (qMu (qSum (qProd (\ q _ → qMu (qSum (qMu (qSum <>))) q))))
