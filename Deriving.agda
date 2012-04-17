module Deriving where

infixr 4 _+'_
infixr 4 _,_

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

data _==_ {X : Set}(x : X) : X → Set where
  refl : x == x

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
  _+'_ _*'_ : (S T : U) → U
  mu' : (F : U) → U

simplify : U → U

simplify (zero' *' T) = zero'
simplify (S *' zero') = zero'

simplify (zero' +' T) = T
simplify (S +' zero') = S

simplify (one' *' T) = T
simplify (S *' one') = S

simplify ((S +' T) +' U) = S +' (T +' U)
simplify ((S *' T) *' U) = S *' (T *' U)

-- Probably want this one backwards
-- simplify (S *' (T +' U)) = (S *' T) +' (S +' U)

simplify F = F

fin' : ℕ → U
fin' zero = zero'
fin' (suc n) = one' +' fin' n

ind' : ℕ → U → U
ind' zero F = one' *' F
ind' (suc n) F = one' *' ind' n F

two' : U
two' = fin' 2

bool' : U
bool' = ind' 0 two'

light' : U
light' = ind' 1 two'

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

fmap : ∀ {F X Y} → (X → Y) → El F X → El F Y
fmap {rec'} f x = f x
fmap {zero'} f ()
fmap {one'} f x = x
fmap {S +' T} f (inl s) = inl (fmap {S} f s)
fmap {S +' T} f (inr t) = inr (fmap {T} f t)
fmap {S *' T} f (s , t) = fmap {S} f s , fmap {T} f t
fmap {mu' F} f x = x

fmapMu : ∀ {F S T} → (Mu S → Mu T) → El F (Mu S) → El F (Mu T)
fmapMu {F} f x = fmap {F} f x

val : ∀ {F} → Mu F → El F (Mu F)
val [ X ] = X

extend : ∀ F G → El F (Mu G) → El F (Mu (one' *' G))
extend rec' G [ x ] = [ _ , extend G G x ]
extend zero' G ()
extend one' G x = x
extend (S +' T) G (inl s) = inl (extend S G s)
extend (S +' T) G (inr t) = inr (extend T G t)
extend (S *' T) G (s , t) = extend S G s , extend T G t
extend (mu' F) G x = x

[from] : ∀ F n → El F (Mu F) → El (ind' n F) (Mu (ind' n F))
[from] F zero x = _ , extend F _ x
[from] F (suc n) x = _ , extend (ind' n F) _ ([from] F n x)

_⟨_⟩ : ∀ {F} n → Mu F → Mu (ind' n F)
n ⟨ x ⟩ = [ [from] _ n (val x) ]

contract : ∀ F G → El F (Mu (one' *' G)) → El F (Mu G)
contract rec' G [ _ , x ] = [ contract G G x ]
contract zero' G ()
contract one' G x = x
contract (S +' T) G (inl s) = inl (contract S G s)
contract (S +' T) G (inr t) = inr (contract T G t)
contract (S *' T) G (s , t) = contract S G s , contract T G t
contract (mu' F) G x = x

raw : ∀ {n F} → Mu (ind' n F) → Mu F
raw {zero} {F} [ _ , f ] = [ contract F _ f ]
raw {suc n} {F} [ _ , f ] = raw {n} [ contract (ind' n F) _ f ]

-- raw-sound : ∀ n F → Mu F == raw {n} (Mu (ind' n F))

expand : ∀ a' b' → El a' (Mu b') → El a' (Mu (one' +' b'))
expand rec' b' [ X ] = [ inr (expand b' b' X) ]
expand zero' b' ()
expand one' b' X = X
expand (S +' T) b' (inl s) = inl (expand S b' s)
expand (S +' T) b' (inr t) = inr (expand T b' t)
expand (S *' T) b' (s , t) = expand S b' s , expand T b' t
expand (mu' F) b' X = X

tabulate' : ∀ {n} {A : Set} → (Mu (fin' n) → A) → Vec A n
tabulate' {zero}  f = []
tabulate' {suc n} f =
  f [ inl <> ] ∷ tabulate' (λ { [ X ] → f [ inr (expand (fin' n) _ X) ] })

all⟦fin'⟧ : ∀ n → Vec (Mu (fin' n)) n
all⟦fin'⟧ _ = tabulate' (λ x → x)

--------------------------------------------------------------------------------

foo : El (one' +' one') (Mu (one' +' one'))
foo = inl _

bar : El (one' +' one' +' one') (Mu (one' +' one' +' one'))
bar = inr foo

three : Mu three'
three = [ inl <> ]

three2 : Mu three2'
three2 = [ inr <> ]

one : Mu two'
one = [ inl <> ]

two : Mu two'
two = [ inr (inl <>) ]

twos : Vec (Mu two') _
twos = all⟦fin'⟧ _

bools : Vec (Mu bool') _
bools = map (_⟨_⟩ 0) twos

lights : Vec (Mu light') _
lights = map (_⟨_⟩ 1) twos

true : Mu bool'
true = 0 ⟨ lookup (# 0) twos ⟩

one==raw[true] : one == raw {0} true
one==raw[true] = refl

false : Mu bool'
false = 0 ⟨ two ⟩

two==raw[false] : two == raw {0} false
two==raw[false] = refl

on : Mu light'
on = 1 ⟨ one ⟩

one==raw[on] : one == raw {1} on
one==raw[on] = refl

off : Mu light'
off = 1 ⟨ two ⟩

two==raw[off] : two == raw {1} off
two==raw[off] = refl

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
