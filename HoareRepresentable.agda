module HoareRepresentable where

-- * Notation

-- We postfix by "D" the operations that computes a functor
-- representation. Associated with it will be the operation that
-- computes the actual functor, by interpreting the representation.

-- Because represented functors are the result of an encoding, we
-- provide helpers functions to be able to manipulate them slightly
-- more naturally:
--     - introduction function, which let us build inhabitants 
--     - views, which let us pattern-match on inhabitants

-- NOTE: In a system where these objects /are/ the basis for
-- data-types (eg. Epigram), this should be less of a pain to deal
-- with these objects. 

-- * Imports

open import Function

open import Data.Unit
open import Data.Nat renaming (_*_ to _*ℕ_)
open import Data.Fin renaming (_+_ to _+Fin_)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Char
open import Data.String
open import Data.List hiding (_++_)

open import Relation.Binary.PropositionalEquality

-- * Working on Predicates

Pow : Set → Set1
Pow X = X → Set

infixr 60 _⟶_
_⟶_ : {I : Set} → Pow I → Pow I → Set
A ⟶ B = {i : _} → A i → B i


-- * A representation of Pow I → Pow O functors
-- ** Descriptions

-- A Description "represents" a functor from Pow I to Set. We define
-- Descriptions with a universe construction: first, the syntax of
-- Descriptions, Desc, then their interpretation, ⟦_⟧D and ⟦_⟧MorphD,
-- as functor from Pow I to Set.

-- I adopt an algebraic presentation of these codes, your mileage may
-- vary: you could do it the Dybjer way, put more or less constructs,
-- etc. In the end, you just need to cover indexed containers.

data Desc (I : Set) : Set1 where
  `var   : (i : I) → Desc I
  `const : (K : Set) → Desc I
  _`+_   : (D : Desc I)(D' : Desc I) → Desc I
  _`×_   : (D : Desc I)(D' : Desc I) → Desc I
  `Π     : (S : Set)(T : S → Desc I) → Desc I
  `Σ     : (S : Set)(T : S → Desc I) → Desc I


⟦_⟧D : {I : Set} → Desc I → Pow I → Set
⟦ `var i ⟧D   X  = X i
⟦ `const K ⟧D X  = K
⟦ D `+ D' ⟧D  X  = ⟦ D ⟧D X ⊎ ⟦ D' ⟧D X
⟦ D `× D' ⟧D  X  = ⟦ D ⟧D X × ⟦ D' ⟧D X
⟦ `Π S T ⟧D   X  = (s : S) → ⟦ T s ⟧D X
⟦ `Σ S T ⟧D   X  = Σ[ s ∶ S ] ⟦ T s ⟧D X

⟦_⟧MorphD : ∀ {I X Y} → (D : Desc I) → (X ⟶ Y) → ⟦ D ⟧D X → ⟦ D ⟧D Y
⟦ `var i ⟧MorphD    f x         = f x
⟦ `const K ⟧MorphD  f x         = x
⟦ D `+ D' ⟧MorphD   f (inj₁ x)  = inj₁ (⟦ D ⟧MorphD f x)
⟦ D `+ D' ⟧MorphD   f (inj₂ y)  = inj₂ (⟦ D' ⟧MorphD f y)
⟦ D `× D' ⟧MorphD   f (x , y)   = (⟦ D ⟧MorphD f x) , (⟦ D' ⟧MorphD f y)
⟦ `Π S T ⟧MorphD    f t         = λ s → ⟦ T s ⟧MorphD f (t s)
⟦ `Σ S T ⟧MorphD    f (s , t)   = (s , ⟦ T s ⟧MorphD f t)            

-- ** Representable indexed functors

-- *** Definition

-- Now, to "represent" functors from Pow I to Pow O, we define:

RFunctor : Set → Set → Set1
RFunctor I O = O → Desc I

-- For lack of a better name, I will call an 'RFunctor' a
-- representable functor and its interpetation a 'represented
-- functor'. This is a very stupid naming convention, so let me know
-- if there is a more appropriate denomination.

-- NOTE: Putting a RFunctor as an implicit argument is
-- completely hopeless: Agda unification algorithm will fail you badly
-- even for the most trivial things (unification of functions = No
-- Future). That's a shame, but I believe that we could think of a
-- workaround, if necessary.

-- *** Interpretation

-- Now, we can 'represent' functors from Pow I to Pow O

⟦_⟧Obj : {I O : Set} → RFunctor I O → Pow I → Pow O
⟦ φ ⟧Obj X o = ⟦ φ o ⟧D X

⟦_⟧Morph : ∀ {I O X Y} → (F : RFunctor I O) → 
          (X ⟶ Y) → ⟦ F ⟧Obj X ⟶ ⟦ F ⟧Obj Y
⟦ φ ⟧Morph f x = ⟦ φ _ ⟧MorphD f x

-- ** Fix point

-- We have initial algebra, catamorphism and even an induction
-- principle if you want.

data μ {I : Set}(φ : RFunctor I I)(i : I) : Set where
  <_> : ⟦ φ ⟧Obj (μ φ) i → μ φ i

-- TODO rewrite as a mapFold 
--      (to shut up the termination checker)

cata : {I : Set}{φ : RFunctor I I}{X : I → Set} → 
       (⟦ φ ⟧Obj X ⟶ X) → μ φ ⟶ X
cata {φ = φ} f < x > = f (⟦ φ ⟧Morph (cata f) x) 

-- * Operators on the language of predicates
-- ** At key operator

-- In his "Parametrised notion of computation", Bob defines
-- "parametrised monads" as some sort of monads built out of functors
-- from O × Set × I to Set, ie. morphism of type O × Set × I → Set

-- Now, if you shuffle things around, you get, equivalently:
--     (Σ[ X ∶ Set ] (X → ⊤ → I)) → (O → Set)
-- ie. (Σ[ X ∶ Set ] (X → ⊤ → I)) → Pow O

-- This (Σ[ X ∶ Set ] (X → ⊤ → I)) is some sort of 
--     Fam₀ I = Σ[ X ∶ Set ] (X → ⊤ → I) 
-- where the second component does not depend on X.

-- In our setting, we work from Pow I to Pow O, or equivalently Fam I
-- to Pow O. Now, surely, we can make those functors Bob is talking
-- about, by restraining ourselves to the k : I pointed to by the 
-- map ⊤ → I:

infix 50 _⊢_
data _⊢_ {I : Set}(X : Set)(k : I) : Pow I where
  witness : (wit : X) → (X ⊢ k) k

-- ** Hoare triple

-- Hoare triples represents the pre- and post-condition required and
-- enforced by a command.

-- In Agda notation, they are implemented as follow:
--
-- record _⟫_ {I I' : Set}
--            (Pre : Pow I)(Post : Pow I')
--            (T : Pow I')(i : I) : Set where
--   field
--     pre : Pre i
--     post : Post ⟶ T


-- *** Definition

infix 40 _⟫D_
_⟫D_ : {I I' : Set}(Pre : Pow I)(Post : Pow I') → RFunctor I' I
_⟫D_ {I} {I'} Pre Post i = 
            `const (Pre i) 
         `× `Π I' (\i' → `Π (Post i') (\_ → `var i'))

infix 40 _⟫_
_⟫_ : {I I' : Set}(Pre : Pow I)(Post : Pow I') → Pow I' → Pow I
Pre ⟫ Post = ⟦ Pre ⟫D Post ⟧Obj

-- *** Constructor

[_]∙[_] : {I I' : Set}{Pre : Pow I}{Post : Pow I'}{T : Pow I'}{i : I} →
          Pre i → ((j : I') → Post j → T j) → (Pre ⟫ Post) T i
[ p ]∙[ q ] = p , q

-- *** View

data ⟫-View {I I' : Set}
            (Pre : Pow I)(Post : Pow I')
            (T : Pow I')(i : I) : Set where
  hoare : (p : Pre i)
          (q : (i' : I') → Post i' → T i') → ⟫-View Pre Post T i

⟫-view : {I I' : Set}
         (Pre : Pow I)(Post : Pow I')
         {T : Pow I'}{i : I} → 
         (Pre ⟫ Post) T i → ⟫-View Pre Post T i
⟫-view Pre Post (pre , post) = hoare pre post

-- ** Sum of indexed functors

-- Pretty much like in Data-type a la Carte, we are going to combine
-- signature over a free monad (yay!). Therefore, we give ourselves a
-- notation for sum of representable functors. 

-- In Agda, one would write:
--
-- data _⊕_ {I I' : Set}(P : Pow I → Pow I')(Q : Pow I → Pow I')(t : Pow I)(i' : I') : Set where
--     inl : (x : P t i') → (P ⊕ Q) t i'
--     inr : (y : Q t i') → (P ⊕ Q) t i'

-- *** Definition

infixr 30 _⊕D_
_⊕D_ : {I I' : Set}(P : RFunctor I I')(Q : RFunctor I I') → RFunctor I I'
(P ⊕D Q) i = P i `+ Q i

infixr 30 _⊕_
_⊕_ : {I I' : Set}(P : RFunctor I I')(Q : RFunctor I I') → Pow I → Pow I'
P ⊕ Q = ⟦ P ⊕D Q ⟧Obj

-- *** Constructors

inj⊕₁ : {I I' : Set}(P : RFunctor I I')(Q : RFunctor I I') →
        {X : Pow I} → ⟦ P ⟧Obj X ⟶ (P ⊕ Q) X
inj⊕₁ P Q x = inj₁ x

inj⊕₂ : {I I' : Set}(P : RFunctor I I')(Q : RFunctor I I') →
        {X : Pow I} → ⟦ Q ⟧Obj X ⟶ (P ⊕ Q) X
inj⊕₂ P Q x = inj₂ x

-- *** View

data ⊕-View {I I' : Set}
            (P : RFunctor I I')(Q : RFunctor I I')
            (T : Pow I)(i : I') : Set where
     inj₁ : ⟦ P ⟧Obj T i → ⊕-View P Q T i
     inj₂ : ⟦ Q ⟧Obj T i → ⊕-View P Q T i

⊕-view : {I I' : Set}
         (P : RFunctor I I')(Q : RFunctor I I')
         {T : Pow I}{i : I'} → (P ⊕ Q) T i → ⊕-View P Q T i
⊕-view P Q (inj₁ x) = inj₁ x
⊕-view P Q (inj₂ y) = inj₂ y


-- ** Free Monad

-- As I said above, we are going to give a signature specifying our
-- effects, from which we want to obtain an algebraic theory with
-- those effects. The way we obtain this theory is by building the
-- free monad over the signature.

-- In Agda, the free monad is defined by:
--
-- data _*_ {I : Set}(P : Pow I → Pow I)(S : Pow I) : Pow I where
--   ηf : S ⟶ P * S 
--   μf : P (P * S) ⟶ P * S

-- NOTE: Obviously, with this definition in Agda, you start an
-- hopeless battle with the positivity-checker, soon to be joined by
-- the termination-checker. Here, because we are in the nice world of
-- representable functors, we enjoy ourselves and don't have to bother.

-- *** Definition

infix 80 _*_
_*_ : {I : Set}(P : RFunctor I I) → Pow I → RFunctor I I
(P * X) i = `const (X i) `+ (P i)

μ⋆ : { I : Set}(P : RFunctor I I)(S : Pow I) → Pow I
μ⋆ P S = μ (P * S)

-- *** Constructors

ηf : ∀ {I S P} → {i : I} → S i → μ⋆ P S i
ηf s = < inj₁ s >

μf : ∀ {I S P} → {i : I} → ⟦ P i ⟧D (μ⋆ P S) → μ⋆ P S i
μf x = < inj₂ x >

-- *** View

data FreeMonad-View {I : Set}(P : RFunctor I I)(S : Pow I) : Pow I where
  ηv : S ⟶ FreeMonad-View P S 
  μv : ⟦ P ⟧Obj (μ⋆ P S) ⟶ FreeMonad-View P S

FreeMonad-view : {I : Set}{P : RFunctor I I}{S : Pow I} → 
                 μ⋆ P S ⟶ FreeMonad-View P S
FreeMonad-view < inj₁ x > = ηv x
FreeMonad-view < inj₂ y > = μv y

-- *** Monadic bind

-- Here starts the story of angelic and demonic binds. But first of
-- all, let's implement composition in the Kleisli category, ie. the
-- usual 'bind':

-- bind : ∀ {I M} {X Y : I → Set} {i : I} → 
--        (∀ {j : I} → X j → μ⋆ M Y j) →
--        μ⋆ M X i → μ⋆ M Y i


bind : ∀ {I M} {X Y : I → Set} →
       (X ⟶ μ⋆ M Y) →
       μ⋆ M X ⟶ μ⋆ M Y
bind σ x = cata (apply σ) x
  where apply : ∀ {I M} {X Y : I → Set} → 
                (X ⟶ μ⋆ M Y) →
                ⟦ M * X ⟧Obj (μ⋆ M Y) ⟶ μ⋆ M Y
        apply σ (inj₁ v) = σ v
        apply σ (inj₂ t) = < inj₂ t >

-- This is all well and good, but, as such, this 'bind' doesn't
-- correspond to sequencing of effect. Sequencing happens when given
-- an mx : μ⋆ M X i and a computation from X to μ⋆ M Y, we explain
-- how to get the an effectful μ⋆ M Y i.

-- And there is two ways to do that. First, the demonic way: the demon
-- choose the state of the system after the execution of mx : μ⋆ M X i
-- Therefore, in the sequence, we have to be prepared to any possible
-- state, ie. (i : I) → X i → μ⋆ M Y i.
--
-- A typical example is openFile: you ask for a file to be opened, but
-- you cannot predict if the OS will indeed open the file. It might,
-- or it might not. You've to be prepared to handle both cases.

?bind : ∀ {I M} {X Y : I → Set} →
        {i : I} → 
        μ⋆ M X i →
        ((i : I) → X i → μ⋆ M Y i) →
        μ⋆ M Y i
?bind x σ = bind (σ _) x

-- Second, the angelic way: we can tell in which state k the first
-- computation terminates (we do so by saying 'at key k'). Hence, for
-- the sequence, we /know/ in which state we are in, there will be no
-- surprise.
--
-- A typical example is closeFile: in all cases, the file will be
-- closed. So we don't need to consider the other (impossible) cases.

=bind : ∀ {I M} {X : Set}{Y : I → Set} →
        {i k : I} →
        μ⋆ M (X ⊢ k) i →
        (X → μ⋆ M Y k) →
        μ⋆ M Y i
=bind {I}{M}{X}{Y}{i}{k} x σ = ?bind x P⊢k
  where P⊢k : (i : I) → (X ⊢ k) i → μ⋆ M Y i
        P⊢k ._ (witness k) = σ k


-- * File demo example

-- Now, let's consider the FileDemo example. It consists in modelling
-- a file-system interface that can:
--     - open a file
--     - read a character from an open file
--     - close an open file

-- ** I/O system

-- We postulate the following, low-level I/O system. On top of it,
-- we build our safe interface.

postulate Filename : Set
postulate FileHandle : Set

postulate getc : FileHandle → Maybe Char
postulate fopen : Filename → Maybe FileHandle
postulate fclose : FileHandle → ⊤

-- ** State

-- The state of a file is either Closed or Open.

data State : Set where
  Open : State 
  Closed : State 

anyState : State → Set 
anyState _ = ⊤

-- ** Signature of the file-system commands

-- There are 3 commands:
--     - openFile
--     - getChar
--     - closeFile

-- Their pre-/post-conditions are as follow:

openFileSignature : RFunctor State State
openFileSignature = Filename ⊢ Closed ⟫D anyState
    -- In a state where no file is open and given a filename,
    --    the system ends up in any state

getCharSignature : RFunctor State State
getCharSignature = ⊤ ⊢ Open ⟫D (Maybe Char) ⊢ Open
    -- In a state where a file is open,
    --     the command might return a character, and
    --     let the file open

closeFileSignature : RFunctor State State
closeFileSignature = ⊤ ⊢ Open ⟫D ⊤ ⊢ Closed
    -- In a state where a file is open,
    --     the file is closed

-- All together, we obtain the commands of the file-system:

FileCommand : RFunctor State State
FileCommand =   openFileSignature 
            ⊕D  getCharSignature
            ⊕D  closeFileSignature

-- ** The FileSystem monad

-- From the signature of the effects, we get the effectful theory by
-- taking the free monad:

FileSystem : Pow State → Pow State
FileSystem = μ⋆ FileCommand

-- Let's specialize the return, demonic bind and angelic bind:

fsReturn : {A : Set}{s : State} → A → FileSystem (A ⊢ s) s
fsReturn a = ηf (witness a)

infixr 10 _?⟫=_
_?⟫=_ : ∀ {S T s} →
        FileSystem S s → 
        ((s' : State) → S s' → FileSystem T s') →
        FileSystem T s
_?⟫=_ = ?bind 

infixr 10 _=⟫=_
_=⟫=_ : ∀ {S T k s} →
        FileSystem (S ⊢ k) s →
        (S → FileSystem T k) →
        FileSystem T s
_=⟫=_ = =bind 


-- ** Command constructors:

-- Beside the return and bind of the free monad, we also have the
-- commands:

openFile : Filename → FileSystem anyState Closed
openFile filename = μf (inj⊕₁ openFileSignature 
                              (getCharSignature ⊕D closeFileSignature) 
                              (witness filename , \s → ηf {S = anyState}))

closeFile : FileSystem (⊤ ⊢ Closed) Open
closeFile = μf (inj⊕₂ openFileSignature 
                      (getCharSignature ⊕D closeFileSignature) 
                      (inj⊕₂ getCharSignature
                             closeFileSignature 
                             (witness tt , \s → ηf {S = (⊤ ⊢ Closed)})))

getChar : FileSystem (Maybe Char ⊢ Open) Open 
getChar = μf (inj⊕₂ openFileSignature 
                    (getCharSignature ⊕D closeFileSignature) 
                    (inj⊕₁ getCharSignature
                           closeFileSignature 
                           (witness tt , \s → ηf {S = (Maybe Char ⊢ Open)})))

-- NOTE: The code is a bit ugly because I have to pass the signatures
-- manually: being functions, they cannot be infered, which is a
-- nuisance. I'm sure there are ways around that.

-- ** Command view:

-- Just as we defined views to read off the interpreted bits of our
-- represented functors, we can define a view for the FileSystem
-- constructors.

data FileSystem-View : (X : Pow State)(s : State) → Set1 where
 fsReturn-view : ∀{X s} → X s → FileSystem-View X s 
 openFile-view : ∀ {X} → Filename → ((s : State) → anyState s → FileSystem X s) → FileSystem-View X {-anyState-} Closed
 closeFile-view : ∀ {X} → ((s : State) → (⊤ ⊢ Closed) s → FileSystem X s) → FileSystem-View X {-(⊤ ⊢ Closed)-} Open
 getChar-view : ∀ {X} → ((s : State) → (Maybe Char ⊢ Open) s → FileSystem X s) → FileSystem-View X {-(Maybe Char ⊢ Open)-} Open

-- TODO I would like to build the view for the {-commented-} types but
--      it doesn't work. I've to '∀ {X} →' them instead.

FileSystem-view : (X : Pow State)(s : State) → FileSystem X s → FileSystem-View X s
FileSystem-view X s x with FreeMonad-view x
FileSystem-view X s x | ηv ret = fsReturn-view ret
FileSystem-view X s x | μv p₁ with ⊕-view openFileSignature (getCharSignature ⊕D closeFileSignature) p₁ 
FileSystem-view X s x | μv p₁ | inj₁ h with ⟫-view (Filename ⊢ Closed) anyState h
FileSystem-view X .Closed x | μv p₁ | inj₁ h | hoare (witness filename) k = openFile-view filename k
FileSystem-view X s x | μv p₁ | inj₂ p₂ with ⊕-view getCharSignature closeFileSignature p₂
FileSystem-view X s x | μv p₁ | inj₂ p₂ | inj₁ h with ⟫-view (⊤ ⊢ Open) ((Maybe Char) ⊢ Open) h 
FileSystem-view X .Open x | μv p₁ | inj₂ p₂ | inj₁ h | hoare (witness tt) k = getChar-view k
FileSystem-view X s x | μv p₁ | inj₂ p₂ | inj₂ h with ⟫-view (⊤ ⊢ Open) (⊤ ⊢ Closed) h
FileSystem-view X .Open x | μv p₁ | inj₂ p₂ | inj₂ h | hoare (witness tt) k = closeFile-view k

-- ** Command interpreter

-- Given a term in the FileSystem monad (intuitively, the syntax tree
-- of an effectful program), we can run it by actually calling the
-- unsafe 'fopen', 'getc' and 'fclose' operations.

postulate
  runFileSystem : {A : Set} → FileSystem (A ⊢ Closed) Closed → A

mutual

  -- runFileSystem {A} x with FileSystem-view (A ⊢ Closed) Closed x 
  -- runFileSystem x | fsReturn-view (witness wit) = wit
  -- runFileSystem x | openFile-view filename k = maybe (openedFileSystem (k Open tt))
  --                                                    (runFileSystem (k Closed tt)) 
  --                                                    (fopen filename)

  openedFileSystem : {A : Set} → FileSystem (A ⊢ Closed) Open → FileHandle → A
  openedFileSystem {A} x fh with FileSystem-view (A ⊢ Closed) Open x 
  openedFileSystem x fh | fsReturn-view ()
  openedFileSystem x fh | closeFile-view k = runFileSystem (k Closed (witness (fclose fh)))
  openedFileSystem x fh | getChar-view k = openedFileSystem (k Open (witness (getc fh))) fh

  -- NOTE: the fact that I'm using a view seems to confuse
  -- the termination checker: if you write this definition by deep
  -- pattern-matching, it does not go salmon.

-- ** Examples

-- *** Reading an open file

readOpenFile : ℕ → FileSystem (String ⊢ Open) Open
readOpenFile 0 = fsReturn ""
readOpenFile (suc n) = getChar =⟫= nextChar
  where nextChar : Maybe Char → FileSystem (String ⊢ Open) Open
        nextChar (just x) = readOpenFile n =⟫= \s → 
                            fsReturn ((fromList (x ∷ [])) ++ s)
        nextChar nothing = fsReturn ""

-- *** Reading the content of a file

fileContents : Filename → ℕ → FileSystem (Maybe String ⊢ Closed) Closed
fileContents filename n = openFile filename ?⟫= ifOpened
  where ifOpened : (s' : State) → ⊤ → FileSystem (Maybe String ⊢ Closed) s'
        ifOpened Open tt =  readOpenFile n =⟫= \ s → 
                            closeFile =⟫= \ _ → 
                            fsReturn (just s)
        ifOpened Closed tt = fsReturn nothing 

-- * Outro

-- Local Variables:
-- mode: outline-minor
-- outline-regexp: "-- [*\f]+"
-- outline-level: outline-level
-- End:                      
