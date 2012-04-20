module Isomorphisms where
import Data.List
import Test.SmallCheck
import Test.SmallCheck.Series

data Foo = Foo1 | Foo2 Foo | Foo3 Foo
  deriving (Show, Eq)

instance Serial Foo where
  series = cons0 Foo1
        \/ cons1 Foo2
        \/ cons1 Foo3

testFoo :: Foo -> Bool
testFoo x = True

--------------------------------------------------------------------------------

data Bar = Bar1 | Bar2 (Either () ()) Bar
  deriving (Show, Eq)

instance Serial Bar where
  series = cons0 Bar1
        \/ cons2 Bar2

testBar :: Bar -> Bool
testBar x = True

--------------------------------------------------------------------------------

data Baz = Baz1 | Baz2 Bool Baz
  deriving (Show, Eq)

instance Serial Baz where
  series = cons0 Baz1
        \/ cons2 Baz2

testBaz :: Baz -> Bool
testBaz x = True

