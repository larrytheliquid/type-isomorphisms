module Enum where
import Data.List
import Test.SmallCheck
import Test.SmallCheck.Series

height :: (Eq a, Serial a) => Series a
height 0 = series 0
height n = series n \\ series (pred n)

summer :: Integer -> (Integer -> Integer) -> Integer
summer 0 f = f 0
summer n f =  f n + summer (pred n) f

total :: Integer -> Integer -> Integer
total m 0 = 1
total m 1 = 1
total m d = (summer (d - 1) (total m) ^ m) - (summer (d - 2) (total m) ^ m)

pretty :: Show a => [a] -> IO ()
pretty xs = mapM_ (putStrLn . show) xs

data TwoX = One2X | Two2X TwoX | Three2X TwoX
  deriving (Show, Eq)

instance Serial TwoX where
  series = cons0 One2X
        \/ cons1 Two2X
        \/ cons1 Three2X

testTwoX :: TwoX -> Bool
testTwoX x = True

--------------------------------------------------------------------------------

data ThreeX = One3X | Two3X ThreeX | Three3X ThreeX | Four3X ThreeX
  deriving (Show, Eq)

instance Serial ThreeX where
  series = cons0 One3X
        \/ cons1 Two3X
        \/ cons1 Three3X
        \/ cons1 Four3X

testThreeX :: ThreeX -> Bool
testThreeX x = True

--------------------------------------------------------------------------------

data XTwo = OneX2 | TwoX2 XTwo XTwo
  deriving (Show, Eq)

instance Serial XTwo where
  series = cons0 OneX2
        \/ cons2 TwoX2

testXTwo :: XTwo -> Bool
testXTwo x = True

--------------------------------------------------------------------------------

data XThree = OneX3 | TwoX3 XThree XThree XThree
  deriving (Show, Eq)

instance Serial XThree where
  series = cons0 OneX3
        \/ cons3 TwoX3

testXThree :: XThree -> Bool
testXThree x = True

--------------------------------------------------------------------------------

data XTwoX = OneX2X | TwoX2X XTwoX XTwoX | ThreeX2X XTwoX XTwoX
  deriving (Show, Eq)

instance Serial XTwoX where
  series = cons0 OneX2X
        \/ cons2 TwoX2X
        \/ cons2 ThreeX2X

testXTwoX :: XTwoX -> Bool
testXTwoX x = True

--------------------------------------------------------------------------------

data XThreeX = OneX3X | TwoX3X XThreeX XThreeX XThreeX | ThreeX3X XThreeX XThreeX XThreeX
  deriving (Show, Eq)

instance Serial XThreeX where
  series = cons0 OneX3X
        \/ cons3 TwoX3X
        \/ cons3 ThreeX3X

testXThreeX :: XThreeX -> Bool
testXThreeX x = True


