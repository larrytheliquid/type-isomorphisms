module Deriving where

data Foo = One | Two | Three
     deriving (Show, Eq, Ord, Enum)
