module Tutorial where

import Prelude hiding (tail, take, min)

{-@ ex1 :: { i : Int | i >= 60 && i < 105 } @-}
ex1 :: Int
ex1 = 61

{-@ tail :: { xs : [a] | len xs > 0 } -> { ys : [a] | len ys == len xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : xs) = xs
tail _        = impossible "impossible: tail on empty list"

{-@ example :: { xs : [a] | len xs >= 4 } -> { ys : [a] | len ys < len xs } @-}
example :: [a] -> [a]
example xs = tail (tail (tail (tail xs)))

{-@ list :: { xs : [Int] | len xs == 3 } @-}
list :: [Int]
list = [1,2,3]

{-@ type Nat' = { n : Int | n >= 0 } @-}

{-@ type GT N = { n : Int | n > N } @-}

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

type Nat = Int
{-@ take :: n : Nat -> { xs : [a] | len xs >= n } -> { rs : [a] | len rs == n } @-}
-- {-@ take :: n : Nat -> xs : [a] -> { rs : [a] | len rs == min n (len xs) } @-}
take :: Nat -> [a] -> [a]
take i xs
  | i == 0      = []
take i []       = []
take i (x : xs) = x : take (i - 1) xs

data Weekday = Mo | Tu | We | Th | Fr | Sa | Su

{-@ type WeekendDay = { w : Weekday | w == Sa || w == Su } @-}

{-@ weekday :: WeekendDay @-}
weekday :: Weekday
weekday = Sa

{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible message = error message

{-@ x :: { xs : [ { i : Int | i == 2 } ] | len xs == 5 } @-}
x :: [Int]
x = replicate 5 2
