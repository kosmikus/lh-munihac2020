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

insert :: Ord a => a -> [a] -> [a]
insert x []       = [x]
insert x (y : ys)
  | x <= y        = x : y : ys
  | otherwise     = y : insert x ys

isort :: Ord a => [a] -> [a]
isort = foldr insert []

data SortedList a = Nil | a :<= SortedList a
infixr 5 :<=

{-@ data SortedList a = Nil | (:<=) { hd :: a, tl :: SortedList { x : a | hd <= x } } @-}

exampleSorted :: SortedList Int
exampleSorted = 2 :<= 3 :<= 4 :<= Nil

insert' :: Ord a => a -> SortedList a -> SortedList a
insert' x Nil     = x :<= Nil
insert' x (y :<= ys)
  | x <= y        = x :<= y :<= ys
  | otherwise     = y :<= insert' x ys

{-@ insert'' :: forall < p :: Int -> Bool > . Int<p> -> SortedList (Int<p>) -> SortedList (Int<p>) @-}
insert'' :: Int -> SortedList Int -> SortedList Int
insert'' x Nil     = x :<= Nil
insert'' x (y :<= ys)
  | x <= y        = x :<= y :<= ys
  | otherwise     = y :<= insert'' x ys

{-@ assume plus :: x : Int -> y : Int -> { z : Int | z == x + y } @-}
plus :: Int -> Int -> Int
plus = (+)

-- foldr :: (a -> r -> r) -> r -> [a] -> r

isort' :: Ord a => [a] -> SortedList a
isort' = foldr insert' Nil

{-@ type SortedList' a = [a]<{\ x y -> x <= y }> @-}

{-@ example' :: SortedList' Integer @-}
example' :: [Integer]
example' = [1,4,5]

{-@ merge :: Ord a => xs : SortedList' a -> ys : SortedList' a -> SortedList' a / [ len xs , len ys ] @-}
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys   = ys
merge xs []   = xs
merge (x : xs) (y : ys)
  | x <= y    = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

{-@ msort :: Ord a => [a] -> SortedList' a @-}
msort :: Ord a => [a] -> [a]
msort []  = []
msort [x] = [x]
msort xs  =
  case split xs of
  -- case splitAt (length xs `div` 2) xs of
    (ys, zs) -> merge (msort ys) (msort zs)

{-@ split :: xs : [a] ->
       { r : ([a], [a]) | (len (fst r) + len (snd r) == len xs)
                      && ((len xs >= 2) => (len (fst r) > 0) && (len (snd r) > 0)) } @-}
split :: [a] -> ([a], [a])
split []           = ([], [])
split [x]          = ([x], [])
split (a : b : rs) = (a : as, b : bs)
  where
    (as, bs) = split rs

{-@ measure validEmail :: String -> Bool @-}
