module Induction where

-- Version of insertion sort written
-- using a generalised version of foldr, called ind.
--
-- With this, we can still derive that the sorted
-- list has the same length as the original list
-- without resorting to explicit recursion.

{-@ infix : @-}

{-@ ind :: forall a b < p :: [a] -> b -> Bool > .
      (xs : [a] -> x : a -> b <p xs> -> b <p (x : xs)>) ->
      b <p []> -> ys : [a] -> b <p ys>
@-}
ind :: ([a] -> a -> b -> b) -> b -> [a] -> b
ind op e [] = e
ind op e (x : xs) = op xs x (ind op e xs)

{-@ type SortedList a = [a]<{\ x y -> x <= y}> @-}

{-@ insert :: Ord a => a -> xs : SortedList a -> { rs : SortedList a | len rs == len xs + 1 } @-}
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y : ys)
  | x <= y    = x : y : ys
  | otherwise = y : insert x ys

{-@ isort :: Ord a => xs : [a] -> { rs : SortedList a | len rs == len xs } @-}
isort :: Ord a => [a] -> [a]
isort = ind (const insert) []

