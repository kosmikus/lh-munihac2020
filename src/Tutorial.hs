module Tutorial where

-- This is a skeleton for the MuniHac 2020 Liquid Haskell Tutorial.
--
-- The following definition should typecheck. If you change either
-- of the arguments of the call to replicate from 5 and 2 to some other
-- number, there should be a Liquid Haskell type error.

{-@ x :: { xs : [ { x : Int | x == 2 } ] | len xs == 5 } @-}
x :: [Int]
x = replicate 5 2
