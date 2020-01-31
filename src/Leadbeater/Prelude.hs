{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.Prelude where

import Prelude hiding
  ( drop
  , foldr
  , length
  , map
  , replicate
  , sum
  , take
  , zipWith
  )

{-@ type TRUE = {v:Bool | v} @-}

-- * Primitives

-- These functions exist because the SMT operators (+), (*), (=), etc, cannot be partially applied in the SMT language. This leads to problems with the reflection of higher-order functions, e.g., `map (+)`. For these cases, you can use `map plus` instead.

{-# NOINLINE plus #-}
{-@ reflect plus @-}
plus :: Num a => a -> a -> a
plus x y = x + y

{-# NOINLINE times #-}
{-@ reflect times @-}
times :: Num a => a -> a -> a
times x y = x * y

{-# NOINLINE eq #-}
{-@ reflect eq @-}
eq :: Ord a => a -> a -> Bool
eq x y = x >= y

{-# NOINLINE geq #-}
{-@ reflect geq @-}
geq :: Ord a => a -> a -> Bool
geq x y = x >= y

{-# NOINLINE (&&) #-}
{-@ reflect && @-}
(&&) :: Bool -> Bool -> Bool
True  && True  = True
True  && False = False
False && _     = False


-- * Lists

type List a = [a]

{-@ reflect length @-}
{-@ length :: List a -> Nat @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

{-@ type ListN a N = {l:List a | length l = N} @-}
{-@ type ListX a X = ListN a {length X} @-}

{-@ reflect foldr @-}
{-@ foldr :: f:(a -> b -> b) -> z:b -> xs:List a -> b @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ e []     = e
foldr f e (x:xs) = f x (foldr f e xs)

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:List a -> ListX b xs @-}
map :: (a -> b) -> List a -> List b
map f []     = []
map f (x:xs) = f x : map f xs

{-@ reflect take @-}
{-@ take :: n:Nat -> {l:List a | n <= length l} -> ListN a n @-}
take :: Int -> List a -> List a
take 0 xs     = []
take n (x:xs) = x : take (n - 1) xs

{-@ reflect drop @-}
{-@ drop :: n:Nat -> {l:List a | n <= length l} -> ListN a {length l - n} @-}
drop :: Int -> List a -> List a
drop 0 xs     = xs
drop n (_:xs) = drop (n - 1) xs

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> x:a -> ListN a n @-}
replicate :: Int -> a -> List a
replicate 0 x = []
replicate n x = x : replicate (n - 1) x

{-@ reflect append @-}
{-@ append :: xs:List a -> ys:List a -> ListN a {length xs + length ys} @-}
append :: List a -> List a -> List a
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:List a -> ys:ListX b xs -> ListX c xs @-}
zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys
zipWith _ _      _      = []

{-@ flatten :: r:Nat -> c:Nat -> xss:ListN (ListN a c) r -> ListN a {r * c} @-}
flatten :: Int -> Int -> List (List a) -> List a
flatten r c (xs:xss) | r > 0 = xs `append` flatten (r - 1) c xss
flatten _ _ _                = []

{-@ reflect singleton @-}
{-@ singleton :: a -> ListN a 1 @-}
singleton :: a -> List a
singleton x = [x]
