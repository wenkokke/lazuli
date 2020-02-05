{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.Prelude where

import Prelude hiding
  ( all
  , and
  , any
  , div
  , drop
  , foldr
  , length
  , min
  , map
  , max
  , or
  , replicate
  , sum
  , take
  , zipWith
  )


-- * Predicates

type R = Double

{-@ type Pos = {n:Int | n > 0} @-}
{-@ type Rpos = {x:R | x > 0} @-}

{-@ type TRUE = {v:Bool | v} @-}


-- * Primitives

-- These functions exist because the SMT operators (+), (*), (=), etc, cannot be partially applied in the SMT language. This leads to problems with the reflection of higher-order functions, e.g., `map (+)`. For these cases, you can use `map plus` instead.

{-# NOINLINE plus #-}
{-@ reflect plus @-}
{-@ plus :: Num a => a -> a -> a @-}
plus :: Num a => a -> a -> a
plus x y = x + y

{-# NOINLINE minus #-}
{-@ reflect minus @-}
{-@ minus :: Num a => a -> a -> a @-}
minus :: Num a => a -> a -> a
minus x y = x - y

{-# NOINLINE times #-}
{-@ reflect times @-}
{-@ times :: Num a => a -> a -> a @-}
times :: Num a => a -> a -> a
times x y = x * y

{-# NOINLINE rdiv #-}
{-@ reflect rdiv @-}
{-@ rdiv :: Fractional a => x:a -> y:{v:a | v /= 0} -> {v:a | v = x / y} @-}
rdiv :: Fractional a => a -> a -> a
rdiv x y = x / y

{-@ reflect max @-}
{-@ max :: Ord a => x:a -> y:a -> {v:a | v >= x && v >= y} @-}
max :: Ord a => a -> a -> a
max x y = if x `geq` y then x else y

{-@ reflect min @-}
{-@ min :: Ord a => x:a -> y:a -> {v:a | v <= x && v <= y} @-}
min :: Ord a => a -> a -> a
min x y = if x `leq` y then x else y

{-# NOINLINE lt #-}
{-@ reflect lt @-}
{-@ lt :: Ord a => a -> a -> Bool @-}
lt :: Ord a => a -> a -> Bool
lt x y = x < y

{-# NOINLINE leq #-}
{-@ reflect leq @-}
{-@ leq :: Ord a => a -> a -> Bool @-}
leq :: Ord a => a -> a -> Bool
leq x y = x <= y

{-# NOINLINE eq #-}
{-@ reflect eq @-}
{-@ eq :: Ord a => a -> a -> Bool @-}
eq :: Ord a => a -> a -> Bool
eq x y = x >= y

{-# NOINLINE geq #-}
{-@ reflect geq @-}
{-@ geq :: Ord a => a -> a -> Bool @-}
geq :: Ord a => a -> a -> Bool
geq x y = x >= y

{-# NOINLINE gt #-}
{-@ reflect gt @-}
{-@ gt :: Ord a => a -> a -> Bool @-}
gt :: Ord a => a -> a -> Bool
gt x y = x > y

{-@ reflect &&& @-}
{-@ (&&&) :: Bool -> Bool -> Bool @-}
(&&&) :: Bool -> Bool -> Bool
False &&& _     = False
True  &&& True  = True
True  &&& False = False

{-@ reflect ||| @-}
{-@ (|||) :: Bool -> Bool -> Bool @-}
(|||) :: Bool -> Bool -> Bool
True  ||| _     = True
False ||| True  = True
False ||| False = False


-- * Lists

type List a = [a]

{-@ reflect length @-}
{-@ length :: List a -> Nat @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

{-@ type ListNE a   = {l:List a | length l > 0} @-}
{-@ type ListN  a N = {l:List a | length l == N} @-}
{-@ type ListX  a X = ListN a (length X) @-}

{-@ reflect foldr @-}
{-@ foldr :: f:(a -> b -> b) -> z:b -> xs:List a -> b @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ e []     = e
foldr f e (x:xs) = f x (foldr f e xs)

{-@ reflect sum @-}
{-@ sum :: List R -> R @-}
sum :: List R -> R
sum = foldr plus 0

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
{-@ drop :: n:Nat -> l:{v:List a | n <= length v} -> {v:List a | length v == length l - n} @-}
drop :: Int -> List a -> List a
drop 0 xs     = xs
drop n (_:xs) = drop (n - 1) xs

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> x:a -> ListN a n @-}
replicate :: Int -> a -> List a
replicate 0 x = []
replicate n x = x : replicate (n - 1) x

{-@ reflect append @-}
{-@ append :: xs:List a -> ys:List a -> {v:List a | length v == length xs + length ys} @-}
append :: List a -> List a -> List a
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:List a -> ys:ListX b xs -> ListX c xs @-}
zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys
zipWith _ _      _      = []

{-@ flatten :: r:Nat -> c:Nat -> xss:ListN (ListN a c) r -> {v:List a | length v == r * c} @-}
flatten :: Int -> Int -> List (List a) -> List a
flatten r c (xs:xss) | r > 0 = xs `append` flatten (r - 1) c xss
flatten _ _ _                = []

{-@ reflect singleton @-}
{-@ singleton :: a -> ListN a 1 @-}
singleton :: a -> List a
singleton x = [x]

{-@ reflect all @-}
{-@ all :: (a -> Bool) -> List a -> Bool @-}
all :: (a -> Bool) -> List a -> Bool
all p xs = foldr (&&&) True (map p xs)

{-@ reflect any @-}
{-@ any :: (a -> Bool) -> List a -> Bool @-}
any :: (a -> Bool) -> List a -> Bool
any p xs = foldr (|||) False (map p xs)
