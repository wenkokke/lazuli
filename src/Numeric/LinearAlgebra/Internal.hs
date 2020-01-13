{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Numeric.LinearAlgebra.Internal where

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

type R = Double

{-# NO_INLINE #-}
{-@ reflect plus @-}
plus :: R -> R -> R
plus x y = x + y

{-# NO_INLINE #-}
{-@ reflect times @-}
times :: R -> R -> R
times x y = x * y

{-# NO_INLINE #-}
{-@ reflect geq @-}
geq :: R -> R -> Bool
geq x y = x >= y

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


-- * Linear Algebra

{-@ reflect matrix @-}
{-@ matrix :: r:Nat -> c:Nat -> xss:ListN a {r * c} -> ListN (ListN a c) r @-}
matrix :: Int -> Int -> List a -> List (List a)
matrix r c xss | r > 0 = take c xss : matrix (r - 1) c (drop c xss)
matrix _ _ _           = []

{-@ reflect asRow @-}
{-@ asRow :: xs:List R -> ListN (ListX R xs) 1 @-}
asRow :: List R -> List (List R)
asRow xs = [xs]

{-@ reflect asColumn @-}
{-@ asColumn :: xs:List R -> ListX (ListN R 1) xs @-}
asColumn :: List R -> List (List R)
asColumn xs = map singleton xs

{-@ reflect sum @-}
sum :: List R -> R
sum = foldr plus 0

{-@ reflect dot @-}
{-@ dot :: xs:List R -> ys:ListX R xs -> R @-}
dot :: List R -> List R -> R
dot xs ys = sum (zipWith times xs ys)

{-@ reflect vAv @-}
{-@ vAv :: xs:List R -> ys:ListX R xs -> ListX R xs @-}
vAv :: List R -> List R -> List R
vAv = zipWith plus

{-@ reflect sAv @-}
{-@ sAv :: x:R -> ys:List R -> ListX R ys @-}
sAv :: R -> List R -> List R
sAv x = map (plus x)

{-@ reflect scale @-}
{-@ scale :: x:R -> ys:List R -> ListX R ys @-}
scale :: R -> List R -> List R
scale x = map (times x)

{-@ reflect vXm @-}
{-@ vXm :: r:Nat -> c:Nat -> xs:ListN R r -> yss:ListN (ListN R c) r -> ListN R c @-}
vXm :: Int -> Int -> List R -> List (List R) -> List R
vXm r c (x:xs) (ys:yss) | r > 0 = scale x ys `vAv` vXm (r - 1) c xs yss
vXm _ c _      _                = replicate c 0

{-@ reflect mXm @-}
{-@ mXm :: i:Nat -> j:Nat -> k:Nat -> xss:ListN (ListN R j) i -> yss:ListN (ListN R k) j -> ListN (ListN R k) i @-}
mXm :: Int -> Int -> Int -> List (List R) -> List (List R) -> List (List R)
mXm i j k (xs:xss) yss | i > 0 = vXm j k xs yss : mXm (i - 1) j k xss yss
mXm _ _ _ _        _           = []

-- -}
-- -}
-- -}
-- -}
-- -}
