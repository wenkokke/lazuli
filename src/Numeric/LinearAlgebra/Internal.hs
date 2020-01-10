{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Numeric.LinearAlgebra.Internal where

import Prelude hiding ((<>), drop, map, length, replicate, take)

{-@ type Pos = {n:Nat | n > 0} @-}

type List a = [a]

{-@ type ListN  a N = {l:List a | len l = N} @-}
{-@ type ListX  a X = ListN a {len X} @-}

{-@ reflect take @-}
{-@ take :: n:Nat -> {l:List a | n <= len l} -> ListN a n @-}
take :: Int -> [a] -> [a]
take 0 xs     = []
take n (x:xs) = x : take (n - 1) xs

{-@ reflect drop @-}
{-@ drop :: n:Nat -> {l:List a | n <= len l} -> ListN a {len l - n} @-}
drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n - 1) xs

{-@ reflect matrix @-}
{-@ matrix :: r:Nat -> c:Nat -> xss:ListN a {r * c} -> ListN (ListN a c) r @-}
matrix :: Int -> Int -> [a] -> [[a]]
matrix 0 c []  = []
matrix r c xss = take c xss : matrix (r - 1) c (drop c xss)

{-@ reflect length @-}
{-@ length :: xs:List a -> {n:Nat | n = len xs} @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:List a -> ys:ListX b xs @-}
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = f x : map f xs

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> x:a -> ListN a n @-}
replicate :: Int -> a -> [a]
replicate 0 x = []
replicate n x = x : replicate (n - 1) x

{-@ reflect ap @-}
{-@ ap :: fs:List (a -> b) -> xs:ListX a fs -> ListX b fs @-}
ap :: [a -> b] -> [a] -> [b]
ap []     []     = []
ap (f:fs) (x:xs) = f x : ap fs xs

{-@ reflect append @-}
{-@ append :: xs:List a -> ys:List a -> ListN a {len xs + len ys} @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ reflect flatten @-}
{-@ flatten :: r:Nat -> c:Nat -> xss:ListN (ListN a c) r -> ListN a {r * c} @-}
flatten :: Int -> Int -> [[a]] -> [a]
flatten 0 c []       = []
flatten r c (xs:xss) = append xs (flatten (r - 1) c xss)

{-@ reflect dot @-}
{-@ dot :: xs:List Double -> ys:ListX Double xs -> Double @-}
dot :: [Double] -> [Double] -> Double
dot []     []     = 0
dot (x:xs) (y:ys) = x*y + dot xs ys

{-@ reflect add @-}
{-@ add :: xs:List Double -> ys:ListX Double xs -> ListX Double xs @-}
add :: [Double] -> [Double] -> [Double]
add []     []     = []
add (x:xs) (y:ys) = x + y : add xs ys

{-@ reflect scale @-}
{-@ scale :: x:Double -> ys:List Double -> ListX Double ys @-}
scale :: Double -> [Double] -> [Double]
scale _ []     = []
scale x (y:ys) = x * y : scale x ys

{-@ reflect vXm @-}
{-@ vXm :: r:Nat -> c:Nat -> xs:ListN Double r -> yss:ListN (ListN Double c) r -> ListN Double c @-}
vXm :: Int -> Int -> [Double] -> [[Double]] -> [Double]
vXm 0 c []     []       = replicate c 0
vXm r c (x:xs) (ys:yss) = add (scale x ys) (vXm (r - 1) c xs yss)

{-@ reflect mXm @-}
{-@ mXm :: i:Nat -> j:Nat -> k:Nat -> xss:ListN (ListN Double j) i -> yss:ListN (ListN Double k) j -> ListN (ListN Double k) i @-}
mXm :: Int -> Int -> Int -> [[Double]] -> [[Double]] -> [[Double]]
mXm 0 j k [] yss = []
mXm i j k (xs:xss) yss = vXm j k xs yss : mXm (i - 1) j k xss yss
