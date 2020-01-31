{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.LinearAlgebra.Internal where

import Prelude hiding
  ( all
  , and
  , any
  , drop
  , foldr
  , length
  , map
  , or
  , replicate
  , sum
  , take
  , zipWith
  )

import Leadbeater.Prelude

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
