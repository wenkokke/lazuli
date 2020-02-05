{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.LinearAlgebra where

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

import           Leadbeater.Prelude (List, R, plus)
import qualified Leadbeater.Prelude as Internal
import qualified Leadbeater.LinearAlgebra.Internal as Internal



-- * Vectors

data Vector a = V
  { size   :: !Int
  , toList :: List a
  }

instance Show a => Show (Vector a) where
  showsPrec p (V n xs) =
    showsPrec p n . showString " |> " . showsPrec p xs

{-@
data Vector a = V
  { size   :: Nat
  , toList :: ListN a size
  }
@-}

{-@ type VectorNE a   = {v:Vector a | size v > 0} @-}
{-@ type VectorN  a N = {v:Vector a | size v == N} @-}
{-@ type VectorX  a X = VectorN a (size X) @-}

{-@ reflect vector @-}
{-@ vector :: n:Nat -> l:ListN a n -> VectorN a n @-}
vector :: Int -> List a -> Vector a
vector = V

{-@ reflect |> @-}
{-@ (|>) :: n:Nat -> l:ListN a n -> VectorN a n @-}
(|>) :: Int -> List a -> Vector a
(|>) = vector

{-@ reflect foldr @-}
{-@ foldr :: f:(a -> b -> b) -> z:b -> xs:Vector a -> b @-}
foldr :: (a -> b -> b) -> b -> Vector a -> b
foldr f e (V _ xs) = Internal.foldr f e xs

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:Vector a -> ys:VectorX b xs @-}
map :: (a -> b) -> Vector a -> Vector b
map f (V n xs) = V n (Internal.map f xs)

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> x:a -> VectorN a n @-}
replicate :: Int -> a -> Vector a
replicate n x = V n (Internal.replicate n x)

{-@ reflect append @-}
{-@ append :: xs:Vector a -> ys:Vector a -> {v:Vector a | size v == size xs + size ys} @-}
append :: Vector a -> Vector a -> Vector a
append (V n xs) (V m ys) = V (n + m) (xs `Internal.append` ys)

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:Vector a -> ys:VectorX b xs -> VectorX c xs @-}
zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f (V n xs) (V _ ys) = V n (Internal.zipWith f xs ys)

{-@ reflect flatten @-}
{-@ flatten :: xss:Matrix a -> {v:Vector a | size v == rows xss * cols xss} @-}
flatten :: Matrix a -> Vector a
flatten (M r c xss) = V (r * c) (Internal.flatten r c xss)

{-@ reflect all @-}
{-@ all :: (a -> Bool) -> Vector a -> Bool @-}
all :: (a -> Bool) -> Vector a -> Bool
all p (V _ xs) = Internal.all p xs

{-@ reflect any @-}
{-@ any :: (a -> Bool) -> Vector a -> Bool @-}
any :: (a -> Bool) -> Vector a -> Bool
any p (V _ xs) = Internal.any p xs

{-@ reflect sum @-}
{-@ sum :: Vector R -> R @-}
sum :: Vector R -> R
sum xs = foldr plus 0.0 xs

{-@ reflect sumPos @-}
{-@ sumPos :: VectorNE Rpos -> Rpos @-}
sumPos :: Vector R -> R
sumPos (V _ xs) = Internal.sumPos xs


-- * Matrices

data Matrix a = M
  { rows    :: Int
  , cols    :: Int
  , toLists :: List (List a)
  }

{-@
data Matrix a = M
  { rows    :: Nat
  , cols    :: Nat
  , toLists :: ListN (ListN a cols) rows
  }
@-}

{-@ type MatrixNE a     = {v:Matrix a | rows v > 0 && cols v > 0} @-}
{-@ type MatrixN  a R C = {v:Matrix a | rows v == R && cols v == C} @-}
{-@ type MatrixX  a X   = MatrixN a (rows X) (cols X) @-}

{-@ reflect matrix @-}
{-@ matrix :: r:Nat -> c:Nat -> {v:List a | length v == r * c} -> MatrixN a r c @-}
matrix :: Int -> Int -> List a -> Matrix a
matrix r c xss = M r c (Internal.matrix r c xss)

{-@ reflect >< @-}
{-@ (><) :: r:Nat -> c:Nat -> {v:List a | length v == r * c} -> MatrixN a r c @-}
(><) :: Int -> Int -> List a -> Matrix a
(><) = matrix


-- * Linear Algebra

{-@ reflect asRow @-}
{-@ asRow :: xs:Vector R -> {v:Matrix R | rows v == 1 && cols v == size xs} @-}
asRow :: Vector R -> Matrix R
asRow (V c xs) = M 1 c (Internal.asRow xs)

{-@ reflect asColumn @-}
{-@ asColumn :: xs:Vector R -> {v:Matrix R | rows v == size xs && cols v == 1} @-}
asColumn :: Vector R -> Matrix R
asColumn (V r xs) = M r 1 (Internal.asColumn xs)

{-@ reflect dot @-}
{-@ dot :: xs:Vector R -> ys:VectorX R xs -> R @-}
dot :: Vector R -> Vector R -> R
dot vx vy = Internal.dot (toList vx) (toList vy)

{-@ reflect <.> @-}
{-@ (<.>) :: xs:Vector R -> ys:VectorX R xs -> R @-}
(<.>) :: Vector R -> Vector R -> R
(<.>) = dot

{-@ reflect vAv @-}
{-@ vAv :: xs:Vector R -> ys:VectorX R xs -> VectorX R xs @-}
vAv :: Vector R -> Vector R -> Vector R
vAv (V n xs) (V _ ys) = V n (xs `Internal.vAv` ys)

{-@ reflect <+> @-}
{-@ (<+>) :: xs:Vector R -> ys:VectorX R xs -> VectorX R xs @-}
(<+>) :: Vector R -> Vector R -> Vector R
(<+>) = vAv

{-@ reflect sAv @-}
{-@ sAv :: x:R -> ys:Vector R -> VectorX R ys @-}
sAv :: R -> Vector R -> Vector R
sAv x (V n ys) = V n (x `Internal.sAv` ys)

{-@ reflect +> @-}
{-@ (+>) :: x:R -> ys:Vector R -> VectorX R ys @-}
(+>) :: R -> Vector R -> Vector R
(+>) = sAv

{-@ reflect scale @-}
{-@ scale :: x:R -> ys:Vector R -> VectorX R ys @-}
scale :: R -> Vector R -> Vector R
scale x (V n ys) = V n (Internal.scale x ys)

{-@ reflect vXm @-}
{-@ vXm :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R (cols yss) @-}
vXm :: Vector R -> Matrix R -> Vector R
vXm (V r xs) (M _ c yss) = V c (Internal.vXm r c xs yss)

{-@ reflect <# @-}
{-@ (<#) :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R (cols yss) @-}
(<#) :: Vector R -> Matrix R -> Vector R
(<#) = vXm

{-@ reflect mXm @-}
{-@ mXm :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R (rows xss) (cols yss) @-}
mXm :: Matrix R -> Matrix R -> Matrix R
mXm (M i j xss) (M _ k yss) = M i k (Internal.mXm i j k xss yss)

{-@ reflect <#> @-}
{-@ (<#>) :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R (rows xss) (cols yss) @-}
(<#>) :: Matrix R -> Matrix R -> Matrix R
(<#>) = mXm

{-@ reflect mXv @-}
{-@ mXv :: xss:Matrix R -> ys:VectorN R (cols xss) -> VectorN R (rows xss) @-}
mXv :: Matrix R -> Vector R -> Vector R
mXv xss ys = flatten (xss <#> asColumn ys)

{-@ reflect #> @-}
{-@ (#>) :: xss:Matrix R -> ys:VectorN R (cols xss) -> VectorN R (rows xss) @-}
(#>) :: Matrix R -> Vector R -> Vector R
(#>) = mXv
