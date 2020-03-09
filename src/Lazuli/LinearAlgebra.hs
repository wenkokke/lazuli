{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Lazuli.LinearAlgebra where

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

import           Lazuli.Prelude (List, R, plus)
import qualified Lazuli.Prelude as Internal
import qualified Lazuli.LinearAlgebra.Internal as Internal


-- * Lists

-- Useful for annotating lists with their length, if LH has trouble.
{-@ reflect |> @-}
{-@ (|>) :: n:Nat -> ListN R n -> ListN R n @-}
(|>) :: Int -> List R -> List R
_ |> xs = xs


-- * Vectors

infix 3 :>

data Vector a = (:>)
  { size   :: !Int
  , toList :: List a
  }
  deriving (Eq)

instance Show a => Show (Vector a) where
  showsPrec p (n :> xs) =
    showsPrec p n . showString " :> " . showsPrec p xs

{-@
data Vector a = (:>)
  { size   :: Nat
  , toList :: ListN a size
  }
@-}

{-@ type VectorNE a   = {v:Vector a | size v > 0} @-}
{-@ type VectorN  a N = {v:Vector a | size v == N} @-}
{-@ type VectorX  a X = VectorN a {size X} @-}

{-@ reflect foldr @-}
{-@ foldr :: f:(a -> b -> b) -> z:b -> xs:Vector a -> b @-}
foldr :: (a -> b -> b) -> b -> Vector a -> b
foldr f e xs = Internal.foldr f e (toList xs)

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:Vector a -> VectorX b xs @-}
map :: (a -> b) -> Vector a -> Vector b
map f xs = size xs :> Internal.map f (toList xs)

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> VectorN a n @-}
replicate :: Int -> a -> Vector a
replicate n x = n :> Internal.replicate n x

{-@ reflect append @-}
{-@ append :: xs:Vector a -> ys:Vector a -> VectorN a {size xs + size ys} @-}
append :: Vector a -> Vector a -> Vector a
xs `append` ys = size xs + size ys :> toList xs `Internal.append` toList ys

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:Vector a -> VectorX b xs -> VectorX c xs @-}
zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f xs ys = size xs :> Internal.zipWith f (toList xs) (toList ys)

{-@ reflect all @-}
{-@ all :: (a -> Bool) -> Vector a -> Bool @-}
all :: (a -> Bool) -> Vector a -> Bool
all p xs = Internal.all p (toList xs)

{-@ reflect any @-}
{-@ any :: (a -> Bool) -> Vector a -> Bool @-}
any :: (a -> Bool) -> Vector a -> Bool
any p xs = Internal.any p (toList xs)

{-@ reflect sum @-}
{-@ sum :: Vector R -> R @-}
sum :: Vector R -> R
sum xs = foldr plus 0.0 xs

{-@ reflect sumPos @-}
{-@ sumPos :: VectorNE Rpos -> Rpos @-}
sumPos :: Vector R -> R
sumPos xs = Internal.sumPos (toList xs)


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
{-@ type MatrixX  a X   = MatrixN a {rows X} {cols X} @-}

{-@ reflect >< @-}
{-@ (><) :: r:Nat -> c:Nat -> ListN (ListN a c) r -> MatrixN a r c @-}
(><) :: Int -> Int -> List (List a) -> Matrix a
(r >< c) xss = M r c xss

-- * Linear Algebra

{-@ reflect asRow @-}
{-@ asRow :: xs:Vector R -> MatrixN R 1 {size xs} @-}
asRow :: Vector R -> Matrix R
asRow xs = M
  { rows = 1
  , cols = size xs
  , toLists = Internal.asRow (toList xs)
  }

{-@ reflect asColumn @-}
{-@ asColumn :: xs:Vector R -> MatrixN R {size xs} 1 @-}
asColumn :: Vector R -> Matrix R
asColumn xs = M
  { rows = size xs
  , cols = 1
  , toLists = Internal.asColumn (toList xs)
  }

{-@ reflect dot @-}
{-@ dot :: xs:Vector R -> ys:VectorX R xs -> R @-}
dot :: Vector R -> Vector R -> R
dot xs ys = Internal.dot (toList xs) (toList ys)

{-@ reflect <.> @-}
{-@ (<.>) :: xs:Vector R -> ys:VectorX R xs -> R @-}
(<.>) :: Vector R -> Vector R -> R
xs <.> ys = xs `dot` ys

{-@ reflect vAv @-}
{-@ vAv :: xs:Vector R -> VectorX R xs -> VectorX R xs @-}
vAv :: Vector R -> Vector R -> Vector R
xs `vAv` ys = size xs :> (toList xs `Internal.vAv` toList ys)

{-@ reflect <+> @-}
{-@ (<+>) :: xs:Vector R -> VectorX R xs -> VectorX R xs @-}
(<+>) :: Vector R -> Vector R -> Vector R
xs <+> ys = xs `vAv` ys

{-@ reflect sAv @-}
{-@ sAv :: R -> ys:Vector R -> VectorX R ys @-}
sAv :: R -> Vector R -> Vector R
x `sAv` ys = size ys :> (x `Internal.sAv` toList ys)

{-@ reflect +> @-}
{-@ (+>) :: R -> ys:Vector R -> VectorX R ys @-}
(+>) :: R -> Vector R -> Vector R
x +> ys = x `sAv` ys

{-@ reflect scale @-}
{-@ scale :: R -> ys:Vector R -> VectorX R ys @-}
scale :: R -> Vector R -> Vector R
scale x ys = size ys :> Internal.scale x (toList ys)

{-@ reflect vXm @-}
{-@ vXm :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R {cols yss} @-}
vXm :: Vector R -> Matrix R -> Vector R
vXm xs yss = cols yss :> Internal.vXm (rows yss) (cols yss) (toList xs) (toLists yss)

{-@ reflect <# @-}
{-@ (<#) :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R {cols yss} @-}
(<#) :: Vector R -> Matrix R -> Vector R
xs <# yss = xs `vXm` yss

{-@ reflect mXm @-}
{-@ mXm :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R {rows xss} {cols yss} @-}
mXm :: Matrix R -> Matrix R -> Matrix R
mXm xss yss = M
  { rows = rows xss
  , cols = cols yss
  , toLists = Internal.mXm (rows xss) (cols xss) (cols yss) (toLists xss) (toLists yss)
  }

{-@ reflect <#> @-}
{-@ (<#>) :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R {rows xss} {cols yss} @-}
(<#>) :: Matrix R -> Matrix R -> Matrix R
xss <#> yss = xss `mXm` yss
