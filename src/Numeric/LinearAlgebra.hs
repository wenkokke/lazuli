{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Numeric.LinearAlgebra where

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

import Numeric.LinearAlgebra.Internal (R, List, length, plus, times, geq)
import qualified Numeric.LinearAlgebra.Internal as Internal


-- * Vectors

data Vector a = V
  { size   :: !Int
  , toList :: List a
  }
  deriving (Eq)

instance Show a => Show (Vector a) where
  showsPrec p (V n xs) =
    showsPrec p n . showString " |> " . showsPrec p xs

{-@
data Vector a = V
  { size   :: Nat
  , toList :: ListN a size
  }
@-}

{-@ type VectorN a N = {v:Vector a | size v = N} @-}
{-@ type VectorX a X = VectorN a (size X) @-}

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
{-@ append :: xs:Vector a -> ys:Vector a -> VectorN a {size xs + size ys} @-}
append :: Vector a -> Vector a -> Vector a
append (V n xs) (V m ys) = V (n + m) (xs `Internal.append` ys)

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:Vector a -> ys:VectorX b xs -> VectorX c xs @-}
zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f (V n xs) (V _ ys) = V n (Internal.zipWith f xs ys)

{-@ reflect flatten @-}
{-@ flatten :: xss:Matrix a -> VectorN a {rows xss * cols xss} @-}
flatten :: Matrix a -> Vector a
flatten (M r c xss) = V (r * c) (Internal.flatten r c xss)


-- * Matrices

data Matrix a = M
  { rows    :: !Int
  , cols    :: !Int
  , toLists :: List (List a)
  }
  deriving (Eq)

{-@
data Matrix a = M
  { rows    :: Nat
  , cols    :: Nat
  , toLists :: ListN (ListN a cols) rows
  }
@-}

{-@ type MatrixN a R C = {v:Matrix a | rows v = R && cols v = C} @-}
{-@ type MatrixX a X   = MatrixN a {rows X} {cols X} @-}

{-@ reflect matrix @-}
{-@ matrix :: r:Nat -> c:Nat -> ListN a {r * c} -> MatrixN a r c @-}
matrix :: Int -> Int -> List a -> Matrix a
matrix r c xss = M r c (Internal.matrix r c xss)

{-@ reflect >< @-}
{-@ (><) :: r:Nat -> c:Nat -> ListN a {r * c} -> MatrixN a r c @-}
(><) :: Int -> Int -> List a -> Matrix a
(><) = matrix


-- * Linear Algebra

{-@ reflect asRow @-}
{-@ asRow :: xs:Vector Double -> MatrixN Double 1 {size xs} @-}
asRow :: Vector Double -> Matrix Double
asRow (V c xs) = M 1 c (Internal.asRow xs)

{-@ reflect asColumn @-}
{-@ asColumn :: xs:Vector Double -> MatrixN Double {size xs} 1 @-}
asColumn :: Vector Double -> Matrix Double
asColumn (V r xs) = M r 1 (Internal.asColumn xs)

{-@ reflect dot @-}
{-@ dot :: xs:Vector Double -> ys:VectorX Double xs -> Double @-}
dot :: Vector Double -> Vector Double -> Double
dot vx vy = Internal.dot (toList vx) (toList vy)

{-@ reflect <.> @-}
{-@ (<.>) :: xs:Vector Double -> ys:VectorX Double xs -> Double @-}
(<.>) :: Vector Double -> Vector Double -> Double
(<.>) = dot

{-@ reflect vAv @-}
{-@ vAv :: xs:Vector Double -> ys:VectorX Double xs -> VectorX Double xs @-}
vAv :: Vector Double -> Vector Double -> Vector Double
vAv (V n xs) (V _ ys) = V n (xs `Internal.vAv` ys)

{-@ reflect <+> @-}
{-@ (<+>) :: xs:Vector Double -> ys:VectorX Double xs -> VectorX Double xs @-}
(<+>) :: Vector Double -> Vector Double -> Vector Double
(<+>) = vAv

{-@ reflect sAv @-}
{-@ sAv :: x:Double -> ys:Vector Double -> VectorX Double ys @-}
sAv :: Double -> Vector Double -> Vector Double
sAv x (V n ys) = V n (x `Internal.sAv` ys)

{-@ reflect +> @-}
{-@ (+>) :: x:Double -> ys:Vector Double -> VectorX Double ys @-}
(+>) :: Double -> Vector Double -> Vector Double
(+>) = sAv

{-@ reflect scale @-}
{-@ scale :: x:Double -> ys:Vector Double -> VectorX Double ys @-}
scale :: Double -> Vector Double -> Vector Double
scale x (V n ys) = V n (Internal.scale x ys)

{-@ reflect vXm @-}
{-@ vXm :: xs:Vector Double -> yss:{yss:Matrix Double | size xs = rows yss} -> VectorN Double {cols yss} @-}
vXm :: Vector Double -> Matrix Double -> Vector Double
vXm (V r xs) (M _ c yss) = V c (Internal.vXm r c xs yss)

{-@ reflect <# @-}
{-@ (<#) :: xs:Vector Double -> yss:{yss:Matrix Double | size xs = rows yss} -> VectorN Double {cols yss} @-}
(<#) :: Vector Double -> Matrix Double -> Vector Double
(<#) = vXm

{-@ reflect mXm @-}
{-@ mXm :: xss:Matrix Double -> yss:{yss:Matrix Double | cols xss = rows yss} -> MatrixN Double {rows xss} {cols yss} @-}
mXm :: Matrix Double -> Matrix Double -> Matrix Double
mXm (M i j xss) (M _ k yss) = M i k (Internal.mXm i j k xss yss)

{-@ reflect <#> @-}
{-@ (<#>) :: xss:Matrix Double -> yss:{yss:Matrix Double | cols xss = rows yss} -> MatrixN Double {rows xss} {cols yss} @-}
(<#>) :: Matrix Double -> Matrix Double -> Matrix Double
(<#>) = mXm

{-@ reflect mXv @-}
{-@ mXv :: xss:Matrix Double -> ys:VectorN Double (cols xss) -> VectorN Double (rows xss) @-}
mXv :: Matrix Double -> Vector Double -> Vector Double
mXv xss ys = flatten (xss <#> asColumn ys)

{-@ reflect #> @-}
{-@ (#>) :: xss:Matrix Double -> ys:VectorN Double (cols xss) -> VectorN Double (rows xss) @-}
(#>) :: Matrix Double -> Vector Double -> Vector Double
(#>) = mXv

{-@ reflect outer @-}
{-@ outer :: xs:Vector Double -> ys:Vector Double -> MatrixN Double {size xs} {size ys} @-}
outer :: Vector Double -> Vector Double -> Matrix Double
outer xs ys = asColumn xs <#> asRow ys
