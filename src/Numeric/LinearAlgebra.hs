{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Numeric.LinearAlgebra where

import Prelude hiding ((<>), map, replicate)
import qualified Numeric.LinearAlgebra.List as L

data Vector a = V
  { size   :: !Int
  , toList :: ![a]
  }
  deriving (Eq)

{-@
data Vector a = V
  { size   :: Nat
  , toList :: ListN a size
  }
@-}

{-@ type VectorN a N = {v:Vector a | size v = N} @-}
{-@ type VectorX a X = VectorN a {size X} @-}

{-@ reflect vector @-}
{-@ vector :: l:List a -> VectorN a {len l} @-}
vector :: [a] -> Vector a
vector xs = V (L.length xs) xs

data Matrix a = M
  { rows    :: !Int
  , cols    :: !Int
  , toLists :: ![[a]]
  }
  deriving (Eq)

{-@
data Matrix a = M
  { rows    :: Nat
  , cols    :: Nat
  , toLists :: ListN (ListN a cols) rows
  }
@-}

{-@ reflect matrix @-}
{-@ matrix :: r:Nat -> c:Nat -> ListN a {r * c} -> MatrixN a r c @-}
matrix :: Int -> Int -> [a] -> Matrix a
matrix r c xss = M r c (L.matrix r c xss)

{-@ type MatrixN a R C = {v:Matrix a | rows v = R && cols v = C} @-}
{-@ type MatrixX a X   = MatrixN a {rows X} {cols X} @-}

{-@ reflect asRow @-}
{-@ asRow :: xs:Vector Double -> MatrixN Double 1 {size xs} @-}
asRow :: Vector Double -> Matrix Double
asRow (V c xs) = M 1 c [xs]

{-@ reflect asColumn @-}
{-@ asColumn :: xs:Vector Double -> MatrixN Double {size xs} 1 @-}
asColumn :: Vector Double -> Matrix Double
asColumn (V r xs) = M r 1 (L.map (:[]) xs)

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:Vector a -> ys:VectorX b xs @-}
map :: (a -> b) -> Vector a -> Vector b
map f (V n xs) = V n (L.map f xs)

instance Functor Vector where
  fmap = map

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> x:a -> VectorN a n @-}
replicate :: Int -> a -> Vector a
replicate n x = V n (L.replicate n x)

{-@ reflect ap @-}
{-@ ap :: fs:Vector (a -> b) -> xs:VectorX a fs -> VectorX b fs @-}
ap :: Vector (a -> b) -> Vector a -> Vector b
ap (V n fs) (V _ xs) = V n (L.ap fs xs)

{-@ reflect append @-}
{-@ append :: xs:Vector a -> ys:Vector a -> VectorN a {size xs + size ys} @-}
append :: Vector a -> Vector a -> Vector a
append (V n xs) (V m ys) = V (n + m) (xs `L.append` ys)

{-@ reflect flatten @-}
{-@ flatten :: xss:Matrix a -> VectorN a {rows xss * cols xss} @-}
flatten :: Matrix a -> Vector a
flatten (M r c xss) = V (r * c) (L.flatten r c xss)

{-@ reflect dot @-}
{-@ dot :: xs:Vector Double -> ys:VectorX Double xs -> Double @-}
dot :: Vector Double -> Vector Double -> Double
dot vx vy = L.dot (toList vx) (toList vy)

{-@ reflect <.> @-}
{-@ (<.>) :: xs:Vector Double -> ys:VectorX Double xs -> Double @-}
(<.>) :: Vector Double -> Vector Double -> Double
(<.>) = dot

{-@ reflect add @-}
{-@ add :: xs:Vector Double -> ys:VectorX Double xs -> VectorX Double xs @-}
add :: Vector Double -> Vector Double -> Vector Double
add (V n xs) (V _ ys) = V n (xs `L.add` ys)

{-@ reflect scale @-}
{-@ scale :: x:Double -> ys:Vector Double -> VectorX Double ys @-}
scale :: Double -> Vector Double -> Vector Double
scale x (V n ys) = V n (L.scale x ys)

{-@ reflect vXm @-}
{-@ vXm :: xs:Vector Double -> yss:{yss:Matrix Double | size xs = rows yss} -> VectorN Double {cols yss} @-}
vXm :: Vector Double -> Matrix Double -> Vector Double
vXm (V r xs) (M _ c yss) = V c (L.vXm r c xs yss)

{-@ reflect <# @-}
{-@ (<#) :: xs:Vector Double -> yss:{yss:Matrix Double | size xs = rows yss} -> VectorN Double {cols yss} @-}
(<#) :: Vector Double -> Matrix Double -> Vector Double
(<#) = vXm

{-@ reflect mXm @-}
{-@ mXm :: xss:Matrix Double -> yss:{yss:Matrix Double | cols xss = rows yss} -> MatrixN Double {rows xss} {cols yss} @-}
mXm :: Matrix Double -> Matrix Double -> Matrix Double
mXm (M i j xss) (M _ k yss) = M i k (L.mXm i j k xss yss)

{-@ reflect <> @-}
{-@ (<>) :: xss:Matrix Double -> yss:{yss:Matrix Double | cols xss = rows yss} -> MatrixN Double {rows xss} {cols yss} @-}
(<>) :: Matrix Double -> Matrix Double -> Matrix Double
(<>) = mXm

{-@ reflect mXv @-}
{-@ mXv :: xss:Matrix Double -> ys:VectorN Double (cols xss) -> VectorN Double (rows xss) @-}
mXv :: Matrix Double -> Vector Double -> Vector Double
mXv xss ys = flatten (xss <> asColumn ys)

{-@ reflect #> @-}
{-@ (#>) :: xss:Matrix Double -> ys:VectorN Double (cols xss) -> VectorN Double (rows xss) @-}
(#>) :: Matrix Double -> Vector Double -> Vector Double
(#>) = mXv

{-@ reflect outer @-}
{-@ outer :: xs:Vector Double -> ys:Vector Double -> MatrixN Double {size xs} {size ys} @-}
outer :: Vector Double -> Vector Double -> Matrix Double
outer xs ys = asColumn xs <> asRow ys