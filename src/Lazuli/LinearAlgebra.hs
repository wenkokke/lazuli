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
foldr f e (_ :> xs) = Internal.foldr f e xs

{-@ reflect map @-}
{-@ map :: f:(a -> b) -> xs:Vector a -> VectorX b xs @-}
map :: (a -> b) -> Vector a -> Vector b
map f (n :> xs) = n :> Internal.map f xs

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> VectorN a n @-}
replicate :: Int -> a -> Vector a
replicate n x = n :> Internal.replicate n x

{-@ reflect append @-}
{-@ append :: xs:Vector a -> ys:Vector a -> VectorN a {size xs + size ys} @-}
append :: Vector a -> Vector a -> Vector a
(n :> xs) `append` (m :> ys) = n + m :> xs `Internal.append` ys

{-@ reflect zipWith @-}
{-@ zipWith :: f:(a -> b -> c) -> xs:Vector a -> VectorX b xs -> VectorX c xs @-}
zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f (n :> xs) (_ :> ys) = n :> Internal.zipWith f xs ys

{-@ reflect flatten @-}
{-@ flatten :: xss:Matrix a -> VectorN a {rows xss * cols xss} @-}
flatten :: Matrix a -> Vector a
flatten (M r c xss) = r * c :> Internal.flatten r c xss

{-@ reflect all @-}
{-@ all :: (a -> Bool) -> Vector a -> Bool @-}
all :: (a -> Bool) -> Vector a -> Bool
all p (_ :> xs) = Internal.all p xs

{-@ reflect any @-}
{-@ any :: (a -> Bool) -> Vector a -> Bool @-}
any :: (a -> Bool) -> Vector a -> Bool
any p (_ :> xs) = Internal.any p xs

{-@ reflect sum @-}
{-@ sum :: Vector R -> R @-}
sum :: Vector R -> R
sum xs = foldr plus 0.0 xs

{-@ reflect sumPos @-}
{-@ sumPos :: VectorNE Rpos -> Rpos @-}
sumPos :: Vector R -> R
sumPos (_ :> xs) = Internal.sumPos xs


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
(><) = M

-- * Linear Algebra

{-@ reflect asRow @-}
{-@ asRow :: xs:Vector R -> MatrixN R 1 {size xs} @-}
asRow :: Vector R -> Matrix R
asRow (c :> xs) = M 1 c (Internal.asRow xs)

{-@ reflect asColumn @-}
{-@ asColumn :: xs:Vector R -> MatrixN R {size xs} 1 @-}
asColumn :: Vector R -> Matrix R
asColumn (r :> xs) = M r 1 (Internal.asColumn xs)

{-@ reflect dot @-}
{-@ dot :: xs:Vector R -> ys:VectorX R xs -> R @-}
dot :: Vector R -> Vector R -> R
dot xs ys = Internal.dot (toList xs) (toList ys)

{-@ reflect <.> @-}
{-@ (<.>) :: xs:Vector R -> ys:VectorX R xs -> R @-}
(<.>) :: Vector R -> Vector R -> R
(<.>) = dot

{-@ reflect vAv @-}
{-@ vAv :: xs:Vector R -> VectorX R xs -> VectorX R xs @-}
vAv :: Vector R -> Vector R -> Vector R
(n :> xs) `vAv` (_ :> ys) = n :> (xs `Internal.vAv` ys)

{-@ reflect <+> @-}
{-@ (<+>) :: xs:Vector R -> VectorX R xs -> VectorX R xs @-}
(<+>) :: Vector R -> Vector R -> Vector R
(<+>) = vAv

{-@ reflect sAv @-}
{-@ sAv :: R -> ys:Vector R -> VectorX R ys @-}
sAv :: R -> Vector R -> Vector R
x `sAv` (n :> ys) = n :> (x `Internal.sAv` ys)

{-@ reflect +> @-}
{-@ (+>) :: R -> ys:Vector R -> VectorX R ys @-}
(+>) :: R -> Vector R -> Vector R
(+>) = sAv

{-@ reflect scale @-}
{-@ scale :: R -> ys:Vector R -> VectorX R ys @-}
scale :: R -> Vector R -> Vector R
scale x (n :> ys) = n :> Internal.scale x ys

{-@ reflect vXm @-}
{-@ vXm :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R {cols yss} @-}
vXm :: Vector R -> Matrix R -> Vector R
vXm (r :> xs) (M _ c yss) = c :> Internal.vXm r c xs yss

{-@ reflect <# @-}
{-@ (<#) :: xs:Vector R -> yss:{v:Matrix R | size xs == rows v} -> VectorN R {cols yss} @-}
(<#) :: Vector R -> Matrix R -> Vector R
(<#) = vXm

{-@ reflect mXm @-}
{-@ mXm :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R {rows xss} {cols yss} @-}
mXm :: Matrix R -> Matrix R -> Matrix R
mXm (M i j xss) (M _ k yss) = M i k (Internal.mXm i j k xss yss)

{-@ reflect <#> @-}
{-@ (<#>) :: xss:Matrix R -> yss:{v:Matrix R | cols xss == rows v} -> MatrixN R {rows xss} {cols yss} @-}
(<#>) :: Matrix R -> Matrix R -> Matrix R
(<#>) = mXm

{-@ reflect mXv @-}
{-@ mXv :: xss:Matrix R -> ys:VectorN R (cols xss) -> VectorN R {rows xss} @-}
mXv :: Matrix R -> Vector R -> Vector R
mXv xss ys = flatten (xss <#> asColumn ys)

{-@ reflect #> @-}
{-@ (#>) :: xss:Matrix R -> ys:VectorN R (cols xss) -> VectorN R {rows xss} @-}
(#>) :: Matrix R -> Vector R -> Vector R
(#>) = mXv
