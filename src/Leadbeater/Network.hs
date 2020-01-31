{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Leadbeater.Network where

import Prelude hiding
  ( all
  , and
  , any
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

import           Leadbeater.LinearAlgebra
import qualified Leadbeater.LinearAlgebra.Internal
import           Leadbeater.Prelude (R, plus, minus, times, rdiv, max, min, lt, leq, geq)
import qualified Leadbeater.Prelude


-- * Activation functions

data Activation
   = ReLU
   | Sigmoid
   deriving (Eq)

{-@
data Activation
   = ReLU
   | Sigmoid
@-}

{-@ reflect relu @-}
{-@ relu :: R -> {x:R | x >= 0} @-}
relu :: R -> R
relu x = x `max` 0.0

{-@ reflect lexp @-}
{-@ lexp :: R -> R @-}
lexp :: R -> R
lexp x | x `lt` (0.0 `minus` 1.0) = 0.00001
       | x `geq` 1.0              = (5.898 `times` x) `minus` 3.898
       | otherwise                = x `plus` 1.0

-- linear approximation of the sigmoid function
{-@ reflect lsigmoid @-}
{-@ lsigmoid :: R -> R @-}
lsigmoid :: R -> R
lsigmoid x = (0.0 `max` ((0.25 `times` x) `plus` 0.5)) `min` 1.0

-- cannot be translated to SMTLIB2
{-@ norm :: xs:VectorNE Rpos -> VectorX R xs @-}
norm :: Vector R -> Vector R
norm xs = map (`rdiv` sumPos xs) xs

-- cannot be translated to SMTLIB2
{-@ assume exp :: Floating a => a -> {x:a | x > 0} @-}

-- cannot be translated to SMTLIB2
{-@ assume sigmoid :: x:R -> {v:R | v = lsigmoid x} @-}
sigmoid :: R -> R
sigmoid x = 1 `rdiv` (1 `plus` exp (0.0 `minus` x))

-- cannot be translated to SMTLIB2
{-@ softmax :: xs:VectorNE R -> VectorX R xs @-}
softmax :: Vector R -> Vector R
softmax xs = norm (map exp xs)

{-@ reflect runActivation @-}
{-@ runActivation :: Activation -> xs:Vector R -> VectorX R xs @-}
runActivation :: Activation -> Vector R -> Vector R
runActivation ReLU    xs = map relu xs
runActivation Sigmoid xs = map lsigmoid xs


-- * Layers

data Layer = Layer
   { bias       :: !R
   , weights    :: Matrix R
   , activation :: Activation
   }
   deriving (Eq)

{-@
data Layer = Layer
   { bias       :: R
   , weights    :: Matrix R
   , activation :: Activation
   }
@-}

{-@ reflect layerInputs @-}
{-@ layerInputs :: Layer -> Nat @-}
layerInputs :: Layer -> Int
layerInputs l = rows (weights l)

{-@ reflect layerOutputs @-}
{-@ layerOutputs :: Layer -> Nat @-}
layerOutputs :: Layer -> Int
layerOutputs l = cols (weights l)

{-@ type LayerN I O = {l:Layer | I = layerInputs l && O = layerOutputs l} @-}
{-@ type LayerX X   = LayerN (layerInputs X) (layerOutputs X) @-}

{-@ reflect runLayer @-}
{-@ runLayer :: l:Layer -> VectorN R (layerInputs l) -> VectorN R (layerOutputs l) @-}
runLayer :: Layer -> Vector R -> Vector R
runLayer l v = runActivation (activation l) (bias l +> (v <# weights l))


-- * Networks

data Network
   = NLast { nLast :: Layer }
   | NStep { nHead :: Layer, nTail :: Network }

{-@ reflect networkInputs @-}
{-@ networkInputs :: Network -> Nat @-}
networkInputs :: Network -> Int
networkInputs (NLast l)   = layerInputs l
networkInputs (NStep l _) = layerInputs l

{-@ reflect networkOutputs @-}
{-@ networkOutputs :: Network -> Nat @-}
networkOutputs :: Network -> Int
networkOutputs (NLast l)   = layerOutputs l
networkOutputs (NStep _ n) = networkOutputs n

{-@ type NetworkN I O = {n:Network | networkInputs n == I && networkOutputs n == O} @-}
{-@ type NetworkX L   = {n:Network | layerOutputs L == networkInputs n} @-}

{-@
data Network
   = NLast { nLast :: Layer }
   | NStep { nHead :: Layer, nTail :: NetworkX nHead }
@-}

{-@ reflect runNetwork @-}
{-@ runNetwork :: n:Network -> VectorN R (networkInputs n) -> VectorN R (networkOutputs n) @-}
runNetwork :: Network -> Vector R -> Vector R
runNetwork (NLast l)   xs = runLayer l xs
runNetwork (NStep l n) xs = runNetwork n (runLayer l xs)
