{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lazuli.Network where

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

import           Lazuli.LinearAlgebra
import qualified Lazuli.LinearAlgebra.Internal
import           Lazuli.Prelude (R, plus, minus, times, rdiv, max, min, leq, geq)
import qualified Lazuli.Prelude


-- * Activation functions

data Activation
   = ReLU
   | Sigmoid
   | Softmax

{-@
data Activation
   = ReLU
   | Sigmoid
   | Softmax
@-}

{-@ reflect relu @-}
{-@ relu :: R -> {x:R | x >= 0} @-}
relu :: R -> R
relu x = x `max` 0.0

-- cannot be translated to SMTLIB2
{-@ assume exp :: Floating a => a -> {x:a | x > 0} @-}

{-@ reflect lexp @-}
{-@ lexp :: R -> Rpos @-}
lexp :: R -> R
lexp x | x `leq` (-1.0) = 0.00001
       | x `geq`   1.0  = 5.898 * x - 3.898
       | otherwise      = x + 1.0

{-@ reflect norm @-}
{-@ norm :: bar:VectorNE Rpos -> VectorX R bar @-}
norm :: Vector R -> Vector R
norm foo = let s = sumPos foo in map (`rdiv` s) foo

-- cannot be translated to SMTLIB2
{-@ assume sigmoid :: x:R -> {v:R | v == lsigmoid x} @-}
sigmoid :: R -> R
sigmoid x = 1 / (1 + exp (-x))

-- linear approximation of the sigmoid function
{-@ reflect lsigmoid @-}
{-@ lsigmoid :: R -> R @-}
lsigmoid :: R -> R
lsigmoid x = min (max 0.0 (0.25 * x + 0.5)) 1.0

-- cannot be translated to SMTLIB2
{-@ softmax :: xs:VectorNE R -> VectorX R xs @-}
softmax :: Vector R -> Vector R
softmax xs = norm (map exp xs)

-- linear approximation of the softmax function
{-@ reflect lsoftmax @-}
{-@ lsoftmax :: xs:VectorNE R -> VectorX R xs @-}
lsoftmax :: Vector R -> Vector R
lsoftmax xs = norm (map lexp xs)

{-@ reflect runActivation @-}
{-@ runActivation :: Activation -> xs:VectorNE R -> VectorX R xs @-}
runActivation :: Activation -> Vector R -> Vector R
runActivation ReLU    xs = map relu xs
runActivation Sigmoid xs = map lsigmoid xs
runActivation Softmax xs = lsoftmax xs


-- * Layers

data Layer = Layer
   { weights    :: Matrix R
   , bias       :: Vector R
   , activation :: Activation
   }

{-@
data Layer = Layer
   { weights    :: MatrixNE R
   , bias       :: VectorN R (cols weights)
   , activation :: Activation
   }
@-}

{-@ reflect layerInputs @-}
{-@ layerInputs :: Layer -> Pos @-}
layerInputs :: Layer -> Int
layerInputs l = rows (weights l)

{-@ reflect layerOutputs @-}
{-@ layerOutputs :: Layer -> Pos @-}
layerOutputs :: Layer -> Int
layerOutputs l = cols (weights l)

{-@ type LayerN I O = {v:Layer | layerInputs v == I && layerOutputs v == O} @-}
{-@ type LayerX X   = LayerN (layerInputs X) (layerOutputs X) @-}

{-@ reflect runLayer @-}
{-@ runLayer :: l:Layer -> VectorN R (layerInputs l) -> VectorN R (layerOutputs l) @-}
runLayer :: Layer -> Vector R -> Vector R
runLayer l v = runActivation (activation l) (bias l <+> (v <# weights l))


-- * Networks

data Network
   = NLast { nLast :: Layer }
   | NStep { nHead :: Layer, nTail :: Network }

{-@ reflect networkInputs @-}
{-@ networkInputs :: Network -> Pos @-}
networkInputs :: Network -> Int
networkInputs (NLast l)   = layerInputs l
networkInputs (NStep l _) = layerInputs l

{-@ reflect networkOutputs @-}
{-@ networkOutputs :: Network -> Pos @-}
networkOutputs :: Network -> Int
networkOutputs (NLast l)   = layerOutputs l
networkOutputs (NStep _ n) = networkOutputs n

{-@ type NetworkN I O = {v:Network | networkInputs v == I && networkOutputs v == O} @-}
{-@ type NetworkX L   = {v:Network | layerOutputs L == networkInputs v} @-}

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
