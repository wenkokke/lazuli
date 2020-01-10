{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.Layer.FullyConnected where

import Prelude hiding (map, replicate, (<>))
import Numeric.LinearAlgebra

data FullyConnected = FC
  { bias    :: !Double
  , weights :: Matrix Double
  }
  deriving (Eq)

{-@
data FullyConnected = FC
  { bias    :: Double
  , weights :: Matrix Double
  }
@-}

{-@ type FullyConnectedN R C = {l:FullyConnected | rows (weights l) = R && cols (weights l) = C} @-}
{-@ type FullyConnectedX X   = FullyConnectedN {rows X} {cols X} @-}

{-@ reflect runForwards @-}
{-@ runForwards :: l:FullyConnected -> v:VectorN Double {cols (weights l)} -> VectorN Double {rows (weights l)} @-}
runForwards :: FullyConnected -> Vector Double -> Vector Double
runForwards (FC b w) v = b `add` (w #> v)

{-@ reflect predict @-}
{-@ predict :: l:FullyConnected -> v:VectorN Double {cols (weights l)} -> VectorN Bool {rows (weights l)} @-}
predict :: FullyConnected -> Vector Double -> Vector Bool
predict l v = threshold 0.0 (runForwards l v)
