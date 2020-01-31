{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.Layers.FullyConnected where

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

import Leadbeater.LinearAlgebra
import Leadbeater.Prelude (geq)

import qualified Leadbeater.Prelude
import qualified Leadbeater.LinearAlgebra.Internal

data FullyConnected = FC
  { bias    :: !R
  , weights :: Matrix R
  }
  deriving (Eq)

{-@
data FullyConnected = FC
  { bias    :: R
  , weights :: Matrix R
  }
@-}

{-@ reflect inputs @-}
{-@ inputs :: FullyConnected -> Nat @-}
inputs :: FullyConnected -> Int
inputs l = cols (weights l)

{-@ reflect outputs @-}
{-@ outputs :: FullyConnected -> Nat @-}
outputs :: FullyConnected -> Int
outputs l = rows (weights l)

{-@ type FullyConnectedN I O = {l:FullyConnected | I = inputs l && O = outputs l} @-}
{-@ type FullyConnectedX X   = FullyConnectedN (inputs X) (outputs X) @-}

{-@ reflect runForwards @-}
{-@ runForwards :: l:FullyConnected -> VectorN R (inputs l) -> VectorN R (outputs l) @-}
runForwards :: FullyConnected -> Vector R -> Vector R
runForwards l v = bias l +> (weights l #> v)
