{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Leadbeater.Layer.FullyConnected where

import Prelude hiding (map, replicate, (<>))
import Numeric.LinearAlgebra
import Numeric.LinearAlgebra.Internal (geq)
import qualified Numeric.LinearAlgebra.Internal as Internal

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
{-@ runForwards :: l:FullyConnected -> VectorN Double (inputs l) -> VectorN Double (outputs l) @-}
runForwards :: FullyConnected -> Vector Double -> Vector Double
runForwards l v = bias l +> (weights l #> v)

{-@ reflect predict @-}
{-@ predict :: l:FullyConnected -> v:VectorN Double (inputs l) -> VectorN Bool (outputs l) @-}
predict :: FullyConnected -> Vector Double -> Vector Bool
predict l v = map (geq 0.0) (runForwards l v)
