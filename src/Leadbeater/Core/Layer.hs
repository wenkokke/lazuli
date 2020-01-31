{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Leadbeater.Core.Layer where

import           Leadbeater.LinearAlgebra
import qualified Leadbeater.LinearAlgebra.Internal
import           Leadbeater.Layers.FullyConnected (FullyConnected)
import qualified Leadbeater.Layers.FullyConnected as FC
import qualified Leadbeater.Prelude

data Layer
   = LayerFC FullyConnected

{-@
data Layer
   = LayerFC FullyConnected
@-}

{-@ reflect layerInputs @-}
{-@ layerInputs :: Layer -> Nat @-}
layerInputs :: Layer -> Int
layerInputs (LayerFC l) = FC.inputs l

{-@ reflect layerOutputs @-}
{-@ layerOutputs :: Layer -> Nat @-}
layerOutputs :: Layer -> Int
layerOutputs (LayerFC l) = FC.outputs l

{-@ reflect runForwards @-}
{-@ runForwards :: l:Layer -> VectorN R (layerInputs l) -> VectorN R (layerOutputs l) @-}
runForwards :: Layer -> Vector R -> Vector R
runForwards (LayerFC l) = FC.runForwards l
