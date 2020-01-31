{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Leadbeater.Core.Network where

import           Leadbeater.Core.Layer
import           Leadbeater.LinearAlgebra
import qualified Leadbeater.LinearAlgebra.Internal
import           Leadbeater.Layers.FullyConnected (FullyConnected)
import qualified Leadbeater.Layers.FullyConnected as FC
import qualified Leadbeater.Prelude


data Network
   = NLast { nLast :: Layer}
   | NCons { nHead :: Layer, nTail :: Network }

{-@ reflect inputs @-}
{-@ inputs :: Network -> Nat @-}
inputs :: Network -> Int
inputs (NLast l)   = layerInputs l
inputs (NCons l _) = layerInputs l

{-@ reflect outputs @-}
{-@ outputs :: Network -> Nat @-}
outputs :: Network -> Int
outputs (NLast l)   = layerOutputs l
outputs (NCons _ n) = outputs n

{-@ type NetworkN I O = {n:Network | inputs n = I && outputs n = O} @-}
{-@ type NetworkX L   = {n:Network | layerOutputs L = inputs n} @-}

{-@
data Network
   = NLast { nLast :: Layer }
   | NCons { nHead :: Layer, nTail :: NetworkX nHead }
@-}

{-@ reflect runNetwork @-}
{-@ runNetwork :: n:Network -> VectorN R (inputs n) -> VectorN R (outputs n) @-}
runNetwork :: Network -> Vector R -> Vector R
runNetwork (NLast l)   xs = runForwards l xs
runNetwork (NCons l n) xs = runNetwork n (runForwards l xs)
