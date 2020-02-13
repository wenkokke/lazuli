{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Prelude hiding
  ( all
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

import           Control.Monad (unless)
import           Leadbeater.Network
import           Leadbeater.LinearAlgebra
import qualified Leadbeater.LinearAlgebra.Internal
import           Leadbeater.Prelude (List, R, geq)
import qualified Leadbeater.Prelude
import           System.Exit


main :: IO ()
main | test1 && test2 && test3 && test4 = return ()
     | otherwise = exitFailure

{-@ reflect layer1 @-}
{-@ layer1 :: LayerN 2 1 @-}
layer1 = Layer { weights    = (2 >< 1)
                              [ 1 |> [17561.5]
                              , 1 |> [17561.5]
                              ]
               , bias       = 1 :> [-25993.1]
               , activation = Sigmoid
               }

{-@ reflect model @-}
{-@ model :: NetworkN 2 1 @-}
model :: Network
model = NLast layer1

{-@ test1 :: TRUE @-}
test1 = runNetwork model (2 :> [1,1]) == (1 :> [1])
{-@ test2 :: TRUE @-}
test2 = runNetwork model (2 :> [0,1]) == (1 :> [0])
{-@ test3 :: TRUE @-}
test3 = runNetwork model (2 :> [1,0]) == (1 :> [0])
{-@ test4 :: TRUE @-}
test4 = runNetwork model (2 :> [0,0]) == (1 :> [0])

{-@ reflect epsilon @-}
epsilon :: R
epsilon = 0.2

{-@ reflect btwn @-}
btwn :: R -> R -> R -> Bool
btwn l x u = l <= x && x <= u

{-@ reflect truthy @-}
truthy :: R -> Bool
truthy x = btwn 0.9 x 1.1

{-@ reflect falsy @-}
falsy :: R -> Bool
falsy x = btwn (-0.1) x 0.1

{-@ test5 :: {v:R | truthy v} -> {v:R | truthy v} -> TRUE @-}
test5 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [1])
{-@ test6 :: {v:R | falsy  v} -> {v:R | truthy v} -> TRUE @-}
test6 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test7 :: {v:R | truthy v} -> {v:R | falsy  v} -> TRUE @-}
test7 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test8 :: {v:R | falsy  v} -> {v:R | falsy  v} -> TRUE @-}
test8 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
