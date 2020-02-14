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
import           Lazuli.Network
import           Lazuli.LinearAlgebra
import qualified Lazuli.LinearAlgebra.Internal
import           Lazuli.Prelude (List, R, geq)
import qualified Lazuli.Prelude
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
               , biases     = 1 :> [-25993.1]
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

{-@ type Truthy = {v:R |  0.9 <= v && v <= 1.1} @-}
{-@ type Falsy  = {v:R | -0.1 <= v && v <= 0.1} @-}

{-@ test5 :: Truthy -> Truthy -> TRUE @-}
test5 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [1])
{-@ test6 :: Falsy  -> Truthy -> TRUE @-}
test6 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test7 :: Truthy -> Falsy  -> TRUE @-}
test7 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test8 :: Falsy  -> Falsy  -> TRUE @-}
test8 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
