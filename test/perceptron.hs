{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Control.Monad (unless)
import Numeric.LinearAlgebra
import Leadbeater.Layer.FullyConnected
import System.Exit

{-@ type TRUE = {v:Bool | v} @-}

{-@ reflect example @-}
example :: FullyConnected
example = FC { bias    = 0.184
             , weights = (1 >< 2)
                         [ 0.194 , 0.195
                         ]
             }

{-@ test1 :: TRUE @-}
test1 = predict example (2 |> [1.0, 1.0]) == 1 |> [True]

{-@ test2 :: {n:Double | n >= 0.5} -> {m:Double | m >= 0.5} -> TRUE @-}
test2 n m = predict example (2 |> [m, n]) == 1 |> [False]

main :: IO ()
main =  unless test1 (exitWith (ExitFailure 1))
