{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Control.Monad (when)
import Numeric.LinearAlgebra (Vector(..), vector, Matrix(..), matrix)
import Leadbeater.Layer.FullyConnected

{-@ type TRUE = {v:Bool | v} @-}
{-@ type Prob = {v:Double | 0.0 <= v && v <= 1.0} @-}

{-@ reflect example @-}
example :: FullyConnected
example = FC { bias    = 0.184
             , weights = matrix 1 2
                         [ 0.194 , 0.195
                         ]
             }

{-@ test1 :: TRUE @-}
test1 = toList (predict example (vector [1.0, 1.0])) == [True]

{-@ test2 :: {n:Prob | n >= 0.5} -> {m:Prob | m >= 0.5} -> TRUE @-}
test2 n m = toList (predict example (vector [m, n])) == [True]

{-@ test3 :: {n:Prob | n >= 0.5} -> {m:Prob | m >= 0.5} -> TRUE @-}
test3 n m = toList (predict example (vector [m, n])) == [False]

main :: IO ()
main = when (not test1) $
         error "test1 failed"
