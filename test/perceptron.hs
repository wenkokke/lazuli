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
import           Leadbeater.Prelude (R,geq)
import qualified Leadbeater.Prelude
import           System.Exit


{-@ reflect example @-}
{-@ example :: NetworkN 2 1 @-}
example :: Network
example = NLast
          (
            Layer { bias       = 0.184
                  , weights    = (1 >< 2)
                                 [ 0.194 , 0.195
                                 ]
                  , activation = Softmax
                  }
          )

{-@ test1 :: TRUE @-}
test1 = all (`geq` 0.0) (runNetwork example (2 |> [1.0, 1.0]))

{-@ test2 :: {n:Double | n >= 0.5} -> {m:Double | m >= 0.5} -> TRUE @-}
test2 n m = all (`geq` 0.0) (runNetwork example (2 |> [m, n]))

main :: IO ()
main =  unless test1 (exitWith (ExitFailure 1))
