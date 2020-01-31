{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Prelude hiding
  ( (&&)
  , drop
  , foldr
  , length
  , map
  , replicate
  , sum
  , take
  , zipWith
  )

import Control.Monad (unless)
import Leadbeater.Core.Layer
import Leadbeater.Core.Network
import Leadbeater.LinearAlgebra
import Leadbeater.Layers.FullyConnected
import Leadbeater.Prelude (geq, (&&))
import System.Exit

import qualified Leadbeater.LinearAlgebra.Internal
import qualified Leadbeater.Prelude

{-@ reflect example @-}
{-@ example :: NetworkN 2 1 @-}
example :: Network
example = NLast
          ( LayerFC
            FC { bias    = 0.184
               , weights = (1 >< 2)
                           [ 0.194 , 0.195
                           ]
               }
          )

{-@ reflect noneNegative @-}
{-@ noneNegative :: xs:Vector R -> Bool @-}
noneNegative :: Vector R -> Bool
noneNegative xs = foldr (&&) True (map (`geq` 0.0) xs)

{-@ test1 :: TRUE @-}
test1 = noneNegative (runNetwork example (2 |> [1.0, 1.0]))

{-@ test2 :: {n:Double | n >= 0.5} -> {m:Double | m >= 0.5} -> TRUE @-}
test2 n m = noneNegative (runNetwork example (2 |> [m, n]))

main :: IO ()
main =  unless test1 (exitWith (ExitFailure 1))
