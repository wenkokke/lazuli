{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Moons_2_ReLU_10_ReLU_10_Softmax_2 where

import           Lazuli.LinearAlgebra
import qualified Lazuli.LinearAlgebra.Internal
import           Lazuli.Network
import qualified Lazuli.Prelude

{-@ reflect layer0 @-}
{-@ layer0 :: LayerN 2 10 @-}
layer0 :: Layer
layer0 = Layer
  { weights    = (2 >< 10)
                 [ 10 |> [-0.69860595, 0.30150732, 0.08476701, 0.63485038, 0.12577459, -0.80605918, 0.41525468, 0.70885551, 0.58857864, 0.27796772]
                 , 10 |> [0.03890725, -0.40764850, -0.57726216, 0.34223819, 0.27123612, 0.55684626, 0.07101971, -0.13747413, -0.84362292, -0.25267375]
                 ]
  , biases     = 10 :> [0.13968933, -0.13591185, 0.26694423, 0.19919132, 0.14054692, 0.05770387, 0.02562346, 0.16781409, 0.13742369, -0.11328863]
  , activation = ReLU
  }

{-@ reflect layer1 @-}
{-@ layer1 :: LayerN 10 10 @-}
layer1 :: Layer
layer1 = Layer
  { weights    = (10 >< 10)
                 [ 10 |> [0.07930053, -0.00979054, 0.55999166, -0.02033671, 0.57894099, 0.38427216, -0.35002741, 0.70861530, 0.13603407, 0.34685719]
                 , 10 |> [0.11626597, -0.53731412, 0.22795877, 0.23164463, -0.01791917, -0.07275171, -0.32659480, -0.30212587, 0.41620210, 0.15143961]
                 , 10 |> [0.45076826, -0.54921031, -0.47037134, 0.30038369, 0.22143203, 0.46453986, -0.48867413, -0.25320530, 0.09735141, 0.09264973]
                 , 10 |> [-0.10899631, 0.03249760, -0.45776603, -0.40047711, 0.46010566, 0.50116748, 0.48178026, -0.14264321, 0.12607713, 0.08339514]
                 , 10 |> [0.06625389, -0.57507491, 0.27933088, 0.02980086, 0.17073223, -0.30436695, 0.69272161, -0.23753758, 0.17939571, -0.03564233]
                 , 10 |> [-0.15930709, -0.10516098, 0.34883106, 0.24899507, 0.38557601, -0.38330331, 0.62009817, 0.31667212, 0.37227914, -0.26375347]
                 , 10 |> [0.05323938, -0.28048891, 0.29833162, -0.25289834, -0.45241082, 0.13698040, -0.06814619, 0.06116130, -0.39508340, 0.15139596]
                 , 10 |> [0.20755632, 0.42114580, -0.24317990, 0.31066561, 0.42062533, 0.40454975, 0.45752111, -0.48240444, -0.11078911, -0.22247115]
                 , 10 |> [0.54915196, 0.06184734, 0.14089715, -0.53640902, -0.48919371, 0.64518404, -0.54104251, -0.54023451, -0.16242626, 0.70138901]
                 , 10 |> [-0.22131109, 0.11974425, 0.11638532, -0.51621020, 0.24396804, 0.18231459, -0.21687774, 0.02013057, -0.62596464, -0.23260085]
                 ]
  , biases     = 10 :> [0.10004407, -0.05645256, 0.04459446, -0.11032539, 0.01563998, 0.11248454, 0.12729751, 0.06255097, -0.03195711, -0.00021379]
  , activation = ReLU
  }

{-@ reflect layer2 @-}
{-@ layer2 :: LayerN 10 2 @-}
layer2 :: Layer
layer2 = Layer
  { weights    = (10 >< 2)
                 [ 2 |> [-0.16509019, 0.57469958]
                 , 2 |> [-0.09795898, -0.34377596]
                 , 2 |> [-0.00453515, -0.88816863]
                 , 2 |> [-0.09279941, 0.01288275]
                 , 2 |> [0.73177314, 0.37891957]
                 , 2 |> [-0.11767633, 0.66085231]
                 , 2 |> [0.92822647, -0.55045778]
                 , 2 |> [0.88676172, -0.13964896]
                 , 2 |> [0.08417362, -0.58222663]
                 , 2 |> [-0.17097764, 0.86680174]
                 ]
  , biases     = 2 :> [0.02339423, -0.02339423]
  , activation = Softmax
  }

{-@ reflect model @-}
{-@ model :: NetworkN 2 2 @-}
model :: Network
model = NStep layer0 (NStep layer1 (NLast layer2))