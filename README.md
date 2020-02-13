# Lazuli

Lazuli is a library for leveraging the interactive theorem proving and SMT checking abilities of Liquid Haskell to verify properties of neural networks.
It currently supports feedforward neural networks using ReLU, sigmoid, and softmax activation functions.
Networks are written as follows:
```haskell
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
```
Properties of the model can then be checked using refinement types.
The type `TRUE` is the type `Bool` refined as `{v:Bool | v == True}`.
Let’s use it to check if the model correctly implements the AND gate:
```haskell
{-@ test1 :: TRUE @-}
test1 = runNetwork model (2 :> [1,1]) == (1 :> [1])
{-@ test2 :: TRUE @-}
test2 = runNetwork model (2 :> [0,1]) == (1 :> [0])
{-@ test3 :: TRUE @-}
test3 = runNetwork model (2 :> [1,0]) == (1 :> [0])
{-@ test4 :: TRUE @-}
test4 = runNetwork model (2 :> [0,0]) == (1 :> [0])
```
Yes! It correctly implements the AND gate!
However, is it robust?
What do we mean by robust?
That’s generally not an easy question.
For this AND gate, let’s take robustness to mean that if the input is within some epsilon of a 0.0 or 1.0, the gate still works:
```haskell
{-@ type Truthy = {v:R |  0.9 <= x && x <= 1.1} @-}
{-@ type Falsy  = {v:R | -0.1 <= x && x <= 0.1} @-}

{-@ test5 :: Truthy -> Truthy -> TRUE @-}
test5 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [1])
{-@ test6 :: Falsy  -> Truthy -> TRUE @-}
test6 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test7 :: Truthy -> Falsy  -> TRUE @-}
test7 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
{-@ test8 :: Falsy  -> Falsy  -> TRUE @-}
test8 x1 x2 = runNetwork model (2 :> [x1,x2]) == (1 :> [0])
```
The network we defined is robust around truthy and falsy inputs!

---

You may also be interested in Lazuli’s friend, [StarChild](https://github.com/wenkokke/starchild)!
