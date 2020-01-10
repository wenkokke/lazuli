import Distribution.Simple
import LiquidHaskell.Cabal

data Choice = Simple | Post

choice :: Choice
choice = Post -- Simple

main :: IO ()
main = case choice of
         Simple -> liquidHaskellMain
         Post   -> liquidHaskellMainHooks
