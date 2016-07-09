module Main where

import Template

main :: IO ()
main = putStr (runProg sample)


sample :: String
sample = "pair x y f = f x y;\n fst p = p K;\n snd p = p K1;\n f x y = letrec\n a = pair x b;\n b = pair y a\n in\n fst (snd (snd (snd a)));\n main = f 3 4"
