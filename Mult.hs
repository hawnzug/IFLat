module Mult where

type MultState = (Int, Int, Int, Int)

evalMult :: MultState -> [MultState]
evalMult state = if multFinal state
                    then [state]
                    else state : evalMult (stepMult state)

multFinal :: MultState -> Bool
multFinal (_, 0, 0, _) = True
multFinal _            = False

stepMult :: MultState -> MultState
stepMult (n, m, d, t) | d > 0 = (n, m, d-1, t+1)
stepMult (n, m, d, t) | d == 0 = (n, m-1, n, t)
stepMult _ = undefined
