module Debug where

import Template
import Pretty


prog :: TiState
prog = compile $ parse "x = MkPair 6 7; t = x; main = fst t"

nsteps :: Int -> TiState -> TiState
nsteps 0 state = state 
nsteps n state = nsteps (n-1) (doAdmin (step state))

temp :: String -> Int -> IO ()
temp s n = putStr $ iDisplay $ showState $ nsteps n (compile (parse s))
