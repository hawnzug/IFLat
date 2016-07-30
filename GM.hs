module GM where

import Lang
import Utils
import Parser
import Pretty
import Prld

runProg :: String -> String
runProg = showResults . eval . compile . parse

parse :: String -> CoreProgram
parse s = fst $ head $ runParser pProgram (clex 0 s)

type GmState = (GmCode,GmStack,GmHeap,GmGlobals,GmStats)

type GmCode = [Instruction]
getCode :: GmState -> GmCode
getCode (i,_,_,_,_) = i
putCode :: GmCode -> GmState -> GmState
putCode i (_,stack,heap,globals,stats) = (i,stack,heap,globals,stats)

data Instruction = Unwind
                 | Pushglobal Name
                 | Pushint Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
                 deriving (Eq, Show)

type GmStack = [Addr]
getStack :: GmState -> GmStack
getStack (_,i,_,_,_) = i
putStack :: GmStack -> GmState -> GmState
putStack i (code,_,heap,globals,stats) = (code,i,heap,globals,stats)
applyToStack :: (GmStack -> GmStack) -> GmState -> GmState
applyToStack f (code,stack,heap,globals,stats) = (code,f stack,heap,globals,stats)

type GmHeap = Heap Node
getHeap :: GmState -> GmHeap
getHeap (_,_,i,_,_) = i
putHeap :: GmHeap -> GmState -> GmState
putHeap i (code,stack,_,globals,stats) = (code,stack,i,globals,stats)

data Node = NNum Int
          | NAp Addr Addr
          | NGlobal Int GmCode
          | NInd Addr

instance Eq Node where
    NNum a == NNum b = a == b
    _ == _ = False

type GmGlobals = ASSOC Name Addr
getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,i,_) = i

type GmStats = Int
statInitial :: GmStats
statInitial = 0
statIncSteps :: GmStats -> GmStats
statIncSteps = (+1)
statGetSteps :: GmStats -> Int
statGetSteps = id
getStats :: GmState -> GmStats
getStats (_,_,_,_,i) = i
putStats :: GmStats -> GmState -> GmState
putStats i (code,stack,heap,globals,_) = (code,stack,heap,globals,i)
applyToStats :: (GmStats -> GmStats) -> GmState -> GmState
applyToStats f (code,stack,heap,globals,stats) = (code,stack,heap,globals,f stats)

eval :: GmState -> [GmState]
eval state = state : rest_states
    where rest_states | gmFinal state = []
                      | otherwise = eval next_state
          next_state = doAdmin (step state)

doAdmin :: GmState -> GmState
doAdmin = applyToStats statIncSteps

gmFinal :: GmState -> Bool
gmFinal = null . getCode

step :: GmState -> GmState
step state = dispatch i (putCode is state)
    where (i:is) = getCode state

dispatch :: Instruction -> GmState -> GmState
dispatch (Pushglobal f) = pushglobal f
dispatch (Pushint n) = pushint n
dispatch Mkap = mkap
dispatch (Push n) = push n
dispatch (Update n) = update n
dispatch (Pop n) = pop n
dispatch Unwind = unwind

pushglobal :: Name -> GmState -> GmState
pushglobal f state = applyToStack (a:) state
    where a = aLookup (getGlobals state) f (error ("Undeclared global " ++ f))

pushint :: Int -> GmState -> GmState
pushint n state = putHeap heap' (applyToStack (a:) state)
    where (heap',a) = hAlloc (getHeap state) (NNum n)

mkap :: GmState -> GmState
mkap state = putHeap heap' (putStack (a:as) state)
    where (heap',a) = hAlloc (getHeap state) (NAp a1 a2)
          (a1:a2:as) = getStack state

push :: Int -> GmState -> GmState
push n state = putStack (a:as) state
    where as = getStack state
          a = getArg (hLookup (getHeap state) (as !! (n+1)))

getArg :: Node -> Addr
getArg (NAp _ a2) = a2
getArg _ = error "getArg: need NAp node"

slide :: Int -> GmState -> GmState
slide n state = putStack (a : drop n as) state
    where (a:as) = getStack state

update :: Int -> GmState -> GmState
update n state = applyToStack tail (putHeap heap' state)
    where an = stack!!(n+1)
          a = head stack
          stack = getStack state
          heap' = hUpdate (getHeap state) an (NInd a)

pop :: Int -> GmState -> GmState
pop n = applyToStack (drop n)

unwind :: GmState -> GmState
unwind state = newState (hLookup heap a)
    where (a:as) = getStack state
          heap = getHeap state
          newState (NNum _) = state
          newState (NInd i) = putCode [Unwind] (putStack (i:as) state)
          newState (NAp a1 _) = putCode [Unwind] (putStack (a1:a:as) state)
          newState (NGlobal n c) | length as < n = error "Unwinding with too few arguments"
                                 | otherwise = putCode c state

compile :: CoreProgram -> GmState
compile program = (initialCode,[],heap,globals,statInitial)
    where (heap,globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program = mapAccuml allocateSc hInitial compiled
    where compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives

type GmCompiledSC = (Name, Int, GmCode)

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name,nargs,instns) = (heap',(name,addr))
    where (heap',addr) = hAlloc heap (NGlobal nargs instns)

initialCode :: GmCode
initialCode = [Pushglobal "main", Unwind]

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name,env,body) = (name,length env,compileR body (zip env [0..]))

type GmCompiler = CoreExpr -> GmEnvironment -> GmCode
type GmEnvironment = ASSOC Name Int

compileR :: GmCompiler
compileR e env = compileC e env ++ [Update d, Pop d, Unwind]
    where d = length env

compileC :: GmCompiler
compileC (EVar v) env
  | v `elem` aDomain env = [Push n]
  | otherwise = [Pushglobal v]
  where n = aLookup env v (error "Can't happen")
compileC (ENum n) _ = [Pushint n]
compileC (EAp e1 e2) env = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [Mkap]
compileC _ _ = error "Todo: compileC"

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v,m+n) | (v,m) <- env]

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = []

showResults :: [GmState] -> String
showResults states = iDisplay (iConcat [iStr "Supercombinator definitions", iNewline,
                                        iInterleave iNewline (map (showSC s) (getGlobals s)),
                                        iNewline, iNewline, iStr "State transitions", iNewline, iNewline,
                                        iLayn (map showState states),
                                        iNewline, iNewline,
                                        showStats (last states), iNewline])
                                            where (s:_) = states

showSC :: GmState -> (Name, Addr) -> Iseq
showSC s (name,addr) = iConcat [iStr  "Code for ", iStr name, iNewline,
                                showInstructions code, iNewline, iNewline]
                                    where (NGlobal _ code) = hLookup (getHeap s) addr

showInstructions :: GmCode -> Iseq
showInstructions is = iConcat [iStr " Code:{",
                               iIndent (iInterleave iNewline (map showInstruction is)),
                               iStr "}", iNewline]

showInstruction :: Instruction -> Iseq
showInstruction i = iStr (show i)

showState :: GmState -> Iseq
showState s = iConcat [showStack s, iNewline,
                       showInstructions (getCode s), iNewline]

showStack :: GmState -> Iseq
showStack s = iConcat [iStr " Stack:[",
                       iIndent (iInterleave iNewline (map (showStackItem s) (reverse (getStack s)))),
                       iStr "]"]

showStackItem :: GmState -> Addr -> Iseq
showStackItem s a = iConcat [iStr (showaddr a), iStr ": ",
                             showNode s a (hLookup (getHeap s) a)]

showNode :: GmState -> Addr -> Node -> Iseq
showNode _ _ (NNum n) = iNum n
showNode s a (NGlobal _ _) = iConcat [iStr "Global ", iStr v]
    where v = head [n | (n,b) <- getGlobals s, a == b]
showNode _ _ (NAp a1 a2) = iConcat [iStr "Ap ", iStr (showaddr a1),
                                    iStr " ", iStr (showaddr a2)]
showNode _ _ (NInd addr) = iConcat [iStr "Indirect ", iStr (showaddr addr)]

showStats :: GmState -> Iseq
showStats s = iConcat [iStr "Steps taken = ", iNum (statGetSteps (getStats s))]
