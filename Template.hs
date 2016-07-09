module Template where

import Lang
import Utils
import Parser
import Pretty
import Prld

runProg :: String -> String
runProg = showResults . eval . compile . parse

parse :: String -> CoreProgram
parse s = fst $ head $ runParser pProgram (clex 0 s)

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)
type TiStack = [Addr]

data TiDump = DummyTiDump

initialTiDump :: TiDump
initialTiDump = DummyTiDump

type TiHeap = Heap Node

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
          | NInd Addr

type TiGlobals = ASSOC Name Addr

tiStatInitial :: TiStats
tiStatIncSteps :: TiStats -> TiStats
tiStatGetSteps :: TiStats -> Int

type TiStats = Int
tiStatInitial = 0
tiStatIncSteps = (+1)
tiStatGetSteps = id

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, sc_defs, stats) = (stack, dump, heap, sc_defs, f stats)

compile :: CoreProgram -> TiState
compile program = (initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)
    where sc_defs = program ++ preludeDefs ++ extraPreludeDefs
          (initial_heap, globals) = buildInitialHeap sc_defs
          initial_stack = [address_of_main]
          address_of_main = aLookup globals "main" (error "main is not defined")

extraPreludeDefs :: CoreProgram
extraPreludeDefs = []

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap = mapAccuml allocateSc hInitial

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NSupercomb name args body)

eval :: TiState -> [TiState]
eval state = state : rest_states
    where rest_states | tiFinal state = []
                      | otherwise = eval next_state
          next_state = doAdmin (step state)

doAdmin :: TiState -> TiState
doAdmin = applyToStats tiStatIncSteps

tiFinal :: TiState -> Bool
tiFinal ([],_,_,_,_) = error "Empty stack!"
tiFinal ([sole_addr],_,heap,_,_) = isDataNode (hLookup heap sole_addr)
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode _        = False

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
    where (stack,_,heap,_,_) = state
          dispatch (NNum n) = numStep state n
          dispatch (NAp a1 a2) = apStep state a1 a2
          dispatch (NSupercomb sc args body) = scStep state sc args body
          dispatch (NInd addr) = indStep state addr

numStep :: TiState -> Int -> TiState
numStep _ _ = error "Number applied as a function!"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack,dump,heap,globals,stats) a1 _ = (a1:stack,dump,heap,globals,stats)

indStep :: TiState -> Addr -> TiState
indStep ([],_,_,_,_) _ = error "indStep: cannot reach here"
indStep (_:stack,dump,heap,globals,stats) a = (a:stack,dump,heap,globals,stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack,dump,heap,globals,stats) name arg_names body =
    if length arg_names + 1 > length stack
       then error (name ++ " is applied to too few arguments!")
       else (new_stack,dump,update_heap,globals,stats)
        where new_stack = result_addr : drop (length arg_names + 1) stack
              (new_heap, result_addr) = instantiate body heap env
              update_heap = hUpdate new_heap (head (drop (length arg_names) stack)) (NInd result_addr)
              env = arg_bindings ++ globals
              arg_bindings = zip arg_names (getargs heap stack)

getargs :: TiHeap -> TiStack -> [Addr]
getargs _ [] = error "getargs: empty stack"
getargs heap (_:stack) = map get_arg stack
    where get_arg addr = arg where (NAp _ arg) = hLookup heap addr

instantiate :: CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)

instantiate (ENum n) heap _ = hAlloc heap (NNum n)

instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
    where (heap1, a1) = instantiate e1 heap env
          (heap2, a2) = instantiate e2 heap1 env

instantiate (EVar v) heap env = (heap, aLookup env v (error ("Undefined name " ++ show v)))

instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env

instantiate (ELet isrec defs body) heap env = instantiateLet isrec defs body heap env
instantiate _ _ _ = undefined

instantiateConstr :: a -> b -> c -> d -> e
instantiateConstr _ _ _ _ = error "Cannot instantiate constructors yet"
instantiateLet :: IsRec -> [(Name, CoreExpr)] -> CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiateLet _ defs body heap env = instantiate body new_heap new_env
    where new_env = nenv ++ env
          (new_heap, nenv) = instantiateDefs defs heap new_env

instantiateDefs :: [(Name, CoreExpr)] -> TiHeap -> ASSOC Name Addr -> (TiHeap, ASSOC Name Addr)
instantiateDefs defs heap env = mapAccuml instantiateDef heap defs
    where instantiateDef h def = (fheap, (fst def, addr))
            where (fheap,addr) = instantiate (snd def) h env


showResults :: [TiState] -> String
showResults states = iDisplay (iConcat [ iLayn (map showState states), showStats (last states)])

showState :: TiState -> Iseq
showState (stack, _, heap, _, _) = iConcat [ showStack heap stack, iNewline ]

showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack = iConcat [ iStr "Stack ",
                                 iIndent (iInterleave iNewline (map show_stack_item stack)), iNewline,
                                 iStr "Heap  ",
                                 iIndent (iInterleave iNewline (map show_stack_item (hAddresses heap))) ]
                                     where show_stack_item addr = iConcat [ showFWAddr addr, iStr ": ", showStkNode heap (hLookup heap addr) ]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp fun_addr arg_addr) = iConcat [ iStr "NAp ", showFWAddr fun_addr,
                                                     iStr " ", showFWAddr arg_addr, iStr " (",
                                                     showNode (hLookup heap arg_addr), iStr ")" ]

showStkNode _ node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", showAddr a1,
                                 iStr " ", showAddr a2 ]

showNode (NSupercomb name _ _) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = iStr "NNum " `iAppend` iNum n
showNode (NInd addr) = iStr "NInd " `iAppend` showAddr addr

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq
showFWAddr addr = iStr (replicate (4 - length str) ' ' ++ str)
    where str = show addr

showStats :: TiState -> Iseq
showStats (_, _, _, _, stats) = iConcat [ iNewline, iNewline, iStr "Total number of steps = ", iNum (tiStatGetSteps stats), iNewline ]
