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

type TiDump = [TiStack]

initialTiDump :: TiDump
initialTiDump = []

type TiHeap = Heap Node

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
          | NInd Addr
          | NPrim Name Primitive
          | NData Int [Addr]

data Primitive = Neg
               | Add | Sub | Mul | Div
               | PrimConstr Int Int
               | If
               | Greater | GreaterEq | Less | LessEq | Equal | NotEq
               | PrimCasePair

type TiGlobals = ASSOC Name Addr
type TiStats = (TiSteps,TiScReducs,TiPrReducs,TiMaxStack)
type TiSteps = Int
type TiScReducs = Int
type TiPrReducs = Int
type TiMaxStack = Int

tiStatInitial :: TiStats
tiStatInitial = (0,0,0,1)

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps (a,b,c,d) = (a+1,b,c,d)
tiStatGetSteps :: TiStats -> Int
tiStatGetSteps (a,_,_,_) = a

tiStatIncScReducs :: TiStats -> TiStats
tiStatIncScReducs (a,b,c,d) = (a,b+1,c,d)
tiStatGetScReducs :: TiStats -> Int
tiStatGetScReducs (_,b,_,_) = b

tiStatIncPrReducs :: TiStats -> TiStats
tiStatIncPrReducs (a,b,c,d) = (a,b,c+1,d)
tiStatGetPrReducs :: TiStats -> Int
tiStatGetPrReducs (_,_,c,_) = c

tiStatIncMaxStack :: TiStats -> TiStats
tiStatIncMaxStack (a,b,c,d) = (a,b,c,d+1)
tiStatGetMaxStack :: TiStats -> Int
tiStatGetMaxStack (_,_,_,d) = d

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, sc_defs, stats) = (stack, dump, heap, sc_defs, f stats)

compile :: CoreProgram -> TiState
compile program = (initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)
    where sc_defs = program ++ preludeDefs ++ extraPreludeDefs
          (initial_heap, globals) = buildInitialHeap sc_defs
          initial_stack = [address_of_main]
          address_of_main = aLookup globals "main" (error "main is not defined")

extraPreludeDefs :: CoreProgram
extraPreludeDefs = [("False", [], EConstr 1 0)
                   ,("True", [], EConstr 2 0)
                   ,("and", ["x","y"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "y")) (EVar "False"))
                   ,("or", ["x","y"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "True")) (EVar "y"))
                   ,("not", ["x"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "False")) (EVar "True"))
                   ,("MkPair", [], EConstr 3 2)
                   ,("fst", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K"))
                   ,("snd", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K1"))
                   ]

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap sc_defs = (heap2, sc_addrs ++ prim_addrs)
    where (heap1, sc_addrs) = mapAccuml allocateSc hInitial sc_defs
          (heap2, prim_addrs) = mapAccuml allocatePrim heap1 primitives

primitives :: ASSOC Name Primitive
primitives = [("negate", Neg)
             ,("+", Add)
             ,("-", Sub)
             ,("*", Mul)
             ,("/", Div)
             ,("if", If)
             ,(">", Greater)
             ,(">=", GreaterEq)
             ,("<", Less)
             ,("<=", LessEq)
             ,("==", Equal)
             ,("!=", NotEq)
             ,("casePair", PrimCasePair)
             ]

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NPrim name prim)

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
tiFinal ([sole_addr],[],heap,_,_) = isDataNode (hLookup heap sole_addr)
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode (NData _ _) = True
isDataNode _        = False

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
    where (stack,_,heap,_,_) = state
          dispatch (NNum _) = numStep state
          dispatch (NAp a1 a2) = apStep state a1 a2
          dispatch (NSupercomb sc args body) = scStep state sc args body
          dispatch (NInd addr) = indStep state addr
          dispatch (NPrim _ prim) = primStep state prim
          dispatch (NData _ _) = dataStep state

numStep :: TiState -> TiState
numStep (_,old_stack:dump,heap,globals,stats) = (old_stack,dump,heap,globals,stats)
numStep _ = error "Number applied as a function!"

dataStep :: TiState -> TiState
dataStep (_,old_stack:dump,heap,globals,stats) = (old_stack,dump,heap,globals,stats)
dataStep _ = error "Data applied as a function!"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack,dump,heap,globals,stats) a1 a2 = case hLookup heap a2 of
                                                 NInd a3 -> let new_heap = hUpdate heap (head stack) (NAp a1 a3)
                                                                    in (stack,dump,new_heap,globals,new_stats)
                                                 _ -> (a1:stack,dump,heap,globals,new_stats)
        where new_stats = if length stack == tiStatGetMaxStack stats then tiStatIncMaxStack stats else stats

indStep :: TiState -> Addr -> TiState
indStep ([],_,_,_,_) _ = error "indStep: cannot reach here"
indStep (_:stack,dump,heap,globals,stats) a = (a:stack,dump,heap,globals,stats)

primStep :: TiState -> Primitive -> TiState
primStep state Neg = primNeg state
primStep state Add = primArith state (+)
primStep state Sub = primArith state (-)
primStep state Mul = primArith state (*)
primStep state Div = primArith state div
primStep state (PrimConstr tag arity) = primConstr state tag arity
primStep state If = primIf state
primStep state Greater = primComp state (>)
primStep state GreaterEq = primComp state (>=)
primStep state Less = primComp state (<)
primStep state LessEq = primComp state (<=)
primStep state Equal = primComp state (==)
primStep state NotEq = primComp state (/=)
primStep state PrimCasePair = primCasePair state

primIf :: TiState -> TiState
primIf (stack,_,_,_,_) | length stack < 4 = error "if: arguments error"
primIf (stack,dump,heap,globals,stats)
  | isDataNode cond = let new_heap = hUpdate heap top_addr node
                          node = case cond of
                                   NData 2 [] -> node1
                                   NData 1 [] -> node2
                                   _ -> error "if: condition needs to be a bool"
                        in (top_addr:old,dump,new_heap,globals,stats)
  | otherwise = ([cond_addr],stack:dump,heap,globals,stats)
  where node1 = hLookup heap arg1_addr
        node2 = hLookup heap arg2_addr
        cond = hLookup heap cond_addr
        cond_addr:arg1_addr:arg2_addr:_ = getargs heap stack
        _:_:_:top_addr:old = stack

primCasePair :: TiState -> TiState
primCasePair (stack,_,_,_,_) | length stack < 3 = error "if: arguments error"
primCasePair (stack,dump,heap,globals,stats)
  | isDataNode pair = case pair of
                        NData 3 [a,b] -> let (heap1,addr1) = hAlloc heap (NAp func_addr a)
                                             heap2 = hUpdate heap1 top_addr (NAp addr1 b)
                                          in (addr1:top_addr:old,dump,heap2,globals,stats)
                        _             -> error "casePair: need a pair"
  | otherwise = ([pair_addr],[top_addr]:dump,heap,globals,stats)
  where --func = hLookup heap func_addr
        pair = hLookup heap pair_addr
        pair_addr:func_addr:_ = getargs heap stack
        _:_:top_addr:old = stack

primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic (stack,_,_,_,_) _ | length stack /= 3 = error "arith arguments error"
primDyadic (stack,dump,heap,globals,stats) nodeOp
  | isDataNode node1 && isDataNode node2 = let new_heap = hUpdate heap ap2_addr (nodeOp node1 node2)
                                            in ([ap2_addr],dump,new_heap,globals,stats)
  | not (isDataNode node1) = ([arg1_addr],[ap1_addr,ap2_addr]:dump,heap,globals,stats)
  | otherwise = ([arg2_addr],[ap2_addr]:dump,heap,globals,stats)
  where node1 = hLookup heap arg1_addr
        node2 = hLookup heap arg2_addr
        [arg1_addr,arg2_addr] = getargs heap stack
        [_,ap1_addr,ap2_addr] = stack

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state arithOp = primDyadic state nodeOp
    where nodeOp (NNum a) (NNum b) = NNum (arithOp a b)
          nodeOp _ _ = error "arith: arguments should be number"

primComp :: TiState -> (Int -> Int -> Bool) -> TiState
primComp state compOp = primDyadic state nodeOp
    where nodeOp (NNum a) (NNum b) = NData (if compOp a b then 2 else 1) []
          nodeOp _ _ = error "comp: arguments should be number"

primNeg :: TiState -> TiState
primNeg (stack,_,_,_,_) | length stack /= 2 = error "negation arguments error"
primNeg (stack,dump,heap,globals,stats) = if isDataNode node
                                             then  let (NNum num) = node
                                                       new_heap = hUpdate heap addr (NNum (-num))
                                                    in ([addr],dump,new_heap,globals,stats)
                                             else ([arg_addr],[addr]:dump,heap,globals,stats)
    where node = hLookup heap arg_addr
          arg_addr = head $ getargs heap stack
          [_,addr] = stack

primConstr :: TiState -> Int -> Int -> TiState
primConstr (stack,dump,heap,globals,stats) tag arity = (new_stack,dump,new_heap,globals,stats)
    where args = take arity (getargs heap stack)
          new_heap = hUpdate heap (stack!!arity) (NData tag args)
          new_stack = drop arity stack

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack,dump,heap,globals,stats) name arg_names body =
    if length arg_names + 1 > length stack
       then error (name ++ " is applied to too few arguments!")
       else (new_stack,dump,new_heap,globals,tiStatIncScReducs stats)
           where env = arg_bindings ++ globals
                 arg_bindings = zip arg_names (getargs heap stack)
                 new_stack = drop (length arg_names) stack
                 new_heap = instantiateAndUpdate body (head new_stack) heap env

getargs :: TiHeap -> TiStack -> [Addr]
getargs _ [] = error "getargs: empty stack"
getargs heap (_:stack) = map get_arg stack
    where get_arg addr = arg where (NAp _ arg) = hLookup heap addr

instantiateAndUpdate :: CoreExpr -> Addr -> TiHeap -> TiGlobals -> TiHeap

instantiateAndUpdate (ENum n) addr heap _ = hUpdate heap addr (NNum n)

instantiateAndUpdate (EVar v) addr heap env = hUpdate heap addr (NInd (aLookup env v (error ("Undefined name " ++ show v))))

instantiateAndUpdate (EAp e1 e2) addr heap env = hUpdate heap2 addr (NAp a1 a2)
    where (heap1, a1) = instantiate e1 heap env
          (heap2, a2) = instantiate e2 heap1 env

instantiateAndUpdate (ELet _ defs body) addr heap env = instantiateAndUpdateLet defs body addr heap env

instantiateAndUpdate (EConstr tag arity) addr heap _ = instantiateAndUpdateConstr tag arity addr heap

instantiateAndUpdate _ _ _ _ = undefined

instantiateAndUpdateConstr :: Int -> Int -> Addr -> TiHeap -> TiHeap
instantiateAndUpdateConstr tag arity addr heap = hUpdate heap addr (NPrim "Pack" (PrimConstr tag arity))

instantiateAndUpdateLet :: [(Name, CoreExpr)] -> CoreExpr -> Addr -> TiHeap -> TiGlobals -> TiHeap
instantiateAndUpdateLet defs body addr heap env = instantiateAndUpdate body addr new_heap new_env
    where new_env = nenv ++ env
          (new_heap, nenv) = instantiateAndUpdateDefs defs addr heap new_env

instantiateAndUpdateDefs :: [(Name, CoreExpr)] -> Addr -> TiHeap -> TiGlobals -> (TiHeap, TiGlobals)
instantiateAndUpdateDefs defs _ heap env = mapAccuml instantiateDef heap defs
    where instantiateDef h def = (fheap, (fst def, addr))
            where (fheap,addr) = instantiate (snd def) h env

instantiate :: CoreExpr -> TiHeap -> TiGlobals -> (TiHeap, Addr)

instantiate (ENum n) heap _ = hAlloc heap (NNum n)

instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
    where (heap1, a1) = instantiate e1 heap env
          (heap2, a2) = instantiate e2 heap1 env

instantiate (EVar v) heap env = (heap, aLookup env v (error ("Undefined name " ++ show v)))

instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env

instantiate (ELet _ defs body) heap env = instantiateLet defs body heap env

instantiate _ _ _ = undefined

instantiateConstr :: Int -> Int -> TiHeap -> TiGlobals -> (TiHeap, Addr)
instantiateConstr tag arity heap _ = hAlloc heap (NPrim "Pack" (PrimConstr tag arity))

instantiateLet :: [(Name, CoreExpr)] -> CoreExpr -> TiHeap -> TiGlobals -> (TiHeap, Addr)
instantiateLet defs body heap env = instantiate body new_heap new_env
    where new_env = nenv ++ env
          (new_heap, nenv) = instantiateDefs defs heap new_env

instantiateDefs :: [(Name, CoreExpr)] -> TiHeap -> TiGlobals -> (TiHeap, TiGlobals)
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
showNode (NPrim name _) = iStr "NPrim " `iAppend` iStr name
showNode (NData name addrs) = iInterleave (iStr " ") ([iStr "NData", iStr (show name)] ++ map showAddr addrs)

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq
showFWAddr addr = iStr (replicate (4 - length str) ' ' ++ str)
    where str = show addr

showStats :: TiState -> Iseq
showStats (_, _, heap, _, stats) = iConcat [ iNewline, iNewline,
                                          iStr "Total number of steps = ", iNum (tiStatGetSteps stats), iNewline,
                                          iStr "Total number of heap allocations = ", iNum (getHeapAlloc heapStats), iNewline,
                                          iStr "Total number of heap updates = ", iNum (getHeapUpdate heapStats), iNewline,
                                          iStr "Total number of heap frees = ", iNum (getHeapFree heapStats), iNewline,
                                          iStr "Total number of max stack depth = ", iNum (tiStatGetMaxStack stats), iNewline,
                                          iStr "Total number of supercombinator reductions = ", iNum (tiStatGetScReducs stats), iNewline ]
                                              where heapStats = getHeapStats heap
