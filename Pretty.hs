module Pretty where

import Lang

pprExpr :: CoreExpr -> Iseq
pprExpr (ENum n) = iStr (show n)
pprExpr (EVar v) = iStr v
pprExpr (EAp e1 e2) = pprExpr e1 `iAppend` iStr " " `iAppend` pprAExpr e2
pprExpr (EConstr x y) = iConcat [ iStr "Pack{", iStr (show x), iStr ", ", iStr (show y), iStr "}"]
pprExpr (ECase e alters) = iConcat [ iStr "case ", iIndent (pprAExpr e), iStr " of", iNewline,
                                     iStr "  ", iIndent (pprAlters alters) ]
pprExpr (ELam ns e) = iConcat [ iStr "λ", iInterleave (iStr " ") (map iStr ns),
                                iStr " -> ", iIndent (pprAExpr e) ]
pprExpr (ELet isrec defns expr) = iConcat [ iStr keyword, iNewline,
                                            iStr "  ", iIndent (pprDefns defns), iNewline,
                                            iStr "in ", pprExpr expr ]
                                                where keyword = if isrec then "letrec" else "let"

pprDefns :: [(Name, CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
            where sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]

pprAlters :: [Alter Name] -> Iseq
pprAlters alters = iInterleave sep (map pprAlter alters)
    where sep = iConcat [ iStr ";", iNewline ]

pprAlter :: Alter Name -> Iseq
pprAlter (n, ns, e) = iConcat [ iStr (show n), iConcat (map iStr ns), iStr " -> ", iIndent (pprAExpr e) ]

pprAExpr :: CoreExpr -> Iseq
pprAExpr e = if isAtomicExpr e
                then pprExpr e
                else iStr "(" `iAppend` pprExpr e `iAppend` iStr ")"

pprProgram :: CoreProgram -> Iseq
pprProgram [] = iNil
pprProgram ((name, ns, e):ps) = iConcat [ iInterleave (iStr " ") (map iStr (name:ns)),
                                          iStr " = ", iIndent (pprAExpr e), iNewline,
                                          pprProgram ps ]

data Iseq = INil
          | IStr String
          | IAppend Iseq Iseq
          | IIndent Iseq
          | INewline

iNil :: Iseq
iNil = INil

iStr :: String -> Iseq
iStr = IStr

iAppend :: Iseq -> Iseq -> Iseq
iAppend seq1 seq2 = case seq1 of
    INil -> seq2
    _    -> case seq2 of
              INil -> seq1
              _    -> IAppend seq1 seq2

iConcat :: [Iseq] -> Iseq
iConcat = foldr iAppend iNil

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ [] = INil
iInterleave _ [sq] = sq
iInterleave it (sq:sqs) = sq `iAppend` it `iAppend` iInterleave it sqs

iNewline :: Iseq
iNewline = INewline

iIndent  :: Iseq -> Iseq
iIndent = IIndent

iDisplay :: Iseq -> String
iDisplay sq = flatten 0 [(sq, 0)]

iNum :: Int -> Iseq
iNum n = iStr (show n)

iFWNum :: Int -> Int -> Iseq
iFWNum width n = iStr (replicate (width - length digits) ' ' ++ digits)
    where digits = show n

iLayn :: [Iseq] -> Iseq
iLayn seqs = iConcat (zipWith (curry lay_item) [1..] seqs)
    where lay_item (n, sq) = iConcat [ iFWNum 4 n, iStr ") ", iIndent sq, iNewline ]

flatten :: Int -> [(Iseq,Int)] -> String
flatten _ [] = ""
flatten col ((INil, _) : seqs) = flatten col seqs
flatten col ((IStr s, _) : seqs) = s ++ flatten (col + length s) seqs
flatten col ((IAppend seq1 seq2, indent) : seqs) = flatten col ((seq1, indent) : (seq2, indent) : seqs)
flatten _ ((INewline, indent) : seqs) = '\n': replicate indent ' ' ++ flatten indent seqs
flatten col ((IIndent sq, _) : seqs) = flatten col ((sq, col) : seqs)

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)
