module Lang where

data Expr a = EVar Name
            | ENum Int
            | EConstr Int Int
            | EAp (Expr a) (Expr a)
            | ELet IsRec [(a, Expr a)] (Expr a)
            | ECase (Expr a) [Alter a]
            | ELam [a] (Expr a)
            deriving (Show)

type CoreExpr = Expr Name
type Name = String
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

bindersOf :: [(a,b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

rhssOf :: [(a,b)] -> [b]
rhssOf defns = [rhs | (_, rhs) <- defns]

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _        = False

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name
type Program a = [ScDefn a]
type CoreProgram = Program Name
