module Parser where

import Lang

import Control.Monad
import Control.Applicative
import Data.Char

type Token = (Int, String)

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_')
isNewline :: Char -> Bool
isNewline c = c `elem` "\n"

twoCharOps :: [String]
twoCharOps = ["==", "!=", ">=", "<=", "->"]

clex :: Int -> String -> [Token]
clex _ "" = []
clex n (c:cs) | isSpace c = clex (if isNewline c then n+1 else n) cs
clex n (c:cs) | isDigit c = (n, num_token) : clex n rest_cs
    where num_token = c : takeWhile isDigit cs
          rest_cs = dropWhile isDigit cs
clex n (c:cs) | isAlpha c = (n, var_tok) : clex n rest_cs
    where var_tok = c : takeWhile isIdChar cs
          rest_cs = dropWhile isIdChar cs
clex n ('|':'|':cs) = clex n (dropWhile (not . isNewline) cs)
clex n (a:b:cs) | [a,b] `elem` twoCharOps = (n, [a,b]) : clex n cs
clex n (c:cs) = (n, [c]) : clex n cs


type State = [Token]
newtype Parser a = Parser (State -> [(a, State)])

runParser :: Parser a -> (State -> [(a, State)])
runParser (Parser f) = f

instance Functor Parser where
    fmap f (Parser g) = Parser (map (\p -> (f $ fst p, snd p)) . g)

instance Applicative Parser where
    pure x = Parser (\s -> [(x, s)])
    p <*> q = Parser (\g -> [(b, z)|(f, y) <- runParser p g, (b, z) <- runParser (fmap f q) y])

instance Alternative Parser where
    empty = Parser (const [])
    m <|> n = Parser (\x -> let t = runParser m x in if null t then runParser n x else t)

instance MonadPlus Parser where
    mzero = Parser (const [])
    mplus p q = Parser (\x -> runParser p x ++ runParser q x)

instance Monad Parser where
    return = pure
    m >>= k = Parser (\x -> [(b, z)|(a, y) <- runParser m x, (b, z) <- runParser (k a) y])

item :: Parser String
item = Parser (\xs -> case xs of
                      [] -> []
                      ((_, s):x) -> [(s, x)])

(▷) :: Parser a -> (a -> Bool) -> Parser a
m ▷ p = m >>= \a -> if p a then return a else mzero

oneOf :: [String] -> Parser String
oneOf xs = item >>= \x -> if x `elem` xs then return x else empty

pLit :: String -> Parser String
pLit s = item ▷ (== s)

keywords :: [String]
keywords = ["let","letrec","case","in","of","Pack"]

pVar :: Parser String
pVar = item ▷ (\s -> isAlpha (head s) && s `notElem` keywords)

pNum :: Parser Int
pNum = do n <- item ▷ all isDigit
          return (read n)

many1 :: Parser a -> Parser [a]
many1 p = do x <- p
             xs <- many p
             return (x:xs)

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep pa pb = do sc <- pa
                             scs <- many (do _ <- pb; pa)
                             return (sc:scs)

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc = do name <- pVar
         args <- many pVar
         _ <- pLit "="
         x <- pExpr
         return (name, args, x)

pExpr :: Parser CoreExpr
pExpr = pLet <|> pCase <|> pLambda <|> pExpr1

data PartialExpr = NoOp | FoundOp Name CoreExpr

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 NoOp = e1
assembleOp e1 (FoundOp op e2) = EAp (EAp (EVar op) e1) e2

pExpr1 :: Parser CoreExpr
pExpr1 = do expr2 <- pExpr2
            expr1c <- pExpr1c
            return (assembleOp expr2 expr1c)

pExpr1c :: Parser PartialExpr
pExpr1c = do _ <- pLit "|"
             expr1 <- pExpr1
             return (FoundOp "|" expr1)
          <|> return NoOp

pExpr2 :: Parser CoreExpr
pExpr2 = do expr3 <- pExpr3
            expr2c <- pExpr2c
            return (assembleOp expr3 expr2c)

pExpr2c :: Parser PartialExpr
pExpr2c = do _ <- pLit "&"
             expr2 <- pExpr2
             return (FoundOp "&" expr2)
          <|> return NoOp

pExpr3 :: Parser CoreExpr
pExpr3 = do expr4 <- pExpr4
            expr3c <- pExpr3c
            return (assembleOp expr4 expr3c)

pExpr3c :: Parser PartialExpr
pExpr3c = do op <- oneOf ["==","!=",">=",">","<=","<"]
             expr4 <- pExpr4
             return (FoundOp op expr4)
          <|> return NoOp

pExpr4 :: Parser CoreExpr
pExpr4 = do expr5 <- pExpr5
            expr4c <- pExpr4c
            return (assembleOp expr5 expr4c)

pExpr4c :: Parser PartialExpr
pExpr4c = do op <- oneOf ["+","-"]
             expr <- if op == "+" then pExpr4 else pExpr5
             return (FoundOp op expr)
          <|> return NoOp

pExpr5 :: Parser CoreExpr
pExpr5 = do expr6 <- pApply
            expr5c <- pExpr5c
            return (assembleOp expr6 expr5c)

pExpr5c :: Parser PartialExpr
pExpr5c = do op <- oneOf ["*","/"]
             expr <- if op == "*" then pExpr5 else pApply
             return (FoundOp op expr)
          <|> return NoOp

pAexpr :: Parser CoreExpr
pAexpr = pENum <|> pEVar <|> pPack <|> pParen

pPack :: Parser CoreExpr
pPack = do _ <- pLit "Pack"
           _ <- pLit "{"
           x <- pNum
           _ <- pLit ","
           y <- pNum
           _ <- pLit "}"
           return (EConstr x y)

pParen :: Parser CoreExpr
pParen = do _ <- pLit "("
            e <- pExpr
            _ <- pLit ")"
            return e

pENum :: Parser CoreExpr
pENum = do x <- pNum
           return (ENum x)

pEVar :: Parser CoreExpr
pEVar = do x <- pVar
           return (EVar x)

pLet :: Parser CoreExpr
pLet = do r <- pLit "let" <|> pLit "letrec"
          s <- pEqts
          _ <- pLit "in"
          x <- pExpr
          return (ELet (if r == "let" then nonRecursive else recursive) s x)

pEqts :: Parser [(Name, CoreExpr)]
pEqts = pOneOrMoreWithSep pEqt (pLit ";")

pEqt :: Parser (Name, CoreExpr)
pEqt = do name <- pVar
          _    <- pLit "="
          expr <- pExpr
          return (name, expr)

pCase :: Parser CoreExpr
pCase = do _ <- pLit "case"
           expr <- pExpr
           _ <- pLit "of"
           alts <- pAlters
           return (ECase expr alts)

pAlters :: Parser [CoreAlt]
pAlters = pOneOrMoreWithSep pAlter (pLit ";")

pAlter :: Parser CoreAlt
pAlter = do _ <- pLit "<"
            n <- pNum
            _ <- pLit ">"
            bnds <- many pVar
            _ <- pLit "->"
            expr <- pExpr
            return (n, bnds, expr)

pApply :: Parser CoreExpr
pApply = do exps <- many1 pAexpr
            return (foldl1 EAp exps)

pLambda :: Parser CoreExpr
pLambda = do _ <- pLit "\\"
             args <- many1 pVar
             _ <- pLit "."
             expr <- pExpr
             return (ELam args expr)
