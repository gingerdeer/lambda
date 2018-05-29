import Data.List
import Test.QuickCheck

import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

-- TODO shorthand type synonyms
-- IDEA use de Bruijn index system internally to avoid problems
--      with scope and variable naming
-- very simple typedef, with this its for example possible to define an abstraction over a term which is not possible in LC
-- TODO better typedef
data LambdaTerm = LambdaVariable String |
                  Abstraction LambdaTerm  LambdaTerm |
                  Application LambdaTerm  LambdaTerm

instance Eq LambdaTerm where
  LambdaVariable a == LambdaVariable b = a == b
  Abstraction a b  == Abstraction c d  = a == c && b == d --
  Application a b  == Application c d  = a == c && b == d -- not taking alpha congruence into account yet
  _ == _ = False
                                                          -- idea: Application a b <alpha> Application c d => terms alpha congruent

-- TODO simplifying rules
instance Show LambdaTerm where
  show (LambdaVariable a) = a
  show (Abstraction a b)  = "λ" ++ show a ++ "." ++ show b ++ ""
  show (Application a b)  = "(" ++ show a ++ " " ++ show b ++ ")"

-- works
subTerms :: LambdaTerm -> [LambdaTerm]
subTerms (LambdaVariable a)      = [(LambdaVariable a)]
subTerms expr@(Abstraction _ b)  = [expr] ++ subTerms b
subTerms expr@(Application a b)  = [expr] ++ subTerms a ++ subTerms b

-- works
freeVariables :: LambdaTerm -> [LambdaTerm]
freeVariables (LambdaVariable a) = [(LambdaVariable a)]
freeVariables expr@(Abstraction a b) = [y | y <- (freeVariables b), y /= a] -- set literal goodness, copypaste from intructor @ ....
freeVariables expr@(Application a b) = freeVariables a `union` freeVariables b

bindings :: LambdaTerm -> [LambdaTerm]
bindings (LambdaVariable a) = []
bindings expr@(Abstraction a b) = [a] ++ bindings b
bindings expr@(Application a b) = bindings a ++ bindings b

-- TODO simplify typedef to make sense of dispatch
variables :: LambdaTerm -> [LambdaTerm]
variables (LambdaVariable a) = [(LambdaVariable a)]
variables expr@(Abstraction a b) = variables a ++ variables b
variables expr@(Application a b) = variables a ++ variables b

-- TODO
rename :: LambdaTerm -> LambdaTerm -> LambdaTerm -> LambdaTerm
rename term var newVar = helperfunction term var newVar where
  frees = freeVariables term
  vars  = variables term
  binds = bindings term 
  helperfunction  term@(LambdaVariable a1) name newName = if (term == name  && not (elem name binds) && not (elem newName frees) && not (elem newName binds)) then newName else term
  helperfunction  term@(Abstraction a b) name newName   = (Abstraction a (helperfunction b name newName))
  helperfunction  term@(Application a b) name newName   = (Application (helperfunction a name newName) (helperfunction b name newName))
  helperfunction  _ _ _ = undefined

-- TODO fix: check free and bound variables in exprs
-- 
alphaCongruent :: LambdaTerm -> LambdaTerm -> Bool
alphaCongruent (Application a b)  (Application c d) = a `alphaCongruent` c && b `alphaCongruent` d
alphaCongruent (Abstraction a b)  (Abstraction c d) = a == c && b `alphaCongruent` d
-- alphaCongruent (Abstraction (LambdaVariable a) (LambdaVariable b)) (Abstraction (LambdaVariable c) (LambdaVariable d)) = 
alphaCongruent (LambdaVariable a) (LambdaVariable b) = True
alphaCongruent _ _ = False


-- performs single step of beta reduction on an application
betaReduce :: LambdaTerm -> LambdaTerm
betaReduce val@(Application (Abstraction a b) c) = betaReduce $ rename b a c
betaReduce val@(Application a b) = Application (betaReduce a) (betaReduce b)
betaReduce val@(Abstraction a (LambdaVariable b)) = val
betaReduce val@(Abstraction a b) = (Abstraction a (betaReduce b))
betaReduce a = a

betaReduceIO :: LambdaTerm -> IO LambdaTerm
betaReduceIO val@(Application (Abstraction a b) c) = do
  putStrLn $ show val
  betaReduceIO $ rename b a c
betaReduceIO val@(Application a b) = do
  putStrLn $ show val
  if isNormalForm val then return val else betaReduceIO $ Application (betaReduce a) (betaReduce b)
  
betaReduceIO val@(Abstraction a (LambdaVariable b)) = do
  putStrLn $ show val
  return val
betaReduceIO val@(Abstraction a b) = do
  putStrLn $ show val
  if isNormalForm b then return val else betaReduceIO $ (Abstraction a (betaReduce b))
betaReduceIO a = do return a



-- no infinite loops in case of non terminating exprs
-- doesnt really detect infinite growth in expansions:  betaReduceIOSafe (Application example3 yCombinator)
recDepth = 10
maxLen = 200

betaReduceSafe :: Int -> LambdaTerm -> LambdaTerm
betaReduceSafe num val@(Application (Abstraction a b) c) = if num >= recDepth then val else betaReduceSafe (num+1) $ rename b a c
betaReduceSafe num val@(Application a b) = if num >= recDepth then val else Application (betaReduceSafe (num+1) a) (betaReduceSafe (num+1) b)
betaReduceSafe num val@(Abstraction a (LambdaVariable b)) = if num >= recDepth then val else val
betaReduceSafe num val@(Abstraction a b) = if num >= recDepth then val else (Abstraction a (betaReduceSafe (num+1) b))
betaReduceSafe num a = a

betaReduceIOSafe :: Int ->LambdaTerm -> IO LambdaTerm
betaReduceIOSafe num val@(Application (Abstraction a b) c) = if num >= recDepth then return val else do
  putStrLn $ take maxLen $ show val
  betaReduceIOSafe   (num+1) (rename b a c)
betaReduceIOSafe num val@(Application a b) = do
  putStrLn $ take maxLen $show val
  if isNormalForm val then return val else betaReduceIOSafe (num+1) (Application (betaReduce a) (betaReduce b))
betaReduceIOSafe num val@(Abstraction a (LambdaVariable b)) = if num >= recDepth then return val else do
  putStrLn $ take maxLen $ show val
  return val
betaReduceIOSafe num val@(Abstraction a b) = if num >= recDepth then return val else do
  putStrLn $ take maxLen $ show val
  if isNormalForm b then return val else betaReduceIOSafe (num+1) (Abstraction a (betaReduce b))
betaReduceIOSafe num a = do return a

-- shorthand synonym
simplifyIO = betaReduceIOSafe 0
simplify a = if isNormalForm a then a else simplify $ betaReduceSafe 0 a

-- find next unused var name in alphabet, maybe lazy zip of alphabet symbols
-- 
alphabet = ['a'..'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
lambdaSymbols = alphabet ++ ['λ',' ','(',')','\\','.']
genVariable :: [LambdaTerm] -> LambdaTerm
genVariable env = undefined

isNormalForm :: LambdaTerm -> Bool
isNormalForm expr = expr == betaReduceSafe 0 expr

-- TODO parser
asd :: Char -> Char -> Bool
asd a b = elem a alphabet && elem b alphabet

valid str = foldl (&&) True $ map (`elem` lambdaSymbols) str
alphabetRegex = "[" ++ alphabet ++ "]"
lambdasRegex = "[" ++ lambdaSymbols ++ "]"
varRegex = "["++alphabetRegex ++ "].*"
appRegex = "("++varRegex++" "++varRegex++")"
absRegex = "λ."++varRegex++"|"++"λ."++appRegex
regex = varRegex ++ "|" ++ absRegex ++ "|" ++ varRegex

parseVar :: Parser LambdaTerm
parseVar = do
  x <- many1 $ oneOf alphabet
  return (LambdaVariable x)

parseAbsBrackets :: Parser LambdaTerm
parseAbsBrackets = do
  string "(λ"
  many space
  expr1 <- parseVar
  char '.'
  many space
  expr2 <- parseTerm -- <|> parseAppNoBrackets
  char ')'
  return (Abstraction expr1 expr2)

parseAbsNoBrackets :: Parser LambdaTerm
parseAbsNoBrackets = do
  string "λ"
  many space
  expr1 <- parseVar
  char '.'
  many space
  expr2 <- parseTerm -- <|> parseAppNoBrackets
  return (Abstraction expr1 expr2)
  
parseAbs :: Parser LambdaTerm
parseAbs = do
  try (parseAbsBrackets <|> parseAbsNoBrackets)

parseAppBrackets :: Parser LambdaTerm
parseAppBrackets = do
  char '('
  expr1 <- parseTerm
  many space
  expr2 <- parseTerm -- <|> parseAppNoBrackets
  char ')'
  return (Application expr1 expr2)
  
parseAppNoBrackets :: Parser LambdaTerm
parseAppNoBrackets = do
  expr1 <- parseVar <|> parseAbs
  many space
  expr2 <- parseVar <|> parseAbs
  return (Application expr1 expr2)
  
parseApp :: Parser LambdaTerm
parseApp = do
  try parseAppBrackets -- <|> parseAppNoBrackets)

parseTerm :: Parser LambdaTerm
parseTerm = parseApp <|> parseAbs <|> parseVar -- <|> parseList

readTerm :: String -> LambdaTerm
readTerm input = case parse parseTerm "haskell" input of
  Left  err -> (LambdaVariable ("parse error" ++ show err))
  Right val -> val

-- parse :: String -> LambdaTerm
-- parse str = if valid str then undefined else (LambdaVariable "PARSE ERROR")
-- TODO quickcheck to verify correctness

-- TODO examples, numbers and arithmetic implementation

-- possibly from type theory book
example1 = (Abstraction (LambdaVariable "x") (Abstraction (LambdaVariable "y") (Application (Application (LambdaVariable "z") (LambdaVariable"z")) (LambdaVariable "x"))))
example2 = (Abstraction (LambdaVariable "x") (Application (Abstraction (LambdaVariable "y") (LambdaVariable "y")) (LambdaVariable "x")))
-- from type theory book
example3 = (Application (Abstraction (LambdaVariable "x") (Abstraction (LambdaVariable "y") (Abstraction (LambdaVariable "z")
                             (Application (LambdaVariable "z") (Application (Application (LambdaVariable "x") (LambdaVariable "y")) (LambdaVariable "z"))))))
          (Abstraction (LambdaVariable "u") (LambdaVariable "u")) )
-- church num
example4 = (Abstraction (LambdaVariable "f")
            (Abstraction (LambdaVariable "x")
                                              (Application (LambdaVariable "f")
                                              (Application (LambdaVariable "f")
                                               (Application (LambdaVariable "f") (LambdaVariable "x"))))))
-- non reducing
example5 = (Application (Abstraction (LambdaVariable "x") (Application (LambdaVariable "x") (LambdaVariable "x"))) (Abstraction (LambdaVariable "x") (Application (LambdaVariable "x") (LambdaVariable "x"))))

-- TODO maybe add stackexchange code golf examples
t1 = readTerm "((λ x. x) (λ y. (λ z. z)))"
t2 = readTerm "(λ x. ((λ y. y) x))"
t3 = readTerm "((λ x. (λ y. x)) (λ a. a))"
t4 = readTerm "(((λ x. (λ y. x)) (λ a. a)) (λ b. b))"
t5 = readTerm "((λ x. (λ y. y)) (λ a. a))"
t6 = readTerm "(((λ x. (λ y. y)) (λ a. a)) (λ b. b))"
t7 = readTerm "((λx. (x x)) (λx. (x x)))"
t8 = readTerm "(((λ x. (λ y. x)) (λ a. a)) ((λx. (x x)) (λx. (x x))))"
t9 = readTerm "((λ a. (λ b. (a (a (a b))))) (λ c. (λ d. (c (c d)))))"

-- TODO arithmetic operators



-- TODO combinatory logic examples
kComb = (Abstraction (LambdaVariable "x") (Abstraction (LambdaVariable "y") (LambdaVariable "x")))
sComb = (Abstraction (LambdaVariable "x") (Abstraction (LambdaVariable "y") (Abstraction (LambdaVariable "z") (Application (Application (LambdaVariable "x") (LambdaVariable "z")) (Application (LambdaVariable "y") (LambdaVariable "z"))))))
iComb = (Abstraction (LambdaVariable "x") (LambdaVariable "x"))
-- simplify (Application (Application sComb kComb) kComb) -> id

yCombinator :: LambdaTerm
yCombinator = (Abstraction (LambdaVariable "g") (Application (Abstraction (LambdaVariable "x") (Application (LambdaVariable "g")
                                                                                           (Application (LambdaVariable "x")
                                                                                                        (LambdaVariable "x"))))
                                                         (Abstraction (LambdaVariable "x") (Application (LambdaVariable "g")
                                                                                           (Application (LambdaVariable "x")
                                                                                             (LambdaVariable "x"))))))
              
-- TODO pretty printer functionality
showSubterms :: LambdaTerm -> String
showSubterms expr = "Subterms\n"++ unlines (map (show) (subTerms expr)) ++ "\n"


showVars     expr = "Variables" ++ unlines(map (show) (variables expr)) ++
                    "\nFree Variables\n" ++ unlines (map (show) (freeVariables expr)) ++ "\nBindings\n" ++ unlines (map (show) (bindings expr))
showSimplify expr = "Reduced form\n" ++ show (betaReduce expr)
printVerbose :: LambdaTerm -> String -> String
printVerbose expr title = title ++ "\nSubterms\n" ++ unlines (map (show) (subTerms expr)) ++ "\nVariables\n" ++ unlines(map (show) (variables expr)) ++
                          "\nFree Variables\n" ++ unlines (map (show) (freeVariables expr)) ++ "\nBindings\n" ++ unlines (map (show) (bindings expr))

prettyPrint expr title = title ++ showSubterms expr ++ showVars expr ++ showSimplify expr

--





main :: IO ()
main = do
  -- putStrLn $ printVerbose yCombinator "The Y-combinator"
  -- putStrLn $ printVerbose example1 "Example term 1"
  -- putStrLn alphabet
  x <- getLine
  if x == "" then return () else do
    putStrLn $ show $ simplify $ readTerm x
    main
  
