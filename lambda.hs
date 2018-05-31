import Data.List
import Test.QuickCheck.All
import Test.QuickCheck

import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

-- TODO shorthand type synonyms
-- IDEA use de Bruijn index system internally to avoid problems
--      with scope and variable naming
data LambdaTerm = LambdaVariable String |
                  Abstraction LambdaTerm  LambdaTerm |
                  Application LambdaTerm  LambdaTerm

instance Eq LambdaTerm where
  LambdaVariable a == LambdaVariable b = a == b
  Abstraction a b  == Abstraction c d  = a == c && b == d --
  Application a b  == Application c d  = a == c && b == d -- not taking alpha congruence into account yet
  _ == _ = False
                                                          -- idea: Application a b <alpha> Application c d => terms alpha congruent


-- TODO implement λ-> maybe
-- add type variables and arrow types
-- IDEA leverage haskells own typesystem??
-- data lambdaVar a
--data (Eq a) => LambdaVar a = LVar a
-- typeVar = String
-- type = typeVar | Arrow typeVar typeVar
-- define set of initial types bool nat etc
-- type derivation rules for var app abs
-- deriveType context expr = ....

data SimpleType = TypeVar String | Arrow SimpleType SimpleType

instance Show SimpleType where
  show (Arrow f@(Arrow _ _) c) = "("++ show f ++")" ++ "->" ++ show c
  show (Arrow a f@(Arrow _ _)) = show a ++ "-> (" ++ show f ++ ")" 
  show (Arrow (TypeVar a) (TypeVar b)) =  a ++ "->" ++ b
  show (TypeVar a) = a

type Context = [(LambdaTerm,SimpleType)]

createContext :: Context
createContext = []

addVarToContext :: Context -> LambdaTerm -> SimpleType -> Context
addVarToContext = undefined

exampleType1 :: SimpleType
exampleType1 = (Arrow (Arrow (TypeVar "A") (TypeVar "B")) (TypeVar "C"))

getType :: LambdaTerm -> SimpleType
getType = undefined


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
freeVariables expr@(Abstraction a b) = [y | y <- (freeVariables b), y /= a] -- set comprehension copypaste from intructor @ github.com/jllang
freeVariables expr@(Application a b) = freeVariables a `union` freeVariables b -- sometimes i forget you can just write math in haskell

bindings :: LambdaTerm -> [LambdaTerm]
bindings (LambdaVariable a)     = []
bindings expr@(Abstraction a b) = [a] ++ bindings b
bindings expr@(Application a b) = bindings a ++ bindings b

variables :: LambdaTerm -> [LambdaTerm]
variables (LambdaVariable a)     = [(LambdaVariable a)]
variables expr@(Abstraction a b) = variables a ++ variables b
variables expr@(Application a b) = variables a ++ variables b

-- TODO fix
alphaCongruent :: LambdaTerm -> LambdaTerm -> Bool
alphaCongruent (Application a b)  (Application c d)  = a `alphaCongruent` c && b `alphaCongruent` d
alphaCongruent (Abstraction a b)  (Abstraction c d)  = a `alphaCongruent` c && b `alphaCongruent` d
alphaCongruent (LambdaVariable a) (LambdaVariable b) = True
alphaCongruent _ _ = False

rename :: LambdaTerm -> LambdaTerm -> LambdaTerm -> LambdaTerm
rename term var newVar = helperfunction term var newVar where
  frees = freeVariables term
  vars  = variables     term
  binds = bindings      term 
  helperfunction term@(LambdaVariable a1) name newName                  = if (term == name  && not (elem name binds) && not (elem newName vars)) then newName else term
  helperfunction term@(Abstraction a@(LambdaVariable _) b) name newName = if ((elem name $ frees) && not (elem newName $ variables term)) then (Abstraction a (helperfunction b name newName)) else term
  helperfunction term@(Application a b) name newName                    = (Application (rename a name newName) (rename b name newName))
  helperfunction  _ _ _                                                 = undefined
rename term _ _ = term

betaReduce :: LambdaTerm -> LambdaTerm
betaReduce val@(Application (Abstraction a b) c)  = betaReduce $ rename b a c
betaReduce val@(Application a b)                  = Application (betaReduce a) (betaReduce b)
betaReduce val@(Abstraction a (LambdaVariable b)) = val
betaReduce val@(Abstraction a b)                  = (Abstraction a (betaReduce b))
betaReduce a = a

-- do it in IO with välivaiheet
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
betaReduceSafe num val@(Application (Abstraction a@(LambdaVariable _) b) c) = if num >= recDepth then val else betaReduceSafe (num+1) $ rename b a c
betaReduceSafe num val@(Application a b) = if num >= recDepth then val else Application (betaReduceSafe (num+1) a) (betaReduceSafe (num+1) b)
betaReduceSafe num val@(Abstraction a (LambdaVariable b)) = val -- if num >= recDepth then val else val
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

-- shorthand synonyms
simplifyIO = betaReduceIOSafe 0
simplify a = if isNormalForm a then a else simplify $ betaReduceSafe 0 a

-- find next unused var name in alphabet, maybe lazy zip of alphabet symbols
alphabet = ['a'..'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
lambdaSymbols = alphabet ++ ['λ',' ','(',')','\\','.']
genVariable :: [LambdaTerm] -> LambdaTerm
genVariable env = undefined

isNormalForm :: LambdaTerm -> Bool
isNormalForm expr = expr == betaReduceSafe 0 expr

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
  
-- examples, numbers and arithmetic implementation
-- possibly from type theory book or wikipedia
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

showVars     expr = "Variables\n" ++ unlines(map (show) (variables expr)) ++
                    "\nFree Variables\n" ++ unlines (map (show) (freeVariables expr)) ++ "\nBindings\n" ++ unlines (map (show) (bindings expr))
showSimplify expr = "Reduced form\n" ++ show (betaReduce expr)
printVerbose :: LambdaTerm -> String -> String
printVerbose expr title = title ++ "\nSubterms\n" ++ unlines (map (show) (subTerms expr)) ++ "\nVariables\n" ++ unlines(map (show) (variables expr)) ++
                          "\nFree Variables\n" ++ unlines (map (show) (freeVariables expr)) ++ "\nBindings\n" ++ unlines (map (show) (bindings expr))

prettyPrint expr title = title ++ showSubterms expr ++ showVars expr ++ showSimplify expr

-- TODO QuickCheck
-- instance Arbitrary LambdaTerm
genSafeChar :: Gen Char
genSafeChar = elements alphabet

genSafeString :: Gen String
genSafeString = listOf1 genSafeChar

  
instance Arbitrary LambdaTerm where
  arbitrary = do
    n <- choose (1,3) :: Gen Int
    case n of
      1 -> do x <- genSafeString :: Gen String
              let c = take 1 x   :: String
              return (LambdaVariable c)-- term
      2 -> do
        x <- genSafeString :: Gen String
        let c = take 1 x   :: String
        y <- arbitrary     :: Gen LambdaTerm
        return (Abstraction (LambdaVariable c) y)-- abs
      3 -> do
        x <- arbitrary :: Gen LambdaTerm
        y <- arbitrary :: Gen LambdaTerm
        return (Application x y)-- app


-- property tests
prop_read :: LambdaTerm -> Bool
prop_read x = x == (readTerm $ show x)

-- example calculations
-- combinatory logic: simplify (Application (Application sComb kComb) kComb) -> id
prop_comb = simplify (Application (Application sComb kComb) kComb) `alphaCongruent` iComb

test_t1  = simplify t1 `alphaCongruent` readTerm "(λ y. (λ z. z))"
test_t2  = simplify t2 `alphaCongruent` readTerm "λ x. x"
test_t3  = simplify t3 `alphaCongruent` readTerm "(λ y. (λ a. a))"
test_t4  = simplify t4 `alphaCongruent` readTerm "(λ a. a)"
test_t5  = simplify t5 `alphaCongruent` readTerm "(λ y. y)"
test_t6  = simplify t6 `alphaCongruent` readTerm "(λ b. b)"
test_t7  = simplify t5 `alphaCongruent` readTerm "(λ y. y)"
test_t8  = simplify t8 `alphaCongruent` readTerm "(λ a. a)"
test_t9  = simplify t9 `alphaCongruent` readTerm "(λ a. (λ b. (a (a (a (a (a (a (a (a b))))))))))"


-- -- options = TestOptions
-- --       {
-- --         no_of_tests     = 200
-- --       , lenght_of_tests = 1
-- --       , debug_tests     = False
-- --       }

main :: IO ()
main = do
  -- putStrLn "Untyped Lambda Calculus"
  -- putStrLn "Running tests"
  -- runTests "simple" options
  --   [
  --     run prop_read
  --   , run prop_comb
  --   , run test_t1
  --   , run test_t2
  --   , run test_t3
  --   , run test_t4
  --   , run test_t5
  --   , run test_t6
  --   , run test_t7
  --   , run test_t8
  --   , run test_t9

  --   ]
  -- putStrLn $ printVerbose yCombinator "The Y-combinator"
  -- putStrLn $ printVerbose example1 "Example term 1"
  -- putStrLn alphabet
  x <- getLine
 -- y <- arbitrary :: Gen String
 -- putStrLn y
  if x == "" then return () else do
    putStrLn $ show $ simplify $ readTerm x
    main
  
