import Data.List
import Test.QuickCheck

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

-- TODO simplify typedef to make sense of dispatch
variables :: LambdaTerm -> [LambdaTerm]
variables expr = undefined -- [y | y <- (subTerms expr), ]

-- TODO
rename :: LambdaTerm -> LambdaTerm -> LambdaTerm
-- rename a (LambdaVariable b)                  = 
-- rename _ _                                   = undefined
rename a b = helperfunction a b where
  frees = freeVariables a
  helperfunction = undefined

-- check free and bound vars
alphaCongruent :: LambdaTerm -> LambdaTerm -> Bool
alphaCongruent = undefined

substitute :: LambdaTerm -> LambdaTerm -> LambdaTerm
substitute = undefined

-- check if abstraction, substitute
betaReduce :: LambdaTerm -> LambdaTerm
betaReduce = undefined

-- find next unused var name in alphabet, maybe lazy zip of alphabet symbols
alphabet = ['a'..'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] 
genVariable :: [LambdaTerm] -> LambdaTerm
genVariable = undefined

isNormalForm :: LambdaTerm -> Bool
isNormalForm expr = expr == betaReduce expr

-- TODO quickcheck to verify correctness

-- TODO examples, numbers and arithmetic implementation

example1 = (Abstraction (LambdaVariable "x") (Abstraction (LambdaVariable "y") (Application (Application (LambdaVariable "z") (LambdaVariable"z")) (LambdaVariable "x"))))

yCombinator :: LambdaTerm
yCombinator = (Abstraction (LambdaVariable "g") (Application (Abstraction (LambdaVariable "x") (Application (LambdaVariable "g")
                                                                                           (Application (LambdaVariable "x")
                                                                                                        (LambdaVariable "x"))))
                                                         (Abstraction (LambdaVariable "x") (Application (LambdaVariable "g")
                                                                                           (Application (LambdaVariable "x")
                                                                                                        (LambdaVariable "x"))))))
printVerbose :: LambdaTerm -> String -> String
printVerbose expr title = title ++ "\nSubterms\n" ++ unlines (map (show) (subTerms expr)) ++ "\nFree Variables\n" ++ unlines (map (show) (freeVariables expr))
--
main :: IO ()
main = do
  putStrLn $ printVerbose yCombinator "The Y-combinator"
  putStrLn $ printVerbose example1 "Example term 1"
  putStrLn alphabet


