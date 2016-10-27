module Main where

import Data.Maybe (mapMaybe, isJust, fromJust)
import Data.List (elemIndex)
import Text.ParserCombinators.ReadP
import Data.Char (isUpper, isDigit)
import Control.Applicative ((<|>))
import Control.Monad (forM_)
import System.Environment (getArgs)
import System.IO (openFile, hClose, hPutStrLn, IOMode (..), hSetEncoding, utf8)
--import System.CPUTime
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- Main Logic
   
infixl 8 :/\
infixl 7 :\/
infixr 6 :->

data Statement = Var Lexeme
               | Not Statement
               | Statement :-> Statement
               | Statement :\/ Statement
               | Statement :/\ Statement
    deriving (Eq, Show, Ord)

type Lexeme = String
type Hypothesis = Statement

-- Checks if the given statement satisfies standart axiom and returns the number of that axiom
-- axiomNumber :: Statement -> Maybe Int
axiomNumber (a :-> b :-> a1)                                  | a == a1 = Just 1
axiomNumber ((a :-> b) :-> (a1 :-> b1 :-> c) :-> (a2 :-> c1)) | a == a1 && a == a2 && b == b1 && c == c1 = Just 2
axiomNumber (a :-> b :-> a1 :/\ b1)                           | a == a1 && b == b1 = Just 3
axiomNumber (a :/\ b :-> a1)                                  | a == a1 = Just 4
axiomNumber (a :/\ b :-> b1)                                  | b == b1 = Just 5 
axiomNumber (a :-> a1 :\/ b)                                  | a == a1 = Just 6
axiomNumber (b :-> a :\/ b1)                                  | b == b1 = Just 7
axiomNumber ((a :-> c) :-> (b :-> c1) :-> (a1 :\/ b1 :-> c2)) | a == a1 && b == b1 && c == c1 && c == c2 = Just 8
axiomNumber ((a :-> b) :-> (a1 :-> Not b1) :-> Not a2)        | a == a1 && b == b1 && a == a2 = Just 9 
axiomNumber (Not (Not a) :-> a1)                              | a == a1 = Just 10
axiomNumber _ = Nothing

commentAxiom s = (("Сх. акс. " ++) . show) <$> axiomNumber s

modusPonens :: [(Int, Statement)] -> Map Statement Int -> Statement -> Maybe String
modusPonens proved provedMap statement = 
    case mapMaybe filteringFunction proved of
       []         -> Nothing
       ((i, j):_) -> Just $ "M.P. " ++ show j ++ ", " ++ show i
    where 
        filteringFunction (i, stm) = 
            if stm `implicatesTo` statement then
                (\j -> (i, j)) <$> (Map.lookup (left stm) provedMap)
            else 
                Nothing
        left (l :-> _) = l

implicatesTo :: Statement -> Statement -> Bool
(a :-> b) `implicatesTo` b1 = b == b1
_         `implicatesTo` _  = False

annotations :: [Hypothesis] -> [Statement] -> [String]
annotations = makeAnnotations 1 [] Map.empty

makeAnnotations :: Int -> [(Int, Hypothesis)] -> Map Hypothesis Int -> [Hypothesis] -> [Statement] -> [String]
makeAnnotations i accum mapAccum hypos []     = []
makeAnnotations i accum mapAccum hypos (s:ss) = annotation : makeAnnotations (i+1) newListAccum newMapAccum hypos ss 
  where
    annotation | isJust hypo  = fromJust hypo
               | isJust axiom = fromJust axiom
               | isJust modus = fromJust modus
               | otherwise    = "Не доказано"
    modus = modusPonens accum mapAccum s
    axiom = commentAxiom s
    hypo  = ("Предп. " ++) <$> show <$> (+ 1) <$> elemIndex s hypos
    --bool  = isJust hypo || isJust axiom || isJust modus
    newListAccum = {-applyIf bool-} ((i, s):) accum
    newMapAccum  = {-applyIf bool-} (Map.insert s i) mapAccum

applyIf b f x = if b then f x else x

-- Parser

whiteSpaces = skipSpaces
upper = satisfy isUpper
digit = satisfy isDigit

parens :: ReadP Statement -> ReadP Statement
parens p = do
    char '('
    e <- p
    char ')'
    whiteSpaces
    return e

atom :: ReadP Statement
atom = do
    l <- upper
    ls <- many (upper <|> digit)
    whiteSpaces
    return $ Var (l:ls)

binar :: String -> (Statement -> Statement -> Statement) -> ReadP (Statement -> Statement -> Statement)
binar name operation = do
    string name
    whiteSpaces
    return $ operation

implication = binar "->" (:->) 
conjunction = binar "&"  (:/\)  
disjunction = binar "|"  (:\/)

negParser p = do
    char '!'
    whiteSpaces
    e <- p
    return $ Not e

impl = disj `chainr1` implication
disj = conj `chainl1` disjunction
conj = term `chainl1` conjunction
term = atom
       <|> negParser term
       <|> parens   impl

line = whiteSpaces >> impl

instance Read Statement where
    readsPrec i = readP_to_S line

-- Input / Output

main = do
    --start <- getCPUTime
    [hypothesisPath] <- getArgs
    (header:proof) <- lines <$> readFile hypothesisPath
    let hypothesis = headerParser header
        ann = annotations hypothesis (run line <$> proof)
    handle <- openFile "output.txt" WriteMode
    hSetEncoding handle utf8
    hPutStrLn handle header
    forM_ (zip3 [1..] proof ann) $ \(i, b, a) -> do
        hPutStrLn handle $ parenthesis (show i) ++ " " ++ b ++ " " ++ parenthesis a
    hClose handle
    --finish <- getCPUTime
    --print $ (fromIntegral $ finish - start) / 1e12

run f s = case readP_to_S f s of
            [] -> error "Parse error"
            xs -> fst $ last xs

parenthesis x = "(" ++ x ++ ")"

headerParser h = run (whiteSpaces >> sepBy impl (char ',' >> whiteSpaces)) str
    where str = run (manyTill (satisfy (const True)) (string "|-")) h