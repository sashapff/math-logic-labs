module Main where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lex
import Synt
import Grammar

data ExprInfo = Axiom Int (Maybe Int) Int | Hypotes Int Int Int | MP Int Int Int Int deriving (Show)

getIndex :: ExprInfo -> Int
getIndex (Axiom a _ _) = a
getIndex (Hypotes a _ _) = a
getIndex (MP a _ _ _) = a

getNormIndex :: ExprInfo -> Int
getNormIndex (Axiom _ _ a) = a
getNormIndex (Hypotes _ _ a) = a
getNormIndex (MP _ _ _ a) = a

setIndex :: Int -> ExprInfo -> ExprInfo
setIndex new (Axiom a b c) = (Axiom a b new)
setIndex new (Hypotes a b c) = (Hypotes a b new)
setIndex new (MP a b c d) = (MP a b c new)

splitStatement :: String -> (String, String)
splitStatement [] = ([],[])
splitStatement s = f s [] [] False where
  f :: String -> String -> String -> Bool -> (String, String)
  f [] xs ys _ = (xs, ys)
  f [a] xs ys _ = (xs, reverse (a:(reverse ys)))
  f (a:b:abs) xs ys flag =
    if a == '|' && b == '-'
    then f abs xs ys True
    else
      if flag
      then f abs xs (reverse (b:a:(reverse ys))) flag
      else f (b:abs) (reverse (a:(reverse xs))) ys flag

splitHypotes :: String -> (Map.Map Expr Int)
splitHypotes [] = Map.empty
splitHypotes s = f s [] Map.empty 1 where
  f :: String -> String -> (Map.Map Expr Int) -> Int -> (Map.Map Expr Int)
  f [] xs ys i = (Map.insert (toExpr xs) i ys)
  f (a:as) xs ys i =
    if a == ','
    then f as [] (Map.insert (toExpr xs) i ys) (i+1)
    else f as (reverse(a:(reverse xs))) ys i

toExpr :: String -> Expr
toExpr = synt . alexScanTokens

numberAxiom :: Expr -> Maybe Int
numberAxiom expr = getNumberOfAxiom expr

getNumberOfAxiom :: Expr -> Maybe Int
getNumberOfAxiom (Impl a1 (Impl b a2)) | a1 == a2 = Just 1
getNumberOfAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Impl b2 c2)) (Impl a3 c3))) | a1 == a2 && a1 == a3 && b1 == b2 && c2 == c3 = Just 2
getNumberOfAxiom (Impl (And a1 b) a2) | a1 == a2 = Just 4
getNumberOfAxiom (Impl (And a b1) b2) | b1 == b2 = Just 5
getNumberOfAxiom (Impl a1 (Impl b1 (And a2 b2))) | a1 == a2 && b1 == b2 = Just 3
getNumberOfAxiom (Impl a1 (Or a2 b)) | a1 == a2 = Just 6
getNumberOfAxiom (Impl b1 (Or a b2)) | b1 == b2 = Just 7
getNumberOfAxiom (Impl (Impl a1 c1) (Impl (Impl b2 c2) (Impl (Or a3 b3) c3))) | a1 == a3 && b2 == b3 && c1 == c2 && c1 == c3 = Just 8
getNumberOfAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Not b2)) (Not a3))) | a1 == a2 && a1 == a3 && b1 == b2 = Just 9
getNumberOfAxiom (Impl (Not (Not a1)) a2) | a1 == a2 = Just 10
getNumberOfAxiom _ = Nothing

modesPonens :: Maybe [(Expr, Int)] -> Map.Map Expr ExprInfo -> Maybe (Int, Int)
modesPonens Nothing _ = Nothing
modesPonens (Just []) _ = Nothing
modesPonens (Just ((r, index) : rs)) good = let (Impl a b) = r in
  if a `Map.member` good
      then Just (index, getIndex $! (good Map.! a))
      else modesPonens (Just rs) good

isImpl :: Expr -> Bool
isImpl (Impl a b) = True
isImpl _ = False

getRightImpl :: Maybe (Int, Int) -> Int
getRightImpl (Just (a,b)) = a

getLeftImpl :: Maybe (Int, Int) -> Int
getLeftImpl (Just (a,b)) = b

cmp :: (Expr, ExprInfo) -> (Expr, ExprInfo) -> Ordering
cmp (_, e1) (_, e2) = do
  let i1 = getIndex e1
  let i2 = getIndex e2
  if i1 == i2
      then EQ
      else if i1 > i2
            then LT
            else GT

rev ::  [(Expr, ExprInfo)] -> Map.Map Int (Expr, ExprInfo) -> Map.Map Int (Expr, ExprInfo)
rev [] acc = acc
rev ((expr, exprInfo):as) acc = do
    rev as (Map.insert (getIndex exprInfo) (expr, exprInfo) acc)

isMP :: (Expr, ExprInfo) -> Bool
isMP (_, (MP _ _ _ _)) = True
isMP _ = False

isAx :: (Expr, ExprInfo) -> Bool
isAx (_, (Axiom _ _ _)) = True
isAx _ = False

makeDependency :: Map.Map Int (Expr, ExprInfo) -> [(Expr, ExprInfo)] -> Set.Set Int -> [(Expr, ExprInfo)] -> [(Expr, ExprInfo)]
makeDependency _ [] _ acc = acc
makeDependency indexes ((expr, (MP a b c d)):as) queue acc = do
    let index = a
    if (index `Set.member` queue)
        then makeDependency indexes as (Set.delete index $ Set.insert b $ Set.insert c queue) ((expr, (MP a b c d)):acc)
        else makeDependency indexes as queue acc
makeDependency indexes ((expr, exprInfo):as) queue acc = do
    let index = (getIndex exprInfo)
    if (index `Set.member` queue)
        then makeDependency indexes as (Set.delete index queue) ((expr, exprInfo):acc)
        else makeDependency indexes as queue acc

numberDependency :: Int -> [(Expr, ExprInfo)] -> [(Expr, ExprInfo)] -> [(Expr, ExprInfo)]
numberDependency _ [] acc = acc
numberDependency num ((expr, exprInfo):as) acc = numberDependency (num + 1) as (reverse ((expr, (setIndex num exprInfo)):(reverse acc)))

getInt :: Maybe Int -> Int
getInt (Just a) = a

getVal :: Maybe (Expr, ExprInfo) -> (Expr, ExprInfo)
getVal (Just a) = a

getInfo :: Maybe (Expr, ExprInfo) -> ExprInfo
getInfo (Just (e,i)) = i

printInfo :: Map.Map Int (Expr, ExprInfo) -> ExprInfo -> String
printInfo _ (Axiom _ b a) = "[" ++ show a ++ ". Ax. sch. " ++ (show $ getInt b) ++ "] "
printInfo _ (Hypotes _ b a) = "[" ++ show a ++ ". Hypothesis " ++ show b ++ "] "
printInfo indexes (MP _ b c a) = "[" ++ show a ++ ". M.P. " ++ show (getNormIndex $ getInfo (Map.lookup b indexes)) ++ ", " ++ show (getNormIndex $ getInfo (Map.lookup c indexes)) ++ "] "

printResult :: Map.Map Int (Expr, ExprInfo) -> [(Expr, ExprInfo)] -> IO ()
printResult _ [] = putStr ""
printResult indexes ((expr, exprInfo) : es) = do
      putStrLn (printInfo indexes exprInfo ++ show expr)
      printResult indexes es

getCorrectStatements :: Expr -> (Map.Map Expr Int) -> [Expr] -> Map.Map Expr ExprInfo -> Map.Map Expr [(Expr, Int)] -> Int -> Expr -> ((Map.Map Expr ExprInfo), Expr)
getCorrectStatements _ _ [] good _ _ last = (good, last)
getCorrectStatements stat hypos (a:as) good rightParts num last = do
  let numAx = numberAxiom a
  let mp = modesPonens (Map.lookup a rightParts) good
  let newRightParts = if (isImpl a) then (let (Impl l r) = a in (Map.insertWith (++) r [(a, num)] rightParts)) else rightParts
  if (a `Map.member` good)
      then getCorrectStatements stat hypos as good rightParts (num + 1) a
      else if (numAx /= Nothing)
          then getCorrectStatements stat hypos as (Map.insert a (Axiom num numAx 0) good) newRightParts (num + 1) a
          else if (a `Map.member` hypos)
              then getCorrectStatements stat hypos as (Map.insert a (Hypotes num (hypos Map.! a) 0) good) newRightParts (num + 1) a
              else if (mp /= Nothing)
                  then getCorrectStatements stat hypos as (Map.insert a (MP num (getRightImpl mp) (getLeftImpl mp) 0) good) newRightParts (num + 1) a
                  else (Map.empty, a)

main :: IO ()
main = do
  statement <- getLine
  contents <- getContents
  let splitedStatement = splitStatement statement
  let hypotes = splitHypotes (fst splitedStatement) -- гипотезы
  let stat = toExpr (snd splitedStatement) -- что выводим
  let lins = lines contents
  let props = map toExpr lins -- выражения которыми выводим
  let (deduction, last) = getCorrectStatements stat hypotes props Map.empty Map.empty 1 (Var "")
  if (last /= stat)
      then putStrLn "Proof is incorrect"
      else do
          let results = dropWhile (\(e,i) -> e /= stat) $ List.sortBy cmp (Map.toList $! deduction)
          if (null results)
              then putStrLn "Proof is incorrect"
              else do
                  let indexToExpr = rev results Map.empty
                  let (expr, exprInfo) = head results
                  let dependencies = makeDependency indexToExpr results (Set.fromList [(getIndex exprInfo)]) []
                  let numberedDependencies = numberDependency 1 dependencies []
                  let indexToExpr' = rev numberedDependencies Map.empty
                  putStrLn statement
                  printResult indexToExpr' numberedDependencies
