module Main where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lex
import Synt
import Grammar

data ExprInfo = Axiom Int (Maybe String) Int | MP Int Int Int Int | FormAxiom Int (Maybe String) Int deriving (Show)

numberAxiom :: Expr -> Maybe (String, Maybe (Var, Term))
numberAxiom expr = getNumberOfAxiom expr

numberFormAxiom :: Expr -> Maybe String
numberFormAxiom expr = getNumberOfFormAxiom expr

checkEqualsExpr :: Var -> Expr -> Expr -> Set.Set Term
checkEqualsExpr a (Impl b1 c1) (Impl b2 c2) = (Set.union (checkEqualsExpr a b1 b2) (checkEqualsExpr a c1 c2))
checkEqualsExpr a (And b1 c1) (And b2 c2) = (Set.union (checkEqualsExpr a b1 b2) (checkEqualsExpr a c1 c2))
checkEqualsExpr a (Or b1 c1) (Or b2 c2) = (Set.union (checkEqualsExpr a b1 b2) (checkEqualsExpr a c1 c2))
checkEqualsExpr a (Not b1) (Not b2) = (checkEqualsExpr a b1 b2)
checkEqualsExpr a (Expr b1) (Expr b2) = (checkEqualsPred a b1 b2)
checkEqualsExpr a (ForAll b1 c1) (ForAll b2 c2) | b1 == a && c1 == c2 && b1 == b2 = Set.empty
checkEqualsExpr a (Exists b1 c1) (Exists b2 c2) | b1 == a && c1 == c2 && b1 == b2 = Set.empty
checkEqualsExpr a (ForAll b1 c1) (ForAll b2 c2) | b1 /= a && b1 == b2 = (checkEqualsExpr a c1 c2)
checkEqualsExpr a (Exists b1 c1) (Exists b2 c2) | b1 /= a && b1 == b2 = (checkEqualsExpr a c1 c2)
checkEqualsExpr _ _ _ = (Set.insert (Term (Var "False")) Set.empty)

checkEqualsPred :: Var -> Pred -> Pred -> Set.Set Term
checkEqualsPred (Var a) (Pred b1) (Pred b2) | b1 == b2 = Set.empty
checkEqualsPred a (Eq b1 c1) (Eq b2 c2) = (Set.union (checkEqualsTerm a b1 b2) (checkEqualsTerm a c1 c2))
checkEqualsPred _ _ _ = (Set.insert (Term (Var "False")) Set.empty)

checkEqualsTerm :: Var -> Term -> Term -> Set.Set Term
checkEqualsTerm a (Sum b1 c1) (Sum b2 c2) = (Set.union (checkEqualsTerm a b1 b2) (checkEqualsTerm a c1 c2))
checkEqualsTerm a (Mul b1 c1) (Mul b2 c2) = (Set.union (checkEqualsTerm a b1 b2) (checkEqualsTerm a c1 c2))
checkEqualsTerm a (Next b1) (Next b2) = (checkEqualsTerm a b1 b2)
checkEqualsTerm a (Term b) c | b == a = (Set.insert c Set.empty)
checkEqualsTerm a (Term b) c | a /= b && (Term b) == c = Set.empty
checkEqualsTerm a (Zero) (Zero) = Set.empty
checkEqualsTerm _ _ _ = (Set.insert (Term (Var "False")) Set.empty)

freeInTerm :: Term -> Set.Set Var
freeInTerm (Sum a b) = (Set.union (freeInTerm a) (freeInTerm b))
freeInTerm (Mul a b) = (Set.union (freeInTerm a) (freeInTerm b))
freeInTerm (Next a) = (freeInTerm a)
freeInTerm (Term a) = (Set.insert a Set.empty)
freeInTerm _ = Set.empty

isFreeTerm :: Var -> Term -> Bool --  есть ли свободное входжение вар в терме

isFreeTerm a (Sum b c) = (isFreeTerm a b) || (isFreeTerm a c)
isFreeTerm a (Mul b c) = (isFreeTerm a b) || (isFreeTerm a c)
isFreeTerm a (Next b) = (isFreeTerm a b)
isFreeTerm a (Term b) = do
      if (a == b)
            then True
            else False
isFreeTerm _ _ = False

isFreePred :: Var -> Pred -> Bool
isFreePred a (Pred b) = False
isFreePred a (Eq b c) = (isFreeTerm a c) || (isFreeTerm a b)
isFreePred _ _ = False

isFree :: Var -> Expr -> Bool
isFree a (Impl b c) = (isFree a b) || (isFree a c)
isFree a (And b c) = (isFree a b) || (isFree a c)
isFree a (Or b c) = (isFree a b) || (isFree a c)
isFree a (Not b) = (isFree a b)
isFree a (Expr b) = (isFreePred a b)
isFree a (ForAll b c) = do
      if (a == b)
            then False
            else (isFree a c)
isFree a (Exists b c) = do
      if (a == b)
            then False
            else (isFree a c)
isFree _ _ = False

getNotFreeTerm :: Var -> Term -> (Bool, Set.Set Var)
getNotFreeTerm a (Sum b c) = do
      let p = (getNotFreeTerm a b)
      let q = (getNotFreeTerm a c)
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)
getNotFreeTerm a (Mul b c) = do
      let p = (getNotFreeTerm a b)
      let q = (getNotFreeTerm a c)
      let set = (Set.union (snd p) (snd q))
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)
getNotFreeTerm a (Next b) = (getNotFreeTerm a b)
getNotFreeTerm a (Term b) = do
      if (a == b)
            then (True, Set.empty)
            else (False, Set.empty)
getNotFreeTerm _ _ = (False, Set.empty)

getNotFreePred :: Var -> Pred -> (Bool, Set.Set Var)
getNotFreePred a (Pred b) = (False, Set.empty)
getNotFreePred a (Eq b c) = do
      let p = (getNotFreeTerm a b)
      let q = (getNotFreeTerm a c)
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)

getNotFree :: Var -> Expr -> (Bool, Set.Set Var)
getNotFree a (Impl b c) = do
      let p = (getNotFree a b)
      let q = (getNotFree a c)
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)
getNotFree a (And b c) = do
      let p = (getNotFree a b)
      let q = (getNotFree a c)
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)
getNotFree a (Or b c) = do
      let p = (getNotFree a b)
      let q = (getNotFree a c)
      if ((fst p) && (fst q))
        then (True, (Set.union (snd p) (snd q)))
        else if (fst p)
                then (True, (snd p))
                else if (fst q)
                        then (True, (snd q))
                        else (False, Set.empty)
getNotFree a (Not b) = (getNotFree a b)
getNotFree a (Expr b) = (getNotFreePred a b)
getNotFree a (ForAll b c) = do
      let p = getNotFree a c
      if (a == b)
            then (False, Set.empty)
            else if (fst p)
                  then (True, (Set.insert b (snd p)))
                  else (False, Set.empty)
getNotFree a (Exists b c) = do
      let p = getNotFree a c
      if (a == b)
            then (False, Set.empty)
            else if (fst p)
                  then (True, (Set.insert b (snd p)))
                  else (False, Set.empty)

checkEquals' :: Var -> Expr -> Expr -> (Bool, Maybe (Var, Term))
checkEquals' a b1 b2 = do
      let myset = (checkEqualsExpr a b1 b2)
      if ((myset) == (Set.empty))
            then (True, Nothing)
            else do
              if (((Set.size myset) /= 1) || (Set.member (Term (Var "False")) myset))
                then (False, Nothing)
                else do
                  let freeInTerm' = (freeInTerm (Set.elemAt 0 myset))
                  let notFree = (getNotFree a b1)
                  let newSet = (Set.union freeInTerm' (snd notFree))
                  if ((Set.size newSet) /= ((Set.size freeInTerm') + (Set.size (snd notFree))))
                    then (False, Just (a, (Set.elemAt 0 myset)))
                    else (True, Nothing)


getNumberOfAxiom :: Expr -> Maybe (String, Maybe (Var, Term))
getNumberOfAxiom (Impl a1 (Impl b a2)) | a1 == a2 = Just ("1", Nothing)
getNumberOfAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Impl b2 c2)) (Impl a3 c3))) | a1 == a2 && a1 == a3 && b1 == b2 && c2 == c3 = Just ("2", Nothing)
getNumberOfAxiom (Impl (And a1 b) a2) | a1 == a2 = Just ("3", Nothing)
getNumberOfAxiom (Impl (And a b1) b2) | b1 == b2 = Just ("4", Nothing)
getNumberOfAxiom (Impl a1 (Impl b1 (And a2 b2))) | a1 == a2 && b1 == b2 = Just ("5", Nothing)
getNumberOfAxiom (Impl a1 (Or a2 b)) | a1 == a2 = Just ("6", Nothing)
getNumberOfAxiom (Impl b1 (Or a b2)) | b1 == b2 = Just ("7", Nothing)
getNumberOfAxiom (Impl (Impl a1 c1) (Impl (Impl b2 c2) (Impl (Or a3 b3) c3))) | a1 == a3 && b2 == b3 && c1 == c2 && c1 == c3 = Just ("8", Nothing)
getNumberOfAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Not b2)) (Not a3))) | a1 == a2 && a1 == a3 && b1 == b2 = Just ("9", Nothing)
getNumberOfAxiom (Impl (Not (Not a1)) a2) | a1 == a2 = Just ("10", Nothing)
getNumberOfAxiom (Impl (ForAll a b1) b2) | (fst (checkEquals' a b1 b2)) = Just ("11", Nothing)
getNumberOfAxiom (Impl (ForAll a b1) b2) | (snd (checkEquals' a b1 b2)) /= Nothing = do
      let r = (snd (checkEquals' a b1 b2))
      Just ("13", r)
getNumberOfAxiom (Impl a1 (Exists b a2)) | (fst (checkEquals' b a2 a1)) = Just ("12", Nothing)
getNumberOfAxiom (Impl a1 (Exists b a2)) | (snd (checkEquals' b a2 a1)) /= Nothing = do
      let r = (snd (checkEquals' b a2 a1))
      Just ("13", r)
getNumberOfAxiom (Impl (And a1 (ForAll b (Impl a2 a3))) a4)
  | (checkEqualsExpr b a2 a1) == (Set.insert Zero Set.empty) && a2 == a4
    && (checkEqualsExpr b a2 a3) == (Set.insert ((Next (Term b))) Set.empty) = Just ("A9", Nothing)
getNumberOfAxiom _ = Nothing

getNumberOfFormAxiom :: Expr -> Maybe String
getNumberOfFormAxiom (Impl (Expr (Eq (Term (Var "a")) (Term (Var "b")))) (Impl (Expr (Eq (Term (Var "a")) (Term (Var "c")))) (Expr (Eq (Term (Var "b")) (Term (Var "c")))))) = Just "A1"
getNumberOfFormAxiom (Impl (Expr (Eq (Term (Var "a")) (Term (Var "b")))) (Expr (Eq (Next (Term (Var "a"))) (Next (Term (Var "b")))))) = Just "A2"
getNumberOfFormAxiom (Impl (Expr (Eq (Next (Term (Var "a"))) (Next (Term (Var "b"))))) (Expr (Eq (Term (Var "a")) (Term (Var "b"))))) = Just "A3"
getNumberOfFormAxiom (Not (Expr (Eq (Next (Term (Var "a"))) Zero))) = Just "A4"
getNumberOfFormAxiom (Expr (Eq (Sum (Term (Var "a")) Zero) (Term (Var "a")))) = Just "A5"
getNumberOfFormAxiom (Expr (Eq (Sum (Term (Var "a")) (Next (Term (Var "b")))) (Next (Sum (Term (Var "a")) (Term (Var "b")))))) = Just "A6"
getNumberOfFormAxiom (Expr (Eq (Mul (Term (Var "a")) Zero) Zero)) = Just "A7"
getNumberOfFormAxiom (Expr (Eq (Mul (Term (Var "a")) (Next (Term (Var "b")))) (Sum (Mul (Term (Var "a")) (Term (Var "b"))) (Term (Var "a"))))) = Just "A8"
getNumberOfFormAxiom _ = Nothing

getIndex :: ExprInfo -> Int
getIndex (Axiom a _ _) = a
getIndex (MP a _ _ _) = a
getIndex (FormAxiom a _ _) = a

modPon :: Expr -> [(Expr, Int)] -> Int
modPon (Impl e1 e2) ((right, num):other) = do
      if (e2 == right)
            then num
            else 0
modPon _ _ = 0

getInd :: Expr -> Map.Map Expr Int -> Maybe Int
getInd e good = (Map.lookup e good)

getMax :: [Expr] -> Maybe (Int, Int) -> Map.Map Expr Int -> Expr -> Maybe (Int, Int)
getMax [] a _ _ = a
getMax (a:as) (Just (b,c)) good right = do
      let ind = (getInd a good)
      if (ind /= Nothing && (getN ind) > b && (Map.member (Impl a right) good))
          then (getMax as (Just (getN ind, (good Map.! (Impl a right)))) good right)
          else (getMax as (Just (b, c)) good right)
getMax (a:as) Nothing good right = do
      let ind = (getInd a good)
      if (ind /= Nothing && (Map.member (Impl a right) good))
          then (getMax as (Just (getN ind, (good Map.! (Impl a right)))) good right)
          else (getMax as Nothing good right)

modesPonens :: Maybe [Expr] -> Map.Map Expr Int -> Expr -> Maybe (Int, Int)
modesPonens Nothing _ _ = Nothing
modesPonens (Just []) _ _ = Nothing
modesPonens (Just t) good right = (getMax t Nothing good right)
modesPonens _ _ _ = Nothing

isImpl :: Expr -> Bool
isImpl (Impl a b) = True
isImpl _ = False

getVar :: Maybe (Var, Term) -> Var
getVar (Just (a,b)) = a

getTerm :: Maybe (Var, Term) -> Term
getTerm (Just (a,b)) = b

getN :: Maybe (Int) -> Int
getN (Just a) = a

get :: Maybe a -> a
get (Just a) = a

getString :: Maybe (String, Maybe (Var, Term)) -> Maybe String
getString(Just (a,b)) = (Just a)

getMaybeVarTerm :: Maybe (String, Maybe (Var, Term)) -> Maybe (Var, Term)
getMaybeVarTerm (Just (a,b)) = b

getRightImpl :: Maybe (Int, Int) -> Int
getRightImpl (Just (a,b)) = b

getLeftImpl :: Maybe (Int, Int) -> Int
getLeftImpl (Just (a,b)) = a

getAll :: Expr -> Maybe (Var, (Expr, Expr))
getAll (Impl a (ForAll b c)) = Just (b, (a, c))
getAll _ = Nothing

getAny :: Expr -> Maybe (Var, (Expr, Expr))
getAny (Impl (Exists a b) c) = Just (a, (b, c))
getAny _ = Nothing

getLI :: Maybe (Var, (Expr, Expr)) -> Expr
getLI (Just (_, (a, b))) = a

getRI :: Maybe (Var, (Expr, Expr)) -> Expr
getRI (Just (_, (a, b))) = b

getX :: Maybe (Var, (Expr, Expr)) -> Var
getX (Just (a, _)) = a

isJust :: Maybe (Int) -> Bool
isJust (Just _) = True
isJust _ = False

getCorrectStatements :: Expr -> [Expr] -> Map.Map Expr [Expr] -> Int -> Expr -> Map.Map (Expr, Expr) Int -> Map.Map Expr Int -> IO ()
getCorrectStatements _ [] _ _ last _ _ = (putStr "")
getCorrectStatements stat (a:as) rightParts num last impl good = do
      let numAxiom = numberAxiom a
      let numAx = (getString numAxiom)
      let numAxMB = (getMaybeVarTerm numAxiom)
      let numFormAx = numberFormAxiom a
      let mp = modesPonens (Map.lookup a rightParts) good a
      let newRightParts = if (isImpl a) then (let (Impl l r) = a in (Map.insertWith (++) r [l] rightParts)) else rightParts
      let newImpl = if (isImpl a) then (let (Impl l r) = a in (Map.insert (l, r) num impl)) else impl
      let newGood = (Map.insert a num good)
      if (numAxiom /= Nothing)
          then do
                if (numAx == (Just "13"))
                      then do
                          (putStrLn ("Expression "++(show (num))++": variable "++(show (getVar numAxMB))++" is not free for term "++(show (getTerm numAxMB))++" in ?@-axiom."))
                      else do
                          (putStrLn ("["++(show (num))++". Ax. sch. "++( (fromJust numAx))++"] "++(show a)))
                          (getCorrectStatements stat as newRightParts (num + 1) last newImpl newGood)
                          if (as == [] && a /= last)
                                then (putStrLn "The proof proves different expression.")
                                else (putStr "")
          else if (numFormAx /= Nothing)
                then do
                      (putStrLn ("["++(show (num))++". Ax. "++( (fromJust numFormAx))++"] "++(show a)))
                      (getCorrectStatements stat as newRightParts (num + 1) last newImpl newGood)
                      if (as == [] && a /= last)
                            then (putStrLn "The proof proves different expression.")
                            else (putStr "")
                else if (mp /= Nothing)
                      then do
                            (putStrLn ("["++(show (num))++". M.P. "++(show (getLeftImpl mp))++", "++(show (getRightImpl mp))++"] "++(show a)))
                            (getCorrectStatements stat as newRightParts (num + 1) last newImpl newGood)
                            if (as == [] && a /= last)
                                  then (putStrLn "The proof proves different expression.")
                                  else (putStr "")
                      else do
                          let any = (getAny a)
                          if (any /= Nothing && (isJust (Map.lookup ((getLI any), (getRI any)) impl)))
                            then do
                                let isFree' = ((isFree (getX any) (getRI any))) -- другой нотфри
                                if (isFree' == False) -- изи иф
                                      then do
                                            (putStrLn ("["++(show num)++". ?@-intro "++(show (getN (Map.lookup ((getLI any), (getRI any)) impl)))++"] "++(show a)))
                                            (getCorrectStatements stat as  newRightParts (num + 1) last newImpl newGood)
                                            if (as == [] && a /= last)
                                                  then (putStrLn "The proof proves different expression.")
                                                  else (putStr "")
                                      else do
                                            (putStrLn ("Expression "++(show num)++": variable "++(show(getX any))++" occurs free in ?@-rule."))
                            else do
                                  let all = (getAll a)
                                  if (all /= Nothing && (isJust (Map.lookup ((getLI all), (getRI all)) impl)))
                                        then do
                                              let isFree' = ((isFree (getX all) (getLI all))) -- другой нотфри
                                              if (isFree' == False) -- изи иф
                                                    then do
                                                          (putStrLn ("["++(show num)++". ?@-intro "++(show (getN (Map.lookup ((getLI all), (getRI all)) impl)))++"] "++(show a)))
                                                          (getCorrectStatements stat as  newRightParts (num + 1) last newImpl newGood)
                                                          if (as == [] && a /= last)
                                                                then (putStrLn "The proof proves different expression.")
                                                                else (putStr "")
                                                    else do
                                                          (putStrLn ("Expression "++(show num)++": variable "++(show(getX all))++" occurs free in ?@-rule."))

                                    else do
                                                    (putStrLn ("Expression "++(show (num))++" is not proved."))


toExpr :: String -> Expr
toExpr = synt . alexScanTokens

fromJust :: (Maybe String) -> String
fromJust (Just a) = a

printExpr :: Expr -> IO ()
printExpr x = do
    putStrLn ("|-"++(show x))


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

main :: IO ()
main = do
  statement <- getLine
  contents <- getContents
  let splitedStatement = splitStatement statement
  let stat = toExpr (snd splitedStatement) -- что выводим
  printExpr stat
  let lins = lines contents
  let props = map toExpr lins -- выражения которыми выводим
  getCorrectStatements stat props Map.empty 1 stat Map.empty Map.empty
