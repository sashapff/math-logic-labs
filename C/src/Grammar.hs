module Grammar where

data Var = Var String deriving (Ord, Eq)
data Term = Sum Term Term | Mul Term Term | Next Term | Term Var | Zero deriving (Ord, Eq)
data Pred = Pred String | Eq Term Term deriving (Ord, Eq)
data Expr = Impl Expr Expr | And Expr Expr | Or Expr Expr | Not Expr | Expr Pred | ForAll Var Expr | Exists Var Expr deriving (Ord, Eq)

instance Show Var where
  show (Var a) = a

instance Show Term where
  show (Sum a b) = "("++(show a)++"+"++(show b)++")"
  show (Mul a b) = "("++(show a)++"*"++(show b)++")"
  show (Zero) = "0"
  show (Next a) = (show a)++"\'"
  show (Term a) = (show a)

instance Show Pred where
  show (Eq a b) = "("++(show a)++"="++(show b)++")"
  show (Pred a) = a

instance Show Expr where
  show (Impl a b) = "("++(show a)++"->"++(show b)++")"
  show (And a b) = "("++(show a)++"&"++(show b)++")"
  show (Or a b) = "("++(show a)++"|"++(show b)++")"
  show (Not a) = "(!"++(show a)++")"
  show (Expr a) = (show a)
  show (ForAll a b) = "(@"++(show a)++"."++(show b)++")"
  show (Exists a b) = "(?"++(show a)++"."++(show b)++")"
