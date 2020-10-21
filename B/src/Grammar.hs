module Grammar where

data Expr = Impl Expr Expr | And Expr Expr | Or Expr Expr | Not Expr | Var String deriving (Ord, Eq)

instance Show Expr where
  show (Impl a b) = "("++(show a)++"->"++(show b)++")"
  show (And a b) = "("++(show a)++"&"++(show b)++")"
  show (Or a b) = "("++(show a)++"|"++(show b)++")"
  show (Not a) = "(!"++(show a)++")"
  show (Var a) = a
