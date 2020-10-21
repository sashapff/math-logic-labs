{
module Synt where
import Grammar
import Lex
}

%name synt
%tokentype { Token }
%error { parseError }

%token
  var         { MVar $$ }
  pr          { MPr $$ }
  "->"        { MImpl }
  '|'         { MOr }
  '&'         { MAnd }
  '!'         { MNot }
  '('         { MOpen }
  ')'         { MClose }
  '@'         { MForAll }
  '.'         { MPoint }
  '?'         { MExists }
  '='         { MEq }
  '+'         { MSum }
  '*'         { MMul }
  '0'         { MZero }
  kav         { MNext }

%%

Exp:
  Dis                           { $1 }
  | Dis "->" Exp                { Impl $1 $3 }

Dis:
  Con                           { $1 }
  | Dis '|' Con                 { Or $1 $3 }

Con:
  Un                            { $1 }
  | Con '&' Un                  { And $1 $3 }

Un:
  Pred                          { Expr $1 }
  | '!' Un                      { Not $2 }
  | '(' Exp ')'                 { $2 }
  | '@' Variable '.' Exp        { ForAll $2 $4 }
  | '?' Variable '.' Exp        { Exists $2 $4 }

Variable:
  var                           { Var $1 }

Pred:
  pr                            { Pred $1 }
  | Term '=' Term               { Eq $1 $3}

Term:
  Add                           { $1 }
  | Term '+' Add                { Sum $1 $3 }

Add:
  Mult                          { $1 }
  | Add '*' Mult                { Mul $1 $3 }

Mult:
  Variable                      { Term $1 }
  | '(' Term ')'                { $2 }
  | '0'                         { Zero }
  | Mult kav                    { Next $1 }


{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
