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
  "->"        { MImpl }
  '|'         { MOr }
  '&'       { MAnd }
  '!'         { MNot }
  '('         { MOpen }
  ')'         { MClose }

%%

Exp:
  Dis                           { $1 }
  | Dis "->" Exp                { Impl $1 $3 }

Dis:
  Con                           { $1 }
  | Dis '|' Con                 { Or $1 $3 }

Con:
  Neg                           { $1 }
  | Con '&' Neg                 { And $1 $3 }

Neg:
  '!' Neg                       { Not $2 }
  | Variable                    { $1 }
  | '(' Exp ')'                 { $2 }

Variable:
  var                           { Var $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
