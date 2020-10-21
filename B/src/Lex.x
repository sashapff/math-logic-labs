{
module Lex where
}

%wrapper "basic"

$digit = 0-9
$alpha = [A-Z]

tokens :-

  $white                                     ;
  \|                                         { \s -> MOr }
  \&                                         { \s -> MAnd }
  \!                                         { \s -> MNot }
  "->"                                       { \s -> MImpl }
  \(                                         { \s -> MOpen }
  \)                                         { \s -> MClose }
  $alpha [$alpha $digit ']*                  { \s -> MVar s }

{
data Token = MOr | MAnd | MNot | MImpl | MOpen | MClose | MVar String  deriving (Eq, Show)
}
