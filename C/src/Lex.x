{
module Lex where
}

%wrapper "basic"

$alpha = [a-z]
$bigAlpha = [A-Z]

tokens :-

  $white                                     ;
  \|                                         { \s -> MOr }
  \&                                         { \s -> MAnd }
  \!                                         { \s -> MNot }
  "->"                                       { \s -> MImpl }
  \(                                         { \s -> MOpen }
  \)                                         { \s -> MClose }
  $alpha                                     { \s -> MVar s }
  $bigAlpha                                  { \s -> MPr s }
  \@                                         { \s -> MForAll }
  \?                                         { \s -> MExists }
  \.                                         { \s -> MPoint }
  \+                                         { \s -> MSum }
  \*                                         { \s -> MMul }
  \=                                         { \s -> MEq }
  "0"                                        { \s -> MZero }
  \'                                         { \s -> MNext }


{
data Token = MOr | MAnd | MNot | MImpl | MOpen | MClose | MVar String | MPr String | MForAll | MExists | MPoint | MEq | MMul | MSum | MZero | MNext deriving (Eq, Show)
}
