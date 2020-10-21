module Main where

import Lex
import Synt

main :: IO ()
main = do
  expr <- getLine
  putStrLn $ show (synt (alexScanTokens expr))
