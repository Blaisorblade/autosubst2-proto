module Main where

import Test.QuickCheck (generate, resize)
import GenSpec
import ParseTest

main :: IO ()
main = do
  spec <- generate $ resize 3 genSpec
  putStrLn $ show spec
  putStrLn $ untypedLambdaInput
  putStrLn $ show untypedLambdaSpec
