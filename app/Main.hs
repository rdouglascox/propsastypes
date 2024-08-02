module Main (main) where

import Lib (parsecheckprint)

main :: IO ()
main = do
  contents <- getContents
  putStrLn (parsecheckprint contents)
