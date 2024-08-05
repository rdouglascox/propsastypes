module Main (main) where

import PropsAsTypes (parsecheckprint)

main :: IO ()
main = do
  contents <- getContents
  putStrLn (parsecheckprint contents)
