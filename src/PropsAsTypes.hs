module PropsAsTypes (
  parsecheckprint,
) where

import Church.Par
import qualified Data.Map as Map
import Data.Tree
import Printing
import TypeChecking

parsecheckprint :: String -> String
parsecheckprint x = case (pTerm . myLexer) x of
  Left y -> y
  Right y -> case derivetype Map.empty y of
    Left z -> z
    Right z -> drawTree (printderivation z)
