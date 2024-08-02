module Printing (
  printtype,
  printterm,
  printcontext,
  printderivation,
) where

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Tree
import ESTLC.Abs
import TypeChecking

-- printing

printtype :: Type -> String
printtype typ = case typ of
  A -> "A"
  B -> "B"
  C -> "C"
  D -> "D"
  (Prod x y) -> "(" ++ printtype x ++ "*" ++ printtype y ++ ")"
  (Sum x y) -> "(" ++ printtype x ++ "+" ++ printtype y ++ ")"
  (Func x y) -> "(" ++ printtype x ++ "->" ++ printtype y ++ ")"
  Bot -> ""

printterm :: Term -> String
printterm trm' = case trm' of
  Var (VarId x) -> x
  App trm1 trm2 -> "(" ++ printterm trm1 ++ printterm trm2 ++ ")"
  Abs (VarId x) typ trm -> "λ" ++ x ++ ":" ++ printtype typ ++ "." ++ printterm trm
  Pair trm1 trm2 -> "{" ++ printterm trm1 ++ "," ++ printterm trm2 ++ "}"
  Fst trm -> "fst " ++ printterm trm
  Snd trm -> "snd " ++ printterm trm
  Inl trm typ -> "inl " ++ printterm trm ++ " as " ++ printtype typ
  Inr trm typ -> "inr " ++ printterm trm ++ " as " ++ printtype typ
  Case trm1 trm2 trm3 -> "case " ++ printterm trm1 ++ " of " ++ printterm trm2 ++ " | " ++ printterm trm3
  Abort trm typ -> "abort " ++ printterm trm ++ " " ++ printtype typ

printcontext :: Context -> String
printcontext ctx = if Map.null ctx then "∅" else "Γ," ++ concat (List.intersperse "," (map asc (Map.toList ctx)))
 where
  asc (VarId x, y) = x ++ ":" ++ printtype y

printjudgement :: Judgement -> String
printjudgement (c, trm, typ) = printcontext c ++ " ⊢ " ++ printterm trm ++ " : " ++ printtype typ

printderivation :: Tree Judgement -> Tree String
printderivation (Node x xs) = Node (printjudgement x) (fmap printderivation xs)
