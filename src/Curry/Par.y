-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Curry.Par
  ( happyError
  , myLexer
  , pTerm
  ) where

import Prelude

import qualified Curry.Abs
import Curry.Lex

}

%name pTerm Term
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '('        { PT _ (TS _ 1)        }
  ')'        { PT _ (TS _ 2)        }
  ','        { PT _ (TS _ 3)        }
  '.'        { PT _ (TS _ 4)        }
  '\\'       { PT _ (TS _ 5)        }
  'abort'    { PT _ (TS _ 6)        }
  'case'     { PT _ (TS _ 7)        }
  'false'    { PT _ (TS _ 8)        }
  'fst'      { PT _ (TS _ 9)        }
  'inl'      { PT _ (TS _ 10)       }
  'inr'      { PT _ (TS _ 11)       }
  'of'       { PT _ (TS _ 12)       }
  'snd'      { PT _ (TS _ 13)       }
  'true'     { PT _ (TS _ 14)       }
  '{'        { PT _ (TS _ 15)       }
  '|'        { PT _ (TS _ 16)       }
  '}'        { PT _ (TS _ 17)       }
  L_Variable { PT _ (T_Variable $$) }

%%

Variable :: { Curry.Abs.Variable }
Variable  : L_Variable { Curry.Abs.Variable $1 }

Term :: { Curry.Abs.Term }
Term
  : Variable { Curry.Abs.Var $1 }
  | '(' Term Term ')' { Curry.Abs.App $2 $3 }
  | '\\' Variable '.' Term { Curry.Abs.Abs $2 $4 }
  | '{' Term ',' Term '}' { Curry.Abs.Pair $2 $4 }
  | 'fst' Term { Curry.Abs.Fst $2 }
  | 'snd' Term { Curry.Abs.Snd $2 }
  | 'inl' Term { Curry.Abs.Inl $2 }
  | 'inr' Term { Curry.Abs.Inr $2 }
  | 'case' Term 'of' Term '|' Term { Curry.Abs.Case $2 $4 $6 }
  | 'abort' Term { Curry.Abs.Abrt $2 }
  | 'true' { Curry.Abs.T }
  | 'false' { Curry.Abs.F }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

}

