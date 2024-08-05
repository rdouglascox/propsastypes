-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Church.Par
  ( happyError
  , myLexer
  , pTerm
  , pType
  ) where

import Prelude

import qualified Church.Abs
import Church.Lex

}

%name pTerm Term
%name pType Type
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '('     { PT _ (TS _ 1)     }
  ')'     { PT _ (TS _ 2)     }
  '*'     { PT _ (TS _ 3)     }
  '+'     { PT _ (TS _ 4)     }
  ','     { PT _ (TS _ 5)     }
  '->'    { PT _ (TS _ 6)     }
  '.'     { PT _ (TS _ 7)     }
  ':'     { PT _ (TS _ 8)     }
  'A'     { PT _ (TS _ 9)     }
  'B'     { PT _ (TS _ 10)    }
  'Bot'   { PT _ (TS _ 11)    }
  'C'     { PT _ (TS _ 12)    }
  'D'     { PT _ (TS _ 13)    }
  '\\'    { PT _ (TS _ 14)    }
  'abort' { PT _ (TS _ 15)    }
  'as'    { PT _ (TS _ 16)    }
  'case'  { PT _ (TS _ 17)    }
  'fst'   { PT _ (TS _ 18)    }
  'inl'   { PT _ (TS _ 19)    }
  'inr'   { PT _ (TS _ 20)    }
  'of'    { PT _ (TS _ 21)    }
  'snd'   { PT _ (TS _ 22)    }
  '{'     { PT _ (TS _ 23)    }
  '|'     { PT _ (TS _ 24)    }
  '}'     { PT _ (TS _ 25)    }
  L_VarId { PT _ (T_VarId $$) }

%%

VarId :: { Church.Abs.VarId }
VarId  : L_VarId { Church.Abs.VarId $1 }

Term :: { Church.Abs.Term }
Term
  : '(' Term ')' { $2 }
  | VarId { Church.Abs.Var $1 }
  | '(' Term Term ')' { Church.Abs.App $2 $3 }
  | '\\' VarId ':' Type '.' Term { Church.Abs.Abs $2 $4 $6 }
  | '{' Term ',' Term '}' { Church.Abs.Pair $2 $4 }
  | 'fst' Term { Church.Abs.Fst $2 }
  | 'snd' Term { Church.Abs.Snd $2 }
  | 'inl' Term 'as' Type { Church.Abs.Inl $2 $4 }
  | 'inr' Term 'as' Type { Church.Abs.Inr $2 $4 }
  | 'case' Term 'of' Term '|' Term { Church.Abs.Case $2 $4 $6 }
  | 'abort' Term Type { Church.Abs.Abort $2 $3 }

Type :: { Church.Abs.Type }
Type
  : 'A' { Church.Abs.A }
  | 'B' { Church.Abs.B }
  | 'C' { Church.Abs.C }
  | 'D' { Church.Abs.D }
  | 'Bot' { Church.Abs.Bot }
  | '(' Type '->' Type ')' { Church.Abs.Func $2 $4 }
  | '(' Type '+' Type ')' { Church.Abs.Sum $2 $4 }
  | '(' Type '*' Type ')' { Church.Abs.Prod $2 $4 }

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

