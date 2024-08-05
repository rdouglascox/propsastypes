module TypeChecking (
  Type (..),
  Term (..),
  Context,
  Judgement,
  gettype,
  derivetype,
) where

import Church.Abs
import Church.Par
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Tree

type Context = Map.Map VarId Type

gettype :: Context -> Term -> Maybe Type
gettype ctx trm0 = case trm0 of
  (Var x1) -> gettypevar ctx x1
  (Abs x1 typ1 trm1) -> gettypeabs ctx x1 typ1 trm1
  (App trm1 trm2) -> gettypeapp ctx trm1 trm2
  (Pair trm1 trm2) -> gettypepair ctx trm1 trm2
  (Fst trm1) -> gettypefst ctx trm1
  (Snd trm1) -> gettypesnd ctx trm1
  (Inl trm1 typ1) -> gettypeinl ctx trm1 typ1
  (Inr trm1 typ1) -> gettypeinr ctx trm1 typ1
  (Case trm1 trm2 trm3) -> gettypecase ctx trm1 trm2 trm3
  (Abort trm1 typ1) -> gettypeabort ctx trm1 typ1

gettypevar :: Context -> VarId -> Maybe Type
gettypevar ctx x1 = Map.lookup x1 ctx

gettypeabs :: Context -> VarId -> Type -> Term -> Maybe Type
gettypeabs ctx x1 typ1 trm1 = case gettype (Map.insert x1 typ1 ctx) trm1 of
  (Just typ2) -> Just (Func typ1 typ2)
  _ -> Nothing

-- gettypeabs' :: Context -> VarId -> Type -> Term -> Maybe Type
-- gettypeabs' ctx x1 typ1 trm1 = Func <$> Just typ1 <*> gettype (Map.insert x1 typ1 ctx) trm1

gettypeapp :: Context -> Term -> Term -> Maybe Type
gettypeapp ctx trm1 trm2 = case (gettype ctx trm1, gettype ctx trm2) of
  (Just (Func typ1 typ2), Just typ3) -> if typ1 == typ3 then Just typ2 else Nothing
  _ -> Nothing

gettypepair :: Context -> Term -> Term -> Maybe Type
gettypepair ctx trm1 trm2 = case (gettype ctx trm1, gettype ctx trm2) of
  (Just typ1, Just typ2) -> Just (Prod typ1 typ2)
  _ -> Nothing

gettypefst :: Context -> Term -> Maybe Type
gettypefst ctx trm = case gettype ctx trm of
  (Just (Prod typ1 _)) -> Just typ1
  _ -> Nothing

gettypesnd :: Context -> Term -> Maybe Type
gettypesnd ctx trm = case gettype ctx trm of
  (Just (Prod _ typ1)) -> Just typ1
  _ -> Nothing

gettypeinl :: Context -> Term -> Type -> Maybe Type
gettypeinl ctx trm typ = case (gettype ctx trm, typ) of
  (Just typ1, Sum typ2 _) -> if typ1 == typ2 then Just typ else Nothing
  _ -> Nothing

gettypeinr :: Context -> Term -> Type -> Maybe Type
gettypeinr ctx trm typ = case (gettype ctx trm, typ) of
  (Just typ1, Sum _ typ2) -> if typ1 == typ2 then Just typ else Nothing
  _ -> Nothing

gettypecase :: Context -> Term -> Term -> Term -> Maybe Type
gettypecase ctx trm1 trm2 trm3 = case (gettype ctx trm1, gettype ctx trm2, gettype ctx trm3) of
  (Just (Sum typ1 typ2), Just (Func typ3 typ4), Just (Func typ5 typ6)) ->
    if typ1 == typ3 && typ2 == typ5 && typ4 == typ6
      then Just typ6
      else Nothing
  _ -> Nothing

gettypeabort :: Context -> Term -> Type -> Maybe Type
gettypeabort ctx trm typ = case gettype ctx trm of
  (Just Bot) -> Just typ
  _ -> Nothing

type Judgement = (Context, Term, Type)

derivetype :: Context -> Term -> Either String (Tree Judgement)
derivetype ctx trm0 = case trm0 of
  (Var x1) -> derivetypevar ctx x1
  (Abs x1 typ1 trm1) -> derivetypeabs ctx x1 typ1 trm1
  (App trm1 trm2) -> derivetypeapp ctx trm1 trm2
  (Pair trm1 trm2) -> derivetypepair ctx trm1 trm2
  (Fst trm1) -> derivetypefst ctx trm1
  (Snd trm1) -> derivetypesnd ctx trm1
  (Inl trm1 typ1) -> derivetypeinl ctx trm1 typ1
  (Inr trm1 typ1) -> derivetypeinr ctx trm1 typ1
  (Case trm1 trm2 trm3) -> derivetypecase ctx trm1 trm2 trm3
  (Abort trm1 typ1) -> derivetypeabort ctx trm1 typ1

derivetypevar :: Context -> VarId -> Either String (Tree Judgement)
derivetypevar ctx x1 = case Map.lookup x1 ctx of
  Just typ -> Right (Node (ctx, Var x1, typ) [])
  _ -> Left ("Could not find the variable " ++ show x1 ++ " in the context.")

derivetypeabs :: Context -> VarId -> Type -> Term -> Either String (Tree Judgement)
derivetypeabs ctx x1 typ1 trm1 = case derivetype (Map.insert x1 typ1 ctx) trm1 of
  Right a@(Node (_, _, typ2) _) -> Right (Node (ctx, Abs x1 typ1 trm1, Func typ1 typ2) [a])
  Left err -> Left err

derivetypeapp :: Context -> Term -> Term -> Either String (Tree Judgement)
derivetypeapp ctx trm1 trm2 = case (derivetype ctx trm1, derivetype ctx trm2) of
  (Right a@(Node (_, _, Func typ1 typ2) _), Right b@(Node (_, _, typ3) _)) ->
    if typ1 == typ3
      then Right (Node (ctx, App trm1 trm2, typ2) [a, b])
      else Left "The argument type does not match the input type in an application."
  (Left err, _) -> Left err
  (_, Left err) -> Left err
  _ -> Left "Tried to apply something other than a function to an argument."

derivetypepair :: Context -> Term -> Term -> Either String (Tree Judgement)
derivetypepair ctx trm1 trm2 = case (derivetype ctx trm1, derivetype ctx trm2) of
  (Right a@(Node (_, _, typ1) _), Right b@(Node (_, _, typ2) _)) -> Right (Node (ctx, Pair trm1 trm2, Prod typ1 typ2) [a, b])
  (Left err, _) -> Left err
  (_, Left err) -> Left err

derivetypefst :: Context -> Term -> Either String (Tree Judgement)
derivetypefst ctx trm = case derivetype ctx trm of
  Right a@(Node (_, _, Prod typ1 _) _) -> Right (Node (ctx, Fst trm, typ1) [a])
  Left err -> Left err
  _ -> Left "Tried to apply Fst to something other than a pair."

derivetypesnd :: Context -> Term -> Either String (Tree Judgement)
derivetypesnd ctx trm = case derivetype ctx trm of
  Right a@(Node (_, _, Prod _ typ1) _) -> Right (Node (ctx, Snd trm, typ1) [a])
  Left err -> Left err
  _ -> Left "Tried to apply Snd to something other than a pair."

derivetypeinl :: Context -> Term -> Type -> Either String (Tree Judgement)
derivetypeinl ctx trm typ = case (derivetype ctx trm, typ) of
  (Right a@(Node (_, _, typ1) _), Sum typ2 _) -> if typ1 == typ2 then Right (Node (ctx, Inl trm typ, typ) [a]) else Left ""
  (Left err, _) -> Left err
  _ -> Left "Inl must have a sum type."

derivetypeinr :: Context -> Term -> Type -> Either String (Tree Judgement)
derivetypeinr ctx trm typ = case (derivetype ctx trm, typ) of
  (Right a@(Node (_, _, typ1) _), Sum _ typ2) -> if typ1 == typ2 then Right (Node (ctx, Inr trm typ, typ) [a]) else Left ""
  (Left err, _) -> Left err
  _ -> Left "Inr must have a sum type."

derivetypecase :: Context -> Term -> Term -> Term -> Either String (Tree Judgement)
derivetypecase ctx trm1 trm2 trm3 = case (derivetype ctx trm1, derivetype ctx trm2, derivetype ctx trm3) of
  (Right a@(Node (_, _, Sum typ1 typ2) _), Right b@(Node (_, _, Func typ3 typ4) _), Right c@(Node (_, _, Func typ5 typ6) _)) ->
    if typ1 == typ3 && typ2 == typ5 && typ4 == typ6
      then Right (Node (ctx, Case trm1 trm2 trm3, typ6) [a, b, c])
      else Left "Type mismatch in case statement."
  (Left err, _, _) -> Left err
  (_, Left err, _) -> Left err
  (_, _, Left err) -> Left err
  _ -> Left "Terms in case statment are not of the correct types."

derivetypeabort :: Context -> Term -> Type -> Either String (Tree Judgement)
derivetypeabort ctx trm typ = case derivetype ctx trm of
  Right a@(Node (_, _, Bot) _) -> Right (Node (ctx, Abort trm typ, typ) [a])
  Left err -> Left err
  _ -> Left "Attempted to abort on something other than a term of the empty type."
