module TypeInference where

import Control.Monad.State
import Curry.Abs
import Curry.Par
import Data.Char
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | our types
data Type
  = TypeVar Int
  | A
  | B
  | C
  | D
  | Func Type Type
  | Prod Type Type
  | Sum Type Type
  | Bot
  | Bool
  deriving (Show, Ord, Eq)

-- | check if a type is a typevariable
isTypeVar :: Type -> Bool
isTypeVar (TypeVar _) = True
isTypeVar _ = False

-- | data type for contexts
type Context = Map.Map Term Type

-- | data type for constraints
data Constraint = Constraint Type Type
  deriving (Show, Ord, Eq)

-- | data type for constraint sets
type ConstraintSet = Set.Set Constraint

-- | get free type variables in a type
fv :: Type -> Set.Set Type
fv (TypeVar v) = Set.singleton (TypeVar v)
fv (Func x y) = Set.union (fv x) (fv y)
fv _ = Set.empty

-- | get a new type variable
newtypevar :: State Type Type
newtypevar = do
  n <- get
  put (inctypevar n)
  return n

-- | increment the index of a type variable
inctypevar :: Type -> Type
inctypevar (TypeVar x) = (TypeVar (x + 1))
inctypevar x = x

-- | a function for deriving a constraint set, now in the state monad
derive :: Context -> Term -> State Type (Type, ConstraintSet)
derive ctx (Var x) = case Map.lookup (Var x) ctx of
  Just typ -> return (typ, Set.empty)
  Nothing -> error "uh oh, this should never happen"
derive ctx (App trm1 trm2) = do
  newvar <- newtypevar
  (ftype, fcons) <- derive ctx trm1 -- the type and constraints of the function
  (atype, acons) <- derive ctx trm2 -- the type and constraints of the argument
  let newconstraints = Set.unions [fcons, acons, Set.singleton (Constraint ftype (Func atype newvar))]
  return (newvar, newconstraints)
derive ctx (Abs var trm1) = do
  newvar <- newtypevar
  let newctx = Map.insert (Var var) newvar ctx
  (ntype, ncons) <- derive newctx trm1
  return (Func newvar ntype, ncons)
derive ctx (Pair trm1 trm2) = do
  (ntyp1, ncs1) <- derive ctx trm1
  (ntyp2, ncs2) <- derive ctx trm2
  let newconstraints = Set.unions [ncs1, ncs2]
  return (Prod ntyp1 ntyp2, newconstraints)
derive ctx (Fst trm) = do
  newvar1 <- newtypevar
  newvar2 <- newtypevar
  (ntype, ncs) <- derive ctx trm
  let newconstraints = Set.unions [ncs, Set.singleton (Constraint ntype (Prod newvar1 newvar2))]
  return (newvar1, newconstraints)
derive ctx (Snd trm) = do
  newvar1 <- newtypevar
  newvar2 <- newtypevar
  (ntype, ncs) <- derive ctx trm
  let newconstraints = Set.unions [ncs, Set.singleton (Constraint ntype (Prod newvar1 newvar2))]
  return (newvar2, newconstraints)
derive ctx (Inl trm) = do
  newvar1 <- newtypevar
  newvar2 <- newtypevar
  (ntype, ncs) <- derive ctx trm
  let newconstraints = Set.unions [ncs, Set.singleton (Constraint newvar1 (Sum ntype newvar2))]
  return (newvar1, newconstraints)
derive ctx (Inr trm) = do
  newvar1 <- newtypevar
  newvar2 <- newtypevar
  (ntype, ncs) <- derive ctx trm
  let newconstraints = Set.unions [ncs, Set.singleton (Constraint newvar1 (Sum newvar2 ntype))]
  return (newvar1, newconstraints)
derive ctx (Case trm1 trm2 trm3) = do
  newvar1 <- newtypevar
  newvar2 <- newtypevar
  newvar3 <- newtypevar
  (ntype1, ncs1) <- derive ctx trm1
  (ntype2, ncs2) <- derive ctx trm2
  (ntype3, ncs3) <- derive ctx trm3
  let newconstraints = Set.unions [ncs1, ncs2, ncs3, Set.singleton (Constraint ntype1 (Sum newvar1 newvar2)), Set.singleton (Constraint ntype2 (Func newvar1 newvar3)), Set.singleton (Constraint ntype3 (Func newvar2 newvar3))]
  return (newvar3, newconstraints)
derive ctx (Abrt trm) = do
  newvar1 <- newtypevar
  (ntype, ncs) <- derive ctx trm
  let newconstraints = Set.unions [ncs, Set.singleton (Constraint ntype Bot)]
  return (newvar1, newconstraints)
derive _ T = do return (Bool, Set.empty)
derive _ F = do return (Bool, Set.empty)

-- | run constraint generator on the empty context
runderive :: Term -> (Type, ConstraintSet)
runderive t = evalState (derive Map.empty t) (TypeVar 1)

-- | a type for our substitution map
type SubstitutionMap = Map.Map Type Type

-- | apply our map to types
applysubstotypes :: SubstitutionMap -> Type -> Type
applysubstotypes sm (TypeVar x) = case Map.lookup (TypeVar x) sm of
  Just typ -> typ
  Nothing -> (TypeVar x) -- "if X not in the domain of the map"
applysubstotypes sm (Func typ1 typ2) = Func (applysubstotypes sm typ1) (applysubstotypes sm typ2)
applysubstotypes sm (Prod typ1 typ2) = Prod (applysubstotypes sm typ1) (applysubstotypes sm typ2)
applysubstotypes sm (Sum typ1 typ2) = Sum (applysubstotypes sm typ1) (applysubstotypes sm typ2)
applysubstotypes _ x = x

-- | apply our map to a constraint
applysubstocon :: SubstitutionMap -> Constraint -> Constraint
applysubstocon sm (Constraint x y) = Constraint (applysubstotypes sm x) (applysubstotypes sm y)

-- | apply our sub map to a constraint set
applysubstocons :: SubstitutionMap -> ConstraintSet -> ConstraintSet
applysubstocons sm cs = Set.map (applysubstocon sm) cs

-- | map composition
mapcomp :: SubstitutionMap -> SubstitutionMap -> SubstitutionMap
mapcomp x y =
  let firstbit = Map.map (applysubstotypes x) y
      keys = Map.keys y
      secondbit = Map.filterWithKey (\z _ -> z `notElem` keys) x
   in Map.union firstbit secondbit

-- now the unification function
unify :: ConstraintSet -> SubstitutionMap
unify cs =
  if Set.null cs
    then Map.empty
    else
      let (Constraint t1 t2) = Set.elemAt 0 cs -- get a constraint from constraint set
          cs' = Set.drop 1 cs -- call the rest of the set cs'
       in if t1 == t2 -- if the types are syntactically identical, unify the rest, cs'
            then
              unify cs' -- returns a substitution map
            else
              if isTypeVar t1 && Set.notMember t1 (fv t2) -- if the first type is a type-variable and not free in the second type, then
                then
                  let sm = Map.singleton t1 t2
                   in mapcomp (unify (applysubstocons sm cs')) sm
                else
                  if isTypeVar t2 && Set.notMember t2 (fv t1)
                    then
                      let sm = Map.singleton t2 t1
                       in mapcomp (unify (applysubstocons sm cs')) sm
                    else case (t1, t2) of
                      (Func t1a t1b, Func t2a t2b) -> unify (Set.unions [cs', Set.singleton (Constraint t1a t2a), Set.singleton (Constraint t1b t2b)])
                      (Prod t1a t1b, Prod t2a t2b) -> unify (Set.unions [cs', Set.singleton (Constraint t1a t2a), Set.singleton (Constraint t1b t2b)])
                      (Sum t1a t1b, Sum t2a t2b) -> unify (Set.unions [cs', Set.singleton (Constraint t1a t2a), Set.singleton (Constraint t1b t2b)])
                      _ -> error "Could not unify constraint set."

infertype :: Term -> (Type, ConstraintSet, SubstitutionMap, Type)
infertype x =
  let (typ, cons) = runderive x
      sm = unify cons
   in (typ, cons, sm, applysubstotypes sm typ)

normalisetype :: Type -> Type
normalisetype t =
  let varindexes = List.nub $ getvarindexes t
      zipped = zip varindexes [1 ..]
      mymap = Map.fromList zipped
   in updatevarindexes mymap t

updatevarindexes :: (Map.Map Int Int) -> Type -> Type
updatevarindexes m (Func t1 t2) = Func (updatevarindexes m t1) (updatevarindexes m t2)
updatevarindexes m (Sum t1 t2) = Sum (updatevarindexes m t1) (updatevarindexes m t2)
updatevarindexes m (Prod t1 t2) = Prod (updatevarindexes m t1) (updatevarindexes m t2)
updatevarindexes m (TypeVar x) = case Map.lookup x m of
  Just y -> TypeVar y
  Nothing -> TypeVar x
updatevarindexes _ x = x

getvarindexes :: Type -> [Int]
getvarindexes (Func t1 t2) = getvarindexes t1 ++ getvarindexes t2
getvarindexes (Sum t1 t2) = getvarindexes t1 ++ getvarindexes t2
getvarindexes (Prod t1 t2) = getvarindexes t1 ++ getvarindexes t2
getvarindexes (TypeVar x) = [x]
getvarindexes _ = []

-- | printing functions
printterm :: Term -> String
printterm (Var (Variable x)) = x
printterm (App x y) = "(" ++ printterm x ++ " " ++ printterm y ++ ")"
printterm (Abs (Variable x) y) = "λ" ++ x ++ "." ++ printterm y
printterm (Pair x y) = "{" ++ printterm x ++ "," ++ printterm y ++ "}"
printterm (Fst x) = "fst " ++ printterm x
printterm (Snd x) = "snd " ++ printterm x
printterm (Inl x) = "inl " ++ printterm x
printterm (Inr x) = "inr " ++ printterm x
printterm (Case x y z) = "case " ++ printterm x ++ " of " ++ printterm y ++ " | " ++ printterm z
printterm (Abrt x) = "abort " ++ printterm x
printterm T = "true"
printterm F = "false"

printtype :: Type -> String
printtype (Func x y) = "(" ++ printtype x ++ "→" ++ printtype y ++ ")"
printtype (Prod x y) = "(" ++ printtype x ++ "x" ++ printtype y ++ ")"
printtype (Sum x y) = "(" ++ printtype x ++ "+" ++ printtype y ++ ")"
printtype A = "A"
printtype B = "B"
printtype C = "C"
printtype D = "D"
printtype (TypeVar x) = [chr (96 + x)]
printtype Bot = "⊥"
printtype Bool = "Bool"

printtype' :: Type -> String
printtype' x = printtype $ normalisetype x

printconstraintset :: ConstraintSet -> String
printconstraintset cs =
  let xs = Set.toList cs
   in concat $ List.intersperse "," $ map printconstraint xs

printconstraint :: Constraint -> String
printconstraint (Constraint x y) = printtype x ++ "≡" ++ printtype y

printsubstitutionmap :: SubstitutionMap -> String
printsubstitutionmap sm =
  let xs = Map.toList sm
   in "σ : " ++ (concat $ List.intersperse "," $ map printsubsitution xs)

printsubsitution :: (Type, Type) -> String
printsubsitution (x, y) = printtype x ++ "⇒" ++ printtype y

printinfertype :: Term -> String
printinfertype t =
  let (_, _, _, z) = infertype t
   in printterm t ++ " : " ++ printtype' z

printinfertype' :: Term -> String
printinfertype' t =
  let (v, x, y, z) = infertype t
   in printterm t ++ " : " ++ printtype v ++ "\n" ++ printterm t ++ " : " ++ printtype' z ++ "\n" ++ printconstraintset x ++ "\n" ++ printsubstitutionmap y

-- | some examples
bcombinator :: String
bcombinator = "\\x.\\y.\\z.(x (y z))"

b'combinator :: String
b'combinator = "\\x.\\y.\\z.(y (x z))"

icombinator :: String
icombinator = "\\x.x"

kcombinator :: String
kcombinator = "\\x.\\y.x"

ccombinator :: String
ccombinator = "\\x.\\y.\\z.((x z) y)"

wcombinator :: String
wcombinator = "\\x.\\y.((x y) y)"

commutativityofproducts :: String
commutativityofproducts = "\\x.{snd x , fst x}"

commutativityofsums :: String
commutativityofsums = "\\x.case x of \\y.inr y | \\y.inl y"

splitconditional :: String
splitconditional = "\\x.\\y.\\z.((x z)(y z))"

prodtosum :: String
prodtosum = "\\x.\\y.case y of fst x | snd x"

-- ((A->C)+(B->C))->((AxB)->C)
sumtoprod :: String
sumtoprod = "\\x.\\y. case x of \\z.(z fst y) | \\z.(z snd y)"

-- x : ((A->C)+(B->C))
-- y : (AxB)

parseterm = pTerm . myLexer

parseinferprint :: String -> String
parseinferprint s = case parseterm s of
  Left x -> "\n    Parser failed with the following error message: " ++ show x ++ "\n"
  Right x -> "\n    " ++ printinfertype x ++ "\n"

-- | evaluator for terms
eval :: Term -> Term
eval (App (Abs v t) y) = eval $ subs v y t
eval (Fst (Pair x _)) = eval x
eval (Snd (Pair _ y)) = eval y
eval (Case (Inl x) y _) = eval (App y x)
eval (Case (Inr x) _ z) = eval (App z x)
eval (Pair x y) = Pair (eval x) (eval y)
eval x = x

subs :: Variable -> Term -> Term -> Term
subs v t (Var x) = if x == v then t else (Var x)
subs v t (App x y) = App (subs v t x) (subs v t y)
subs v t (Abs x y) = Abs x (subs v t y)
subs v t (Pair x y) = Pair (subs v t x) (subs v t y)
subs v t (Fst x) = Fst (subs v t x)
subs v t (Snd x) = Snd (subs v t x)
subs v t (Inl x) = Inl (subs v t x)
subs v t (Inr x) = Inr (subs v t x)
subs v t (Case t1 t2 t3) = Case (subs v t t1) (subs v t t2) (subs v t t3)
subs v t (Abrt x) = Abrt (subs v t x)
subs _ _ T = T
subs _ _ F = F

parseevalprint s = case parseterm s of
  Left x -> "\n    Parser failed with the following error message: " ++ show x ++ "\n"
  Right x -> "\n    " ++ printinfertype (eval x) ++ "\n\n    " ++ printinfertype x ++ "\n"
