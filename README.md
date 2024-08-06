# Propositions as Types, Programs as Proofs 

## Introduction

This is a not-so-brief tutorial on the Curry-Howard correspondence between *propositions* of intuitionistic logic and *types* of an extended version of the simply typed lambda calculus, and between Gentzen style natural deduction *proofs* of such propositions and *terms* of such a calculus.  

Its intended audience is philosophers with a background in logic. It presupposes some understanding of classical logic and Gentzen style natural deduction proofs but that's all. Unlike many presentations of the correspondence which only focus on the "implicational fragment" of intuitionistic propositional logic, the following tutorial explicitly discusses the correspondence between function types and conditionals, sum types and disjunctions, product types and conjunctions. 

The aim is to convey an understanding of the Curry-Howard correspondence in a hands-on way. Perhaps it would be possible to grasp the correspondence in an immediate way if one had a good background intuitionistic logic---in particular in Gentzen style natural deduction proofs in intuitionist logic---and in some extended version of the simply typed lambda calculus. 

The Curry-Howard correspondence provides a link between the worlds of logic and programming. There are many instances of the correspondence between different logics and different "programming languages." We focus here on the correspondence between intuitionistic propositional logic and an extended version of the simply typed lambda calculus---a primitive functional programming language. 

As I said, the aim is to convey an understanding in a hands-on way. So we will be implementing our extended version of the simply typed lambda calculus in the Haskell programming language, a language that takes its name from one of the same people the Curry-Howard correspondence gets its name from, Haskell Curry. I won't be trying to convey the basis of Haskell here. But I'll do my best to explain what the code is doing. 

We will begin, in the first instance, by trying to implement a function that checks whether a term of our extended simply typed lambda calculus (henceforth ESTLC) is well-typed and returns a derivation of the type of the term if it is. Given how we will have set things up, a term in our ESTLC will be well-typed if and only if its type corresponds to a tautology in intuitionistic propositional logic. The derivation we get if our term is well-typed will correspond to a Gentzen style natural deduction proof of the proposition corresponding to the type. 

This will give us an initial feel for the correspondence. However the limitation of our approach will be immediately felt: we effectively end up with a somewhat cumbersome way of writing natural deduction proofs in a linear format, that format being the format of an ESTLC term. True, our type-checker is a proof-checker, and we can easily translate our linear proofs into more familiar tree-style natural deduction proofs. But our terms are cumbersome to write. Our "proofs" of the commutativity of sums and of the commutativity of products look like this respectively: 

> $\lambda x$:(A+B).case $x$ of $\lambda y$:A.inr $y$ as (B+A) | $\lambda y$:B.inl $y$ as (B+A) 

> $\lambda x$:(AxB).{snd $x$,fst $x$}

The shortcoming is a result of the fact that we need to annotate abstractions and other terms in order to use our simple type-checking function. We will overcome this shortcoming by taking advantage of the fact that there's an algorithm available that can "infer" or "reconstruct" the type of a "raw" lambda term if that term can be typed according to certain typing rules. We'll implement a type-inference algorithm for our extended version of the simply typed lambda calculus. Our "proofs" of the commutativity of sums and of the commutativity of products become the following respectively:

> $\lambda x$.case $x$ of $\lambda y$.inr $y$ | $\lambda y$.inl $y$

> $\lambda x$.{snd $x$,fst $x$}

Finally, we will implement a function for evaluating our lambda terms, or "running" our "programs". Since we are coming at the issue from the side of logic, this will reassure us that we have bridged the world of logic and programming. We will see how our "program", given an "input", returns a particular "output". For example, this:

> ($\lambda x$.{snd $x$,fst $x$} {true,false})

Which happens to have the type (Bool $\times$ Bool), will evaluate to this: 

> {false,true} 

Which, not accidentally, also has the type (Bool $\times$ Bool). A further nice feature of implementing a function for evaluating our lambda terms is that if our "proofs" of certain propositions can ever be evaluated they will remain proofs of the same propositions, just simpler proofs. It turns out that this illustrates the final remaining part of the Curry-Howard correspondence, namely, that evaluation, or "running" the "program" corresponds to proof simplification. 

## Extended Simply Typed Lambda Calculus

Let's jump right in and start describing our extended version of the simply typed lambda calculus. We start with a description of our types. Here is how we specify our types as a data type in Haskell: 

```haskell 
data Type = A 
          | B 
          | C 
          | D 
          | Func Type Type          --e.g. (A->B)
          | Sum Type Type           --e.g. (A+B)
          | Prod Type Type          --e.g. (A*B)
          | Bot
          deriving (Show,Eq)
```

According to this definition a type is either an unspecified base type, A, B, C, or D, a function type, a sum type, a product type, or the empty type. The expressions `Func`, `Sum`, and `Prod` here are all data constructors. They construct data of the type `Type` given two bits of data of the type `Type`. `A`, `B`, `C`, `D`, and `Bottom` are also data constructors. They construct data of the type `Type` given no other bits of data. The analogy here is with two place and zero place connectives in logic. The line `deriving (Show,Eq)` just tells Haskell that we want to be able to print data of this type in an obvious way and that we want to be able to compare it for equality in an obvious way. 

Here is how we specify our terms as a data type in Haskell: 

```haskell
data Term = Var Variable            --e.g. x,y,z
          | Abs Variable Type Term  --e.g. \x:(A->B).x
          | App Term Term           --e.g. (x y)
          | Pair Term Term          --e.g. {x,y}
          | Fst Term                --e.g. fst x 
          | Snd Term                --e.g. snd x
          | Inl Term Type           --e.g. inl x
          | Inr Term Type           --e.g. inr x 
          | Case Term Term Term     --e.g. case x of y | z
          | Abort Term Type         --e.g. abort x (A->B)
          deriving (Show,Eq)
```

Notice that our definition of terms depends on our definition of types and that some terms are constructed from types and other terms. This captures the sense in which some terms in our ESTLC require "type annotations" and that variables in abstractions also require such abstractions. These are needed for our simple type checking algorithm. We will dispense with them once we introduce type reconstruction/inference later.    

At this stage it is worth noting that I am just taking for granted that we have parsing and printing functions available for our data types. That is, we have a way of parsing strings of characters into our data types and we have a way of printing them as strings of characters. We will want to be able to write things like `\x(A->B).{snd x,fst x}` and have it parsed into our Haskell representation. Notes on parsing and printing can be found below. But since these are not central to our task, we set them aside for now. 

## Type Checking

What we want to do now is write our type-checking function for our terms. Now, what we want is not merely a yes/no answer. We want to return the type of the term if it is well-typed and nothing otherwise. So let us call our function `gettype`. It will take a context and a term and return a "maybe" value. Here's the skeleton of our function. We will fill it in step by step. A context is defined as follows: 

```haskell 
type Context = Map.Map VarId Type
```

Our skeleton looks like this:

```haskell 
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

```

To type-check a variable, we just look up its type in the context. Since the result is a "maybe" type our result will already be of the right type. So we have:

```haskell 
gettypevar :: Context -> VarId -> Maybe Type
gettypevar ctx x1 = Map.lookup x1 ctx
```


To type-check an abstraction we add the type of the variable to the context and type-check the body of the abstraction on the new context.

```haskell 
gettypeabs :: Context -> VarId -> Type -> Term -> Maybe Type
gettypeabs ctx x1 typ1 trm1 = case gettype (Map.insert x1 typ1 ctx) trm1 of
  (Just typ2) -> Just (Func typ1 typ2)
  _ -> Nothing

```

```haskell 
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

```

## Type Inference 

Okay, that's cool. We've implemented type-checking for the extended simply typed lambda calculus. As mentioned earlier, this approach is a little cumbersome. It would be better if we could write terms without type annotations and have an algorithm "infer" a type for the term. 

Here's what our terms look like now. Notice the lack of type annotations on abstractions, left and right injections, and abort. 

```haskell
data Term = Var VarId               --e.g. x
          | Abs VarId Term          --e.g. \x.x
          | App Term Term           --e.g. (x y)
          | Pair Term Term          --e.g. {x,y}
          | Fst Term                --e.g. fst x 
          | Snd Term                --e.g. snd x
          | Inl Term                --e.g. inl x
          | Inr Term                --e.g. inr x 
          | Case Term Term Term     --e.g. case x of y | z
          | Abort Term              --e.g. abort x
          deriving (Show,Eq)
```

Our approach to type inference is called constraint-based typing. The basic idea is that rather than checking the type of a term as we encounter it, we just register certain constraints that need to be satisfied in order for the term to be well-typed. Constraint generation is just like checking but without the actual checking. 

```haskell
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

```







