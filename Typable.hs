-- Typable.hs by Pierre Lescanne
-- Time-stamp: "2019-01-13 11:33:30 pierre" 

----------------------------------
-- type reconstruction
----------------------------------
-- Types
module Typable where
import Lambda_R_dB
import Data.List

data Type = Var Int
          | Arrow Type Type

instance Eq Type where
  (Var i) == (Var j) = i == j
  (Arrow ty1 ty2) == (Arrow ty1' ty2') = ty1 == ty1' && ty2 == ty2'
  _ == _ = False

instance Show Type where
  show ty = show_fancy_Type (indOf ty) ty
    where indOf (Var i) = [i]
          indOf (Arrow ty1 ty2) = indOf ty1 `union` indOf ty2
  -- show ty = showClassic ty

showClassic (Var i) = "α" ++ show i
showClassic (Arrow ty1 ty2) = (showWith ty1) ++ "->" ++ (showClassic ty2)
      where showWith ty@(Var _) = showClassic ty    
            showWith (Arrow ty1 ty2) = "(" ++ (showWith ty1) ++ "->" ++ (showClassic ty2) ++ ")"

greek_alphabet = ["α","β","γ","δ","ζ","η","θ"]

show_fancy_Type :: [Int] -> Type -> String 
show_fancy_Type l (Var i) = let Just k = elemIndex i l
                       in if k <= 6 then  greek_alphabet !! k else "α" ++ show (k-7)
show_fancy_Type l (Arrow ty1 ty2) = (showfWith ty1) ++ "->" ++ (show_fancy_Type l ty2)
      where showfWith ty@(Var _) = show_fancy_Type l ty    -- show With parentheses
            showfWith (Arrow ty1 ty2) = "(" ++ (showfWith ty1) ++ "->" ++ (show_fancy_Type l ty2) ++ ")"

-- Equation between types
type Equation = (Type,Type)

-- Giving a RTerm t, `build_constraint` returns a pair
-- of a type (the type of t) subject to
-- a set of equational constraints returned as a second value
build_constraint :: RTerm -> (Type, [Equation])
build_constraint t = 
  let (ty,_,constraint,_) = buildC t 0 0 
  in (ty, constraint)

-- `build_constraint` relies on a function `buildC` which takes
--   * a term t
--   * an integer, the depth of λ's the term lies at
--   * an integer,
-- returns
--   * the type associated with t
--   * the context: an associative list of pairs ((Int,[Bool]),Type)
--   * a set of constraints
--   * the number of type variables in the constraints and the context (necessary for creating a fresh variable)
buildC :: RTerm -> Int -> Int -> (Type, [((Int,[Bool]),Type)], [Equation],Int)
buildC (Ind i str) d cu = (Var cu, [((i,str), Var cu)],[],cu+1) 
buildC (Abs t) d cu = 
  let (ty,cntxt,constraint,cu') = buildC t (d+1) cu
      (Just a) = lookup (0,[]) cntxt
      cntxt' = map (\((i,str),a')->((i-1,str),a')) $ delete ((0,[]),a) cntxt
  in ((Arrow a ty),cntxt',constraint,cu')
buildC (App t1 t2) d cu = 
  let (ty1, cntxt1, constraint1, cu1) = buildC t1 d cu
      (ty2, cntxt2, constraint2, cu2) = buildC t2 d cu1
      ty = (Var cu2)
  in (ty,
      cntxt1++cntxt2,
      (ty1,(Arrow ty2 ty)): constraint1 ++ constraint2, 
      cu2+1)
buildC (Dup i str t) d cu =
  let (ty, cntxt, constraint,cu') = buildC t d cu
      str0 = str++[False]
      (Just ty0) = lookup (i,str0) cntxt
      str1 = str ++ [True]
      (Just ty1) = lookup (i,str1) cntxt
  in (ty,
      ((i,str),ty0):delete ((i,str0),ty0) (delete ((i,str1),ty1) cntxt),
      (ty0,ty1):constraint,
      cu')
buildC (Era i str t) d cu =
  let (ty, cntxt, constraint,cu') = buildC t d cu
  in (ty,
      ((i,str),Var cu'):cntxt,
      constraint,
      cu'+1)
           
-- operations for solving constraints
decompose :: Equation -> [Equation]
decompose ((Arrow ty1 ty2), (Arrow ty1' ty2')) = 
  decompose (ty1,ty1') ++ decompose (ty2,ty2')
decompose ((Arrow ty1 ty2),(Var i)) = [(Var i,(Arrow ty1 ty2))]
decompose (ty1,ty2) = [(ty1,ty2)]

nonTrivialEq :: Equation -> Bool
nonTrivialEq (Var i, Var j) = i /= j
nonTrivialEq (ty1, ty2) = True

-- v ¢ ty, means that v is a variable that occurs in ty.
-- v ¢ ty, means that 
(¢) :: Type -> Type -> Bool 
(Var i) ¢ (Var j) = False
(Var i) ¢ (Arrow ty1 ty2) = (Var i)¢=ty1 || 
                            (Var i)¢=ty2
    where (Var i) ¢= (Var j) = i == j
          (Var i) ¢= (Arrow ty1 ty2) = (Var i)¢=ty1 || 
                                       (Var i)¢=ty2

-- instanciates a variable Var i by a type ty in a type 
(←) :: Type -> Equation -> Type
(Var j) ← (Var i,ty) = if i == j then ty else Var j
(Arrow ty1 ty2) ← σ = Arrow (ty1 ← σ) (ty2 ← σ)

-- apply an instantion to an equation
apply::  Equation -> Equation -> Equation
apply σ @ (Var i,ty) (ty1,ty2) = (ty1 ← σ,  ty2 ← σ)

-- `solve` takes a set of constraints and a set of solved constraints and 
-- returns a set of constraints, a set of solved constraints or fails
solve :: [Equation] -> [Equation] -> Maybe ([Equation],[Equation])
solve (σ @ (Var i,ty):l) sol = 
  if  Var i ¢ ty then Nothing -- cycle detected
  else solve (map (apply σ) l) (σ:sol)
solve (eq:l) sol = solve (filter nonTrivialEq (decompose eq) ++ l) sol
solve [] sol = Just ([],sol)

-- ==== Final functions 
isTypable t = let (_,c) = build_constraint t in
             case solve c [] of
             Just _ -> True
             Nothing -> False

-- returns a type (before assignment) and an assignment
typeAssgOf :: RTerm -> Maybe (Type,[Equation])
typeAssgOf t = let (ty,c) = build_constraint t
               in case solve c []
                  of Just (_,sol) -> Just (ty,reverse sol)
                     Nothing -> Nothing
-- returns the most general type
typeOf :: RTerm -> Maybe Type
typeOf t =  case typeAssgOf t
            of Nothing -> Nothing
               Just (ty, sol) ->  
                 let asg ty [] = ty
                     asg ty (a:lasg) = asg (ty←a) lasg
                 in Just (asg ty sol)
