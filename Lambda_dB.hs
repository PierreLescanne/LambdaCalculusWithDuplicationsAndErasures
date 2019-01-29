module Lambda_dB where

import Data.List

data Term = Ap Term Term
          | Ab Term
          | In Int

instance Show Term where
  show (Ap t1 t2)  = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Ab t @ (In _)) = "λ" ++ show t
  show (Ab t) = "λ(" ++ show t ++ ")"
  show (In i) = show i

-- ====================
-- De Bruijn view
-- ====================

-- i ? t, means that (In i) occurs in t
(?) :: Int -> Term -> Bool
(?) i (Ap t1 t2) = i ? t1 || i ? t2
(?) i (Ab t) = (i+1) ? t
(?) i (In j) = i == j

-- The open indices of t
indOf :: Term -> [Int]
indOf (Ap t1 t2) = indOf t1 `union` indOf t2
indOf (Ab t) = map pred (filter (>0) (indOf t))
indOf (In i) = [i]

-- ====================
-- Level view
-- ====================
-- Terms can also be seens as term with levels
-- Thus one can write terms with names (see Lescanne & Rouyer-Degli, RTA6)

-- From de Bruijn to Level
-- i is the level
dB2Lev :: Int -> Term -> Term
dB2Lev i (In n) = In (i-n-1)  -- i > n
dB2Lev i (Ap t1 t2) = Ap (dB2Lev i t1) (dB2Lev i t2)
dB2Lev i (Ab t) = Ab (dB2Lev (i+1) t)

d2L = dB2Lev 0

listOfVariables = ["x","y","z","u","v", "w", "a","b","c","d"]

num2Var k = if k <= 9 then listOfVariables !! k else "x" ++ show (k-10)

showLev _ (In n) = num2Var n
showLev i (Ap t1 t2) = showLev i t1 ++ " " ++ showLevWith i t2
  where showLevWith i (Ap t1 t2) = "(" ++ showLev i t1 ++ " " ++ showLevWith i t2 ++ ")"
        showLevWith i t = showLev i t
showLev i (Ab t@(Ap _ _)) = "^" ++ num2Var i  ++".(" ++ showLev (i+1) t ++ ")"
showLev i (Ab t) = "^" ++ num2Var i  ++"." ++ showLev (i+1) t

-- On takes a term with de Bruijn indices and one print a terms with variables
show_fancy_Term t = showLev 0 (d2L t)

