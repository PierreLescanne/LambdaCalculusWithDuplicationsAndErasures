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

--- Local Variables:
--- mode: haskell
--- mode: haskell-indentation
--- End:
