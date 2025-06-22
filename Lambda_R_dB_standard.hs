module Lambda_R_dB_standard where

import Lambda_dB
import Lambda_R_dB
import Data.List
import Data.Maybe

-- ===== An exercise ===
-- The function `standardize`  returns an equivalent RTerm
-- where "Dup and Era are put at the right place"!
-- Unlike `representative`, `standardize` does not change the ®indices

standardize :: RTerm -> RTerm
-- many Dup may be added at a time
standardize (App t1 t2) =
  let st1 = standardize t1
      st2 = standardize t2
      init2 (i,a) = (i, init a)
      it1 = map init2 $ filter (not.null.snd) (indicesOf t1)
      it2 = map init2 $ filter (not.null.snd) (indicesOf t2)
      common = it1 `intersect` it2
  in dupTheIndices common $ App st1 st2

-- At most one Dup is added at a time
-- standardize (App t1 t2) =
--   let st1 = standardize t1
--       st2 = standardize t2
--       init2 (i,a) = (i, init a)
--       it1 = map init2 $ filter (not.null.snd) (indicesOf t1)
--       it2 = map init2 $ filter (not.null.snd) (indicesOf t2)
--   in case twins it1 it2 of
--     Nothing -> App st1 st2
--     Just (i,α) -> Dup i α (App st1 st2)

standardize (Abs t) = if (0,[]) € t then Abs (standardize t)
                      else Abs (Era 0 [] (standardize t))
standardize t@(Ind _ _) = t
standardize (Era i α  t) = Era i α $ standardize t
standardize (Dup i α t) = 
  let t' = standardize t
      ind = map (\(j,a)->(j,init a)) (indicesOf t')
      dupInd = snd $ listSingDup ind
  in dupTheIndices dupInd t'

---- Version with one Dup added at each step ----
-- standardize (Dup i α t) = 
--   let t' = standardize t
--       ind = map (\(j,a)->(j,init a)) (indicesOf t')
--   in case lfdL ind of
--     Just (i,α) -> (Dup i α t')
--     Nothing -> t'

-- ===== tools for standardize =====
-- `lfdL` looks for duplicates in a list and
-- returns the last duplicate
-- lfdL [3,2,1,5,0,2,4,5,6] == Just 5
lfdL :: Eq a => [a] -> Maybe a
lfdL [] = Nothing
lfdL (x:l) = case lfdL l of
  Nothing -> find ((==) x) l
  Just y -> Just y

-- `lfd1` look for duplicates in a list and
-- returns the first duplicate
-- lfd1 [3,2,1,5,0,2,4,5,6] == Just 2
lfd1 :: Eq a => [a] -> Maybe a
lfd1 [] = Nothing
lfd1 (x:l) = case find ((==) x) l of
  Nothing -> lfd1 l
  Just y -> Just y

-- Given two lists
-- `twins` looks for one element that belongs to each list.
twins :: Eq a => [a] -> [a]  -> Maybe a
twins [] _ = Nothing
twins (_:_) [] = Nothing
twins (x1:l1) (x2:l2) =
  if x1 == x2 then Just x1
  else if x1 `elem` l2 then Just x1
       else if x2 `elem` l1 then Just x2 
            else twins l1 l2 

-- we assume that there is only singles and duplicates
-- `listSingDup` returns a pair made of
-- the list of singles and the list of duplicates
listSingDup :: Eq a => [a] -> ([a],[a])
listSingDup [] = ([],[])
listSingDup (x:l) = let (s,d) = listSingDup l
            in case find ((==) x) l of
              Nothing -> (x:s, d)
              (Just _) -> (delete x s,x:d)

-- ========== I want standardize to look like representative
-- The open indices of t (t is assumed linear)
indOf' :: RTerm -> [(Int,[Bool])]
indOf' (App t1 t2) = indOf' t1 `union` indOf' t2
indOf' (Abs t) = map (\(i,α)->(i-1,α)) (filter (\(i,α)->i>0) (indOf' t))
indOf' (Ind i α) = [(i,α)]
indOf' (Era i α t) = (i,α):indOf' t
indOf' (Dup i α t) = (i,α):(delete (i,α++[False]) (delete (i,α++[True]) (indOf' t)))

sortRIndices :: [(Int,[Bool])] -> [(Int,[Bool])]
sortRIndices [] = []
sortRIndices ((i,α):l) = insertRIndices (i,α) (sortRIndices l)

insertRIndices :: (Int,[Bool]) -> [(Int,[Bool])] -> [(Int,[Bool])]
insertRIndices (i,α) [] = [(i,α)]
insertRIndices (i,α) ((j,β):l) = if i <= j && α << β then (i,α):(j,β):l else (j,β):insertRIndices (i,α) l

(<<) :: [Bool] -> [Bool] -> Bool
[] << [] = False
[] << _ = True
(False:_) << (True:_) = True
(True:_) << (False:_) = False
(_:α) << (_:β) = α << β

-- `consR` is a function used in `readLR`
-- given a boolean and an index, put the boolean (0 or 1)
-- in front of all the α parts associated with the index
consR' :: Bool -> (Int,[Bool]) -> RTerm -> RTerm
consR' b i (App t1 t2) = App (consR' b i t1) (consR' b i t2)
consR' b (i,α) (Abs t) = Abs (consR' b (i+1,α) t)
consR' b (i,α) (Ind j β) = if (i,α)==(j,β)
                       then Ind j (b:β)
                       else Ind j β
consR' b (i,α) (Era j β t) = if (i,α)==(j,β)
                          then Era j (b:β) (consR' b (i,α) t)
                          else Era j β (consR' b (i,α) t)
consR' b (i,α) (Dup j β t) = if (i,α)==(j,β)
                          then Dup j (b:β) (consR' b (i,α) t)
                          else Dup j β (consR' b (i,α) t)


sta' :: RTerm -> RTerm
sta' (App t1 t2) =
  let stat1 = sta' t1
      stat2 = sta' t2
      commonInd = sortRIndices $ indOf' t1 `intersect`  indOf' t2
      pt1 = foldl (.) id (map (consR' False) commonInd) stat1
      pt2 = foldl (.) id (map (consR' True) commonInd) stat2
  in dupTheIndices commonInd (App pt1 pt2)
sta' t = t

sta :: RTerm -> Maybe RTerm
sta t = let t' = sta' t in if t' == t then Nothing  else Just t'

-- `rot' transforms index {i,α00} |-> {i,α0}, {i,α01} |-> {i,α10}, {i,α1} |-> {i,α11}
rot :: Int -> [Bool] ->  RTerm -> RTerm
rot i α (App t1 t2) = App (rot i α t1) (rot i α t2)
rot i α (Abs t) = Abs (rot (i+1) α t)
rot i α (Ind j β) = if i == j then case stripPrefix α β of
                                        Just γ -> case γ of
                                          False : (False : δ) -> Ind j (α ++ [False] ++ δ)
                                          False : (True : δ) -> Ind j (α ++ [True,False] ++ δ)
                                          True : δ -> Ind j (α ++ [True, True] ++ δ)
                                        Nothing -> Ind j β 
                    else Ind j β
rot i α (Era j β t) = if i == j then case stripPrefix α β of
                                        Just γ -> case γ of
                                          False : (False : δ) -> Era j (α ++ [False] ++ δ) (rot i α t)
                                          False : (True : δ) -> Era j (α ++ [True,False] ++ δ) (rot i α t)
                                          True : δ -> Era j (α ++ [True, True] ++ δ) (rot i α t)
                                        Nothing -> Era j β  (rot i α t)
                    else Era j β  (rot i α t)
rot i α (Dup j β t) = if i == j then case stripPrefix α β of
                                        Just γ -> case γ of
                                          False : (False : δ) -> Dup j (α ++ [False] ++ δ) (rot i α t)
                                          False : (True : δ) -> Dup j (α ++ [True,False] ++ δ) (rot i α t)
                                          True : δ -> Dup j (α ++ [True, True] ++ δ) (rot i α t)
                                        Nothing -> Dup j β  (rot i α t)
                    else Dup j β  (rot i α t)

-- One step of sta
redSta :: RTerm -> RTerm
redSta t = case reduc sta t of Just u -> u
                               Nothing -> Ind 10000 [True,False,False,False,False]
nfSta :: RTerm -> RTerm
nfSta t = case reduc sta t of Just u -> nfSta (nfStruct u)
                              Nothing -> nfStruct t

-- look at ch2 and ch2''.  We have also to order the ®-indices according to the lexicographical order on α 

