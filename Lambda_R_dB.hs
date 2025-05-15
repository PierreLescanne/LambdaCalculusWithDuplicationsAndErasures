-- Lambda_R_dB.hs by Pierre Lescanne
-- Time-stamp: "2025-05-15 16:34:13 pierre" 

module Lambda_R_dB where

import Data.List
import Data.Maybe
import Lambda_dB

data RTerm = App RTerm RTerm
           | Abs RTerm
           | Ind Int [Bool]
           | Era Int [Bool] RTerm
           | Dup Int [Bool] RTerm

instance Eq RTerm where
  (==) (App t1 t2) (App u1 u2) = t1 == u1 && t2 == u2
  (==) (Abs t) (Abs u) = t == u
  (==) (Ind i α ) (Ind j β) = i == j && α == β
  (==) (Era i α t) (Era j β u) = i == j && α == β && t == u
  (==) (Dup i α t) (Dup j β u) = i == j && α == β && t == u
  (==) _ _ = False

-- an infix App
(¤) t1 t2 = App t1 t2

data SubLiftShift = Shift
                  | Lift SubLiftShift
                    
-- ==================== LINEARITY ====================
-- (iL t) returns the list of free (R)-de Bruijn indices of t
-- if all the binders of the term bind one and only one (R)-index.
remove :: Eq a => a -> [a] -> Maybe [a]
remove _ [] = Nothing
remove x (y:l) = if x == y then Just l
                 else case (remove x l) of
                   Nothing -> Nothing
                   Just l' -> Just (y:l')

iL :: RTerm -> Maybe [(Int,[Bool])]
iL (Ind n α) = Just [(n,α)]
iL (Abs t) =
  case iL t of
    Nothing -> Nothing
    Just u -> case remove (0,[]) u of 
      Nothing -> Nothing
      Just u' -> case find (((==) 0).fst) u' of
        Just _ -> Nothing
        Nothing -> Just $ map (\(i,a)->(i-1,a)) u'

iL (App t1 t2) =
  case iL t1 of
    Nothing -> Nothing
    Just u1 -> case iL t2 of
                         Nothing -> Nothing
                         Just u2 -> if null (u1 `intersect` u2)
                                    then Just(u1 ++ u2)
                                    else Nothing
iL (Era n α t) = case iL t of
                       Nothing -> Nothing
                       Just u -> Just ((n,α):u)
iL (Dup n α t) =
  case iL t of
    Nothing -> Nothing
    Just u -> if (n,α++[False]) `elem` u &&
                 (n,α++[True]) `elem` u
              then Just ((n,α):(delete (n,α++[False]) (delete (n,α++[True]) u)))
              else Nothing
      
                        
-- is linear in the sense that all the binders bound one and only one indices. 
isLinearAndClosed t = case iL t of
  Nothing -> False
  Just u -> u == []

isLinear = isJust.iL

-- ==================== From Λ® to Λ ====================
readback :: RTerm -> Term
readback (App t1 t2) = Ap (readback t1) (readback t2)
readback (Abs t) = Ab (readback t)
readback (Ind i _) = In i
readback (Era j β t) = readback t
readback (Dup j β t) = readback t

-- ==================== From Λ to Λ® ====================
-- `consR` is a function used in `readLR`
-- given a boolean and an index, put the boolean (0 or 1)
-- in front of all the α parts associated with the index
consR :: Bool -> Int -> RTerm -> RTerm
consR b i (App t1 t2) = App (consR b i t1) (consR b i t2)
consR b i (Abs t) = Abs (consR b (i+1) t)
consR b i (Ind j β) = if i==j
                        then Ind j (b:β)
                        else Ind j β
consR b i (Era j β t) = if i==j
                          then Era j (b:β) (consR b i t)
                          else Era j β (consR b i t)
consR b i (Dup j β t) = if i==j
                          then Dup j (b:β) (consR b i t)
                          else Dup j β (consR b i t)

-- call 'readLR' the function from  Λ (de Bruijn terms) to Λ®
readLR :: Term -> RTerm
readLR (Ap t1 t2) =
  let rt1 = readLR t1
      rt2 = readLR t2
      indToIndR i = (i,[])
      commonInd = sort (indOf t1 `intersect`  indOf t2)
      pt1 = foldl (.) id (map (consR False) commonInd) rt1
      pt2 = foldl (.) id (map (consR True) commonInd) rt2
  in dupTheIndices (map indToIndR commonInd) (App pt1 pt2) 
readLR (Ab t) = if 0 ? t then Abs (readLR t) else Abs (Era 0 [] (readLR t))
readLR (In i) = Ind i []

-- ==================== From Λ® to Λ® ====================
-- Using `readLR` and `readback` we can produce the "representative"
-- of a term modulo structural equivalences
representative :: RTerm -> RTerm
representative = readLR . readback

-- ======== The substitution of Λ® ========

-- (i, α) € t, means that (i, α) occurs in t
(€) :: (Int, [Bool]) -> RTerm -> Bool
(€) (i,α) (App t1 t2) = (i,α) € t1 || (i,α) € t2
(€) (i,α) (Abs t) = (i+1,α) € t
(€) (i,α) (Ind j β) = (i,α) == (j,β)
(€) (i,α) (Era j β t) = (i,α) == (j,β) || (i,α) € t 
(€) (i,α) (Dup j β t) = (i,α) == (j,β) || (i,α) € t 

-- The list of all the "open" indices of a term                              
indicesOf :: RTerm -> [(Int, [Bool])]
indicesOf (App t1 t2) = indicesOf t1 ++ indicesOf t2
indicesOf (Abs t) = map (\(i,α)->(i-1,α)) (filter (\(i,_)->i>0) (indicesOf t))
indicesOf (Ind i α) = [(i,α)]
indicesOf (Era i α t) = (i,α):indicesOf t 
indicesOf (Dup i α t) =
  (i,α) : (delete (i,α++[True])
                      (delete (i,α++[False])
                              (indicesOf t)))

-- Given a list of indices and a term,
-- dupTheIndices applies all the duplications of that list to that term
dupTheIndices :: [(Int,[Bool])] -> RTerm -> RTerm
dupTheIndices [] t = t
dupTheIndices ((i,α):l) t = Dup i α  (dupTheIndices l t)

-- Given a list of indices and a term,
-- eraTheIndices applies all the erasings of that list to that term
eraTheIndices :: [(Int,[Bool])] -> RTerm -> RTerm
eraTheIndices [] t = t
eraTheIndices ((i,α):l) t = Era i α  (eraTheIndices l t)

-- given a boolean, update the "open" indices of the given terms
-- by appending the boolean to there α part,
-- provided the index is not bound (told by i)
appendToα :: Bool -> Int -> RTerm -> RTerm
appendToα b i (App t1 t2) = App (appendToα b i t1) (appendToα b i t2)
appendToα b i (Abs t) = Abs (appendToα b (i+1) t)
appendToα b i (Ind j α) =
  if j < i then Ind j α
  else Ind j (α ++ [b])
appendToα b i (Era j α t) =
  if j < i then Era j α (appendToα b i t)
  else Era j (α ++ [b]) (appendToα b i t)
appendToα b i (Dup j α t)  =
  if j < i then Dup j α (appendToα b i t)
  else Dup j (α ++ [b]) (appendToα b i t)

-- 'sub' reduces a substitution,
-- that is 'sub t u i α' means reduce t [u / (i,α)] 
sub :: RTerm -> RTerm -> Int -> [Bool] -> RTerm
sub (App t1 t2) t i α = App (sub t1 t i α) (sub t2 t i α)
sub (Abs t1) t i α = Abs (sub t1 (ift t Shift) (i+1) α) 
sub (Ind i α) t j β = if (i,α) == (j,β) then t
                      else if i <= j
                           then (Ind i α)
                           else (Ind (i-1) α)
sub t@(Era i α t1) u j β =
  if (i,α) == (j,β)
  then eraTheIndices (indicesOf u) (sub t1 u j β)
  else if i <= j
       then Era i α (sub t1 u j β)
       else Era (i-1) α (sub t1 u j β)
sub (Dup i α t1) t j β =
  if (i,α)  == (j,β)
  then let red2 = sub t1 (appendToα True 0 t) i (α++[True])
           red1 = replace red2 (appendToα False 0 t) i (α++[False])
       in dupTheIndices (indicesOf t) red1
  else if i <= j
       then Dup i α (sub t1 t j β)
       else Dup (i-1) α (sub t1 t j β)

-- 'replace' is a little like 'sub', but does not update the other indices
replace :: RTerm -> RTerm -> Int -> [Bool] -> RTerm
replace (App t1 t2) t i α = App (replace t1 t i α)
                                    (replace t2 t i α)
replace (Abs t1) t i α =
  let tSh = ift t Shift
  in  Abs (replace t1 tSh (i+1) α) 
replace (Ind i α) t j β = if (i,α) == (j,β)
                                 then t
                                 else (Ind i α)
replace u @ (Era i α t1) t j β =
  if (i,α) == (j,β)
  then u
  else Era i α (replace t1 t j β)
replace (Dup i α t1) t j β =
  if (i,α)  == (j,β)
  then let red2 = replace t1 (appendToα True 0 t) i (α++[True])
           red1 = replace red2 (appendToα False 0 t) i (α++[False])
       in  dupTheIndices (indicesOf t) red1
  else Dup i α (replace t1 t j β)

-- 'ift' applies a substitution s of the form Lift^n(Shift) to a RTerm t
ift :: RTerm -> SubLiftShift -> RTerm
ift (App t1 t2) s = App (ift t1 s) (ift t2 s)
ift (Abs t) s = Abs (ift t (Lift s))
ift (Ind i α) s = Ind (subOnInd s i) α
ift (Era i α t) s = Era (subOnInd s i) α (ift t s)
ift (Dup i α t) s = Dup (subOnInd s i) α (ift t s)

subOnInd :: SubLiftShift -> Int -> Int
subOnInd Shift i = i+1
subOnInd (Lift s) 0 = 0
subOnInd (Lift s) i = (subOnInd s (i-1)) + 1

-- ========== THE HEAD REDUCTION of Λ®  =========
-- The names of the rules refer to
-- Silvia Ghilezan, Jelena Ivetic, Pierre Lescanne, Silvia Likavec:
-- ``Resource control and intersection types: an intrinsic connection''

-- `structural' contains alls stuctural contractions
-- but ε3 and ε4 (Notice that ε2, which exchanges the name in a duplication,
-- is meanlingless)

structural :: RTerm -> Maybe RTerm
structural t @ (Dup i α (App t1 t2)) =                 -- γ2 and γ3
  if (i,α++[True]) € t1 && (i,α++[False]) € t1
  then Just (App (Dup i α t1) t2)
  else if (i,α++[True]) € t2 && (i,α++[False]) € t2
       then Just (App t1 (Dup i α t2))
       else Nothing
structural (Dup i α (Abs t)) = Just (Abs (Dup (i+1) α t))  -- γ1
structural (App (Era i α t1) t2) = Just(Era i α (App t1 t2)) -- ω2
structural (App t1 (Era i α t2)) = Just(Era i α (App t1 t2)) -- ω3
structural t@(Abs (Era i α t')) =                         -- ω1
  if i > 0 then Just (Era (i-1) α (Abs t'))
  else Nothing
structural t' @ (Dup i α (Era j β t)) = Just (γω' t')     -- γω1 and γω2 
structural (Era i α (Era j β t)) =
  if i < j then Just(Era j β (Era i α t))     -- ε1
  else Nothing
structural t = Nothing

-- Only β contraction
betaR ::  RTerm -> Maybe RTerm
betaR (App (Abs t) u) = Just (sub t u 0 [])  -- β
betaR t = Nothing

-- Only γω1 and γω2 Actually ⊙-▽1 or ⊙-▽0 in the Fig.9 of [Ghil et al. 2035]
γω'  ::  RTerm -> RTerm
γω' (Dup i α (Era j β t)) = 
  if i==j && (α++[True]==β || α++[False]==β)
  then let raze (App t1 t2) = App (raze t1) (raze t2)  -- linearity is assumed
           raze (Abs t) = Abs (raze t)
           raze (Ind j β) = if i == j && (β == α ++ [True] || β == α ++ [False])
                            then Ind i α
                            else Ind j β
           raze (Era j β t) = if i == j && (β == α ++ [True] || β == α ++ [False])
                              then Era i α t -- no need to go further (linearity)
                              else Era j β (raze t)
           raze (Dup i α t) = Dup i α (raze t)
       in (raze t) -- remove all the occurrences of ⦇i,αb⦈ by ⦇i,α⦈ or of ⦇i,αb⦈⊙t by ⦇i,α⦈⊙t.
                   -- This function provides an incomplete implementation of 'replacement' in [Ghil et al. 2035]
   else Era j β (Dup i α t)
γω' t = t


-- ======== THE REDUCTIONS AND NORMALIZATION OF Λ®  ========

-- Given a relation 'r', r-reduce (one step) a term 't'
reduc :: (RTerm -> Maybe RTerm) -> RTerm -> Maybe RTerm
reduc r t = case r t of
  Just t' -> Just t'
  Nothing -> case t of
    App t1 t2 -> case reduc r t1 of
      Just t1' -> Just (App t1' t2)
      Nothing -> case reduc r t2 of
        Just t2' -> Just (App t1 t2')
        Nothing -> Nothing
    Abs u -> case reduc r u of
      Just u' -> Just (Abs u')
      Nothing -> Nothing
    Ind i α -> Nothing
    Era i α u  -> case reduc r u of
      Just u' -> Just (Era i α u')
      Nothing -> Nothing
    Dup i α u -> case reduc r u of
      Just u' -> Just (Dup i α u')
      Nothing ->  Nothing

-- One step of betaR 
β :: RTerm -> RTerm
β t = case reduc betaR t of Just u -> u
                            Nothing -> Ind 10000 [True,False,False,False,False]
-- One step of structural
στ  :: RTerm -> RTerm
στ t  = case reduc structural t of Just u -> u
                                   Nothing -> Ind 00001 [True,False,True,False,True]
-- One step of γω'
γΩ :: RTerm -> RTerm
γΩ (App t1 t2) = let t1' = γΩ t1 in if t1' == t1 then (App t1 (γΩ t2)) else App t1' t2
γΩ (Abs t) = (Abs (γΩ t))
γΩ (Ind i α) = Ind i α
γΩ (Era i α t) = Era i α (γΩ t)
γΩ t' @ (Dup i α t) = let t'' = γω' t' in if t'' == t' then Dup i α (γΩ t) else t''


-- ========== The normalization in Λ® ==========
-- For the examples, it is enough in order to reach the normal form.
-- If it is not enough, change the parameter after !!
      
-- Given a relation 'r', 'redIt' iterates r-reduce and
-- produces the stream of the reduced
      
redIt :: (RTerm -> Maybe RTerm) -> RTerm -> [RTerm]
redIt r t =  let b u = case reduc r u of
                  Nothing -> u
                  Just t' -> t'
            in t : map b (redIt r t)

betaNF t =  (redIt betaR t)  !! 16

-- Given two relation 'r' and 'r2', 'redIt' iterates r-reduce and r2-reduce and
-- produces the stream of the reduced
      
redIt2 :: (RTerm -> Maybe RTerm) -> (RTerm -> Maybe RTerm) -> RTerm -> [RTerm]
redIt2 r1 r2 t =  let b u = case reduc r1 u of
                        Nothing -> case reduc r2 u of
                                         Nothing -> u
                                         Just  v -> v
                        Just t' -> t'
                 in t : map b (redIt2 r1 r2 t)

-- the normal form according to betaR and structural
nfPath t = redIt2 betaR structural t
nf t = nfPath t !! 64

-- normalize by structural rules everywhere (now limit is necessary, since the process terminates always)
nfStruct t =  case reduc structural t of
  Nothing -> t
  Just t' -> nfStruct t'
