module Lambda_R_dB where

import Data.List
import Data.Maybe
import Lambda_dB

data RTerm = App RTerm RTerm
           | Abs RTerm
           | Ind Int [Bool]
           | Era Int [Bool] RTerm
           | Dup Int [Bool] RTerm
           | Sub RTerm RTerm Int [Bool]
           | Sub' RTerm Substitution

-- an infix App
(¤) t1 t2 = App t1 t2

data Substitution = Shift
                  | Lift Substitution
                    
-- routines for showing and equating terms                    
showBoolStr [] = "ε"
showBoolStr [b] = if b then "1" else "0"
showBoolStr (b1:b2:l) = (if b1 then "1" else "0") ++ showBoolStr (b2:l)

instance Show Substitution where
  show Shift = "↑"
  show (Lift s) = "⇑(" ++ show s ++ ")"

instance Show RTerm where
--  show (Abs (Abs (Era 0 [] (Ind 1 [])))) = "true"
--  show (Abs (Era 0 [] (Abs (Ind 0 [])))) ="false"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Abs t @ (Ind _ _)) = "λ" ++ show t
  show (Abs t) = "λ(" ++ show t ++ ")"
  show (Ind i alpha) = "{" ++ show i ++ "," ++ showBoolStr alpha ++ "}"
  show (Era i alpha t) = "(" ++ show i ++ "," ++ showBoolStr alpha ++ ")⊙" ++ show t
  show (Dup i alpha t) = "<(" ++  show i ++ "," ++ showBoolStr alpha ++ ")" ++ show t
  show (Sub t1 t2 i alpha) = show t1 ++ "[" ++ show t2 ++ "/(" ++ show i ++ "," ++ showBoolStr alpha ++ ")]" 
  show (Sub' t s) = show t ++ "〚" ++ show s ++ "〛"

instance Eq RTerm where
  (==) (App t1 t2) (App u1 u2) = t1 == u1 && t2 == u2
  (==) (Abs t) (Abs u) = t == u
  (==) (Ind i alpha ) (Ind j beta) = i == j && alpha == beta
  (==) (Era i alpha t) (Era j beta u) = i == j && alpha == beta && t == u
  (==) (Dup i alpha t) (Dup j beta u) = i == j && alpha == beta && t == u
  (==) _ _ = False

-- The following functions are for printing easily
-- the LaTeX forms of RTerm for the article
showBoolLaTeX :: [Bool] -> [Char]
showBoolLaTeX [] = "\\varepsilon"
showBoolLaTeX [b] = if b then "1" else "0"
showBoolLaTeX (b1:b2:l) = (if b1 then "1" else "0") ++ showBoolLaTeX (b2:l)

showLaTeX :: RTerm -> [Char]
showLaTeX (Ind i alpha) = "\\ind{" ++ show i ++ "}{" ++ showBoolLaTeX alpha ++ "}" 
showLaTeX (App t1 t2) = "(" ++ showLaTeX t1 ++ "\\," ++ showLaTeX t2 ++ ")"
showLaTeX (Abs t) = "(\\lambda" ++ showLaTeX t ++")"
showLaTeX (Dup i alpha t) = "\\dup{" ++ show i ++ "}{" ++  showBoolLaTeX alpha ++ "}" ++ showLaTeX t
showLaTeX (Era i alpha t) = "\\era{" ++ show i ++ "}{" ++  showBoolLaTeX alpha ++ "} `(.) " ++ showLaTeX t

-- ==================== LINEARITY ====================
-- (iL t) returns the list of free extended de Bruijn indices of t
-- if all the binders of the term binds
-- one and only one de Bruijn index. 
iL :: RTerm -> Maybe [(Int,[Bool])]
iL (Ind n alpha) = Just [(n,alpha)]
iL (Abs t) =
  case iL t of
    Nothing -> Nothing
    Just u -> if (0,[]) `elem` u
              then let u' = delete (0,[]) u
                   in if isJust$find (((==) 0).fst) u' 
                      then Nothing
                      else Just $ map (\(i,a)->(i-1,a)) u'
              else Nothing 
iL (App t1 t2) =
  case iL t1 of
    Nothing -> Nothing
    Just u1 -> case iL t2 of
                         Nothing -> Nothing
                         Just u2 -> if null (u1 `intersect` u2)
                                    then Just(u1 ++ u2)
                                    else Nothing
iL (Era n alpha t) = case iL t of
                       Nothing -> Nothing
                       Just u -> Just ((n,alpha):u)
iL (Dup n alpha t) =
  case iL t of
    Nothing -> Nothing
    Just u -> if (n,alpha++[False]) `elem` u &&
                 (n,alpha++[True]) `elem` u
              then Just ((n,alpha):(delete (n,alpha++[False]) (delete (n,alpha++[True]) u)))
              else Nothing
      
                        
-- is linear in the sense that if it is a closed term then
-- all the binders bound one and only one index. 
isLinear = isJust.iL
-- ==================== From Λ® to Λ ====================
readback :: RTerm -> Term
readback (App t1 t2) = Ap (readback t1) (readback t2)
readback (Abs t) = Ab (readback t)
readback (Ind i _) = In i
readback (Era j beta t) = readback t
readback (Dup j beta t) = readback t

-- ==================== From Λ to Λ® ====================
-- `pref` (for  prefix) is a function used in `readLR`
-- given a boolean and an index, put the boolean (0 or 1)
-- in front of all the alpha parts associated with the index
pref :: Bool -> Int -> RTerm -> RTerm
pref b i (App t1 t2) = App (pref b i t1) (pref b i t2)
pref b i (Abs t) = Abs (pref b (i+1) t)
pref b i (Ind j beta) = if i==j
                        then Ind j (b:beta)
                        else Ind j beta
pref b i (Era j beta t) = if i==j
                          then Era j (b:beta) (pref b i t)
                          else Era j beta (pref b i t)
pref b i (Dup j beta t) = if i==j
                          then Dup j (b:beta) (pref b i t)
                          else Dup j beta (pref b i t)

-- call 'readLR' the function from  Λ (de Bruijn terms) to Λ®
readLR :: Term -> RTerm
readLR (Ap t1 t2) =
  let rt1 = readLR t1
      rt2 = readLR t2
      commonInd = sort $ indOf t1 `intersect`  indOf t2
      pt1 = foldl (.) id (map (pref False) commonInd) rt1
      pt2 = foldl (.) id (map (pref True) commonInd) rt2
  in dupTheIndices (map (\i->(i,[])) commonInd) (App pt1 pt2) 
readLR (Ab t) = if 0 ? t then Abs (readLR t) else Abs (Era 0 [] (readLR t))
readLR (In i) = Ind i []

-- ==================== From Λ® to Λ® ====================
-- Using `readLR` and `readback` we can produce the "representative"
-- of a term modulo structural equivalences
representative :: RTerm -> RTerm
representative = readLR . readback

-- The function `standardize`  returns an equivalent RTerm
-- where "Dup and Era are put at the right place"!
-- Unlike `representative`, `standardize` does not change the indices
standardize :: RTerm -> RTerm
-- many Dup may be added at a time
-- standardize (App t1 t2) =
--   let st1 = standardize t1
--       st2 = standardize t2
--       init2 (i,a) = (i, init a)
--       it1 = map init2 $ filter (not.null.snd) (indicesOf t1)
--       it2 = map init2 $ filter (not.null.snd) (indicesOf t2)
--       common = it1 `intersect` it2
--   in dupTheIndices common $ App st1 st2

-- At most one Dup is added at a time
standardize (App t1 t2) =
  let st1 = standardize t1
      st2 = standardize t2
      init2 (i,a) = (i, init a)
      it1 = map init2 $ filter (not.null.snd) (indicesOf t1)
      it2 = map init2 $ filter (not.null.snd) (indicesOf t2)
  in case twins it1 it2 of
    Nothing -> App st1 st2
    Just (i,alpha) -> Dup i alpha (App st1 st2)
standardize (Abs t) = if (0,[]) € t then Abs (standardize t)
                      else Abs (Era 0 [] (standardize t))
standardize t @ (Ind _ _) = t
standardize (Era i alpha  t) = Era i alpha $ standardize t
-- standardize (Dup i alpha t) = 
--   let t' = standardize t
--       ind = map (\(j,a)->(j,init a)) (indicesOf t')
--       dupInd = snd $ listSingDup ind
--   in dupTheIndices dupInd t'

---- Another version with one Dup added at each step ----
standardize (Dup i alpha t) = 
  let t' = standardize t
      ind = map (\(j,a)->(j,init a)) (indicesOf t')
  in case lfdL ind of
    Just (i,alpha) -> (Dup i alpha t')
    Nothing -> t'

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

-- ======== The substitution of Λ® ========

-- (i, alpha) € t, means that (i, alpha) occurs in t
(€) :: (Int, [Bool]) -> RTerm -> Bool
(€) (i,alpha) (App t1 t2) = (i,alpha) € t1 || (i,alpha) € t2
(€) (i,alpha) (Abs t) = (i+1,alpha) € t
(€) (i,alpha) (Ind j beta) = (i,alpha) == (j,beta)
(€) (i,alpha) (Era j beta t) = (i,alpha) == (j,beta) || (i,alpha) € t 
(€) (i,alpha) (Dup j beta t) = (i,alpha) == (j,beta) || (i,alpha) € t 

-- produces the list of all the "open" indices of a term                              
indicesOf :: RTerm -> [(Int, [Bool])]
indicesOf (App t1 t2) = indicesOf t1 ++ indicesOf t2
indicesOf (Abs t) = map (\(i,alpha)->(i-1,alpha)) (filter (\(i,_)->i>0) (indicesOf t))
indicesOf (Ind i alpha) = [(i,alpha)]
indicesOf (Era i alpha t) = (i,alpha):indicesOf t 
indicesOf (Dup i alpha t) =
  (i,alpha) : (delete (i,alpha++[True])
                      (delete (i,alpha++[False])
                              (indicesOf t)))

-- Given a list of indices and a term,
-- dupTheIndices applies all the duplications of that list to that term
dupTheIndices :: [(Int,[Bool])] -> RTerm -> RTerm
dupTheIndices [] t = t
dupTheIndices ((i,alpha):l) t = Dup i alpha  (dupTheIndices l t)

-- Given a list of indices and a term,
-- eraTheIndices applies all the erasings of that list to that term
eraTheIndices :: [(Int,[Bool])] -> RTerm -> RTerm
eraTheIndices [] t = t
eraTheIndices ((i,alpha):l) t = Era i alpha  (eraTheIndices l t)

-- given a boolean, update the "open" indices of the given terms
-- by appending the boolean to there alpha part 

upDate :: Bool -> Int -> RTerm -> RTerm
upDate b i (App t1 t2) = App (upDate b i t1) (upDate b i t2)
upDate b i (Abs t) = Abs (upDate b (i+1) t)
upDate b i (Ind j alpha) =
  if j < i then Ind j alpha
  else Ind j (alpha ++ [b])
upDate b i (Era j alpha t) =
  if j < i then Era j alpha (upDate b i t)
  else Era j (alpha ++ [b]) (upDate b i t)
upDate b i (Dup j alpha t)  =
  if j < i then Dup j alpha (upDate b i t)
  else Dup j (alpha ++ [b]) (upDate b i t)

-- substit reduces a substitution,
-- that is substit t u i alpha means reduce t [u / (i,alpha)] 
substit :: RTerm -> RTerm -> Int -> [Bool] -> RTerm
substit (App t1 t2) t i alpha = App (substit t1 t i alpha)
                                    (substit t2 t i alpha)
substit (Abs t1) t i alpha =
  let tSh = ift t Shift
  in  Abs (substit t1 tSh (i+1) alpha) 
substit (Ind i alpha) t j beta = if (i,alpha) == (j,beta)
                                then t
                                else if i <= j
                                     then (Ind i alpha)
                                     else (Ind (i-1) alpha)
substit t@(Era i alpha t1) u j beta =
  if (i,alpha) == (j,beta)
  then eraTheIndices (indicesOf u) (substit t1 u j beta)
  else if i <= j
       then Era i alpha (substit t1 u j beta)
       else Era (i-1) alpha (substit t1 u j beta)
substit (Dup i alpha t1) t j beta =
  if (i,alpha)  == (j,beta)
  then let red2 = substit t1 (upDate True 0 t) i (alpha++[True])
           red1 = replace red2 (upDate False 0 t) i (alpha++[False])
       in dupTheIndices (indicesOf t) red1
  else if i <= j
       then Dup i alpha (substit t1 t j beta)
       else Dup (i-1) alpha (substit t1 t j beta)

-- replace is a little like substit, but does not update the other indices
replace :: RTerm -> RTerm -> Int -> [Bool] -> RTerm
replace (App t1 t2) t i alpha = App (replace t1 t i alpha)
                                    (replace t2 t i alpha)
replace (Abs t1) t i alpha =
  let tSh = ift t Shift
  in  Abs (replace t1 tSh (i+1) alpha) 
replace (Ind i alpha) t j beta = if (i,alpha) == (j,beta)
                                 then t
                                 else (Ind i alpha)
replace u @ (Era i alpha t1) t j beta =
  if (i,alpha) == (j,beta)
  then u
  else Era i alpha (replace t1 t j beta)
replace (Dup i alpha t1) t j beta =
  if (i,alpha)  == (j,beta)
  then let red2 = replace t1 (upDate True 0 t) i (alpha++[True])
           red1 = replace red2 (upDate False 0 t) i (alpha++[False])
       in  dupTheIndices (indicesOf t) red1
  else Dup i alpha (replace t1 t j beta)

-- Reducing substitution of the form Lift^n(Shift)
ift :: RTerm -> Substitution -> RTerm
ift (App t1 t2) s = App (ift t1 s) (ift t2 s)
ift (Abs t) s = Abs (ift t (Lift s))
ift (Ind i alpha) s = Ind (effect s i) alpha
ift (Era i alpha t) s = Era (effect s i) alpha (ift t s)
ift (Dup i alpha t) s = Dup (effect s i) alpha (ift t s)

effect :: Substitution -> Int -> Int
effect Shift i = i+1
effect (Lift s) 0 = 0
effect (Lift s) i = (effect s (i-1)) + 1

-- ========== THE HEAD REDUCTION of Λ®  =========
-- lambdaR contains alls contractions
-- but ε3 and ε4 (Notice that ε2 is meanlingless)
lambdaR :: RTerm -> Maybe RTerm
lambdaR (App (Abs t) u) = Just (substit t u 0 [])  -- ϐ
lambdaR (Dup i alpha (Abs t)) = Just (Abs (Dup (i+1) alpha t))  -- γ1
lambdaR t @ (Dup i alpha (App t1 t2)) =                 -- γ2 and γ3
  if (i,alpha++[True]) € t1 && (i,alpha++[False]) € t1
  then Just (App (Dup i alpha t1) t2)
  else if (i,alpha++[True]) € t2 && (i,alpha++[False]) € t2
       then Just (App t1 (Dup i alpha t2))
       else Nothing
lambdaR t@(Abs (Era i alpha t')) =                         -- ω1
  if i > 0 then Just (Era (i-1) alpha (Abs t'))
  else Nothing
lambdaR (App (Era i alpha t1) t2) = Just(Era i alpha (App t1 t2)) -- ω2
lambdaR (App t1 (Era i alpha t2)) = Just(Era i alpha (App t1 t2)) -- ω3
lambdaR (Dup i alpha (Era j beta t)) =      -- γω1 and γω2 
  if i==j && alpha++[True]==beta
  then Just (replace t (Ind i alpha) i (alpha++[False]))
  else if i==j && alpha++[False]==beta
       then Just(replace t (Ind i alpha) i (alpha++[True]))
       else Just(Era j beta (Dup i alpha t))
lambdaR (Era i alpha (Era j beta t)) =
  if i < j then Just(Era j beta (Era i alpha t))     -- ε1
  else Nothing
lambdaR t = Nothing

-- Only beta contraction
betaR ::  RTerm -> Maybe RTerm
betaR (App (Abs t) u) = Just (substit t u 0 [])  -- ϐ
betaR t = Nothing

-- Only γω1 and γω2 
gamOm  ::  RTerm -> Maybe RTerm
gamOm (Dup i alpha (Era j beta t)) = 
  if i==j && alpha++[True]==beta
  then Just (replace t (Ind i alpha) i (alpha++[False]))
  else if i==j && alpha++[False]==beta
       then Just(replace t (Ind i alpha) i (alpha++[True]))
       else Just(Era j beta (Dup i alpha t))
gamOm t = Nothing

-- ======== THE REDUCTIONS OF Λ®  ========

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
    Ind i alpha -> Nothing
    Era i alpha u  -> case reduc r u of
      Just u' -> Just (Era i alpha u')
      Nothing -> Nothing
    Dup i alpha u -> case reduc r u of
      Just u' -> Just (Dup i alpha u')
      Nothing ->  Nothing

--- Local Variables:
--- mode: haskell
--- mode: haskell-indentation
--- End:
