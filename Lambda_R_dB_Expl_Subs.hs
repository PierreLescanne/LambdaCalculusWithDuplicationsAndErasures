module Lambda_R_dB_Expl_Subs where

import Lambda_dB
import Lambda_R_dB
import Data.List
import Data.Maybe

-- ************************************************************
-- **********                 UNDER WORK             **********
-- ************************************************************

-- ===============================================================
-- ========== The calculus of explicit susbtitution λυ® ==========
-- ===============================================================

-- for λυ read
-- https://www.dropbox.com/s/4eo36bg482b95si/Lien%20vers%20Bendkowski_Lescanne_counting_environment.pdf?dl=0
-- or https://www.dropbox.com/s/j66bq80mm1g84o9/popl_94pdf?dl=0
  
data RClosure  = ApC RClosure RClosure
           | AbC RClosure
           | IdC Int [Bool]
           | ErC Int [Bool] RClosure
           | DuC Int [Bool] RClosure
           | Sub RClosure RSubstitution

data RSubstitution = Up | Slash RClosure | LiC RSubstitution

instance Eq RClosure where
  (ApC t1 t2) == (ApC u1 u2) = t1 == u1 && t2 == u2
  (AbC t) == (AbC u) = t == u
  (==) (IdC i α ) (IdC j β) = i == j && α == β
  (==) (ErC i α t) (ErC j β u) = i == j && α == β && t == u
  (==) (DuC i α t) (DuC j β u) = i == j && α == β && t == u
  (Sub t s) == (Sub t' s') = t == t' && s == s'
  (==) _ _ = False

instance Eq RSubstitution where
  Up == Up = True
  Slash t == Slash t' = t == t'
  LiC s == LiC s' = s == s'

closOfRTerm ::  RTerm -> RClosure
closOfRTerm (App t1 t2) = ApC (closOfRTerm t1) (closOfRTerm t2)
closOfRTerm (Abs t) = AbC (closOfRTerm t)
closOfRTerm (Ind i α) = IdC i α
closOfRTerm (Dup i α t) = DuC i α (closOfRTerm t)
closOfRTerm (Era i α t) = ErC i α (closOfRTerm t)

(∈) :: (Int, [Bool]) -> RClosure -> Bool
(i,α) ∈ (AbC t) = (i+1,α) ∈ t
(i,α) ∈ (ApC t1 t2) = (i,α) ∈ t1 || (i,α) ∈ t2
(i,α) ∈ IdC j β = (i,α) == (j,β)
(i,α) ∈ (ErC j β t) = (i,α) == (j,β) || (i,α) ∈ t 
(i,α) ∈ (DuC j β t) = (i,α) == (j,β) || (i,α) ∈ t
(0,α) ∈ (Sub t Up) = False
(i,α) ∈ (Sub t Up) = (i-1,α) ∈ t
(i,α) ∈ (Sub t (Slash t')) = (i+1,α) ∈ t || (i,α) ∈ t'
(0,α) ∈ (Sub t (LiC s)) = True
(i,α) ∈ (Sub t (LiC s)) = (i-1,α) ∈ (Sub (Sub t s) Up)

-- 
idxOf :: RClosure -> [(Int, [Bool])]
idxOf (ApC t1 t2) = idxOf t1 ++ idxOf t2
idxOf (AbC t) = map (\(i,α)->(i-1,α)) (filter (\(i,[])->i>0) (idxOf t))
idxOf (IdC i α) = [(i,α)]
idxOf (ErC i α t) = (i,α):idxOf t 
idxOf (DuC i α t) = (i,α) : (delete (i,α++[True]) (delete (i,α++[False]) (idxOf t)))
idxOf (Sub t s) = map (\(i,α)->(i-1,α)) (filter (\(i,_)->i>0) (idxOf t)) ++ idxOfS s

idxOfS :: RSubstitution -> [(Int, [Bool])]
idxOfS Up = []
idxOfS (Slash t) = idxOf t
idxOfS (LiC s) = map (\(i,α)->(i+1,α)) (idxOfS s)

-- Given a list of indices and a term,
-- eraIndices applies all the erasings of that list to that closure
eraIndices :: [(Int,[Bool])] -> RClosure -> RClosure
eraIndices [] t = t
eraIndices ((i,α):l) t = ErC i α  (eraIndices l t)

-- Given a list of indices and a term,
-- dupIndices applies all the duplications of that list to that closure
dupIndices :: [(Int,[Bool])] -> RClosure -> RClosure
dupIndices [] t = t
dupIndices ((i,α):l) t = DuC i α  (dupIndices l t)

-- given a boolean, update the "open" indices of the given terms
-- by appending the boolean to there α part 
-- provided the index is not bound (told by i)
boolAfterα :: Bool -> Int -> RClosure -> RClosure
boolAfterα b i (ApC t1 t2) = ApC (boolAfterα b i t1) (boolAfterα b i t2)
boolAfterα b i (AbC t) = AbC (boolAfterα b (i+1) t)
boolAfterα b i (IdC j α) =
  if j < i then IdC j α
  else IdC j (α ++ [b])
boolAfterα b i (ErC j α t) =
  if j < i then ErC j α (boolAfterα b i t)
  else ErC j (α ++ [b]) (boolAfterα b i t)
boolAfterα b i (DuC j α t)  =
  if j < i then DuC j α (boolAfterα b i t)
  else DuC j (α ++ [b]) (boolAfterα b i t)

-- whichLiC tells the shape of a substitution
-- of the form LiC^q(t/) or the LiC^q(↑)
-- b == True says that it is /
whichLiC :: RSubstitution -> (Int,RClosure,Bool)
whichLiC (Slash t) = (0,t,True)
whichLiC (Up) = let a = AbC (AbC (ErC 0 [] (IdC 1 [])))
                in (0,a,False)
whichLiC (LiC s) = let (q,t,b) = whichLiC s in (q+1,t,b)

-- To take in to account a substitution of the form [t]⇑^q(t'/)
itLiftSlash :: RClosure -> Int -> RClosure -> RClosure
itLiftSlash t 0 t' = υ (Sub t (Slash t'))
itLiftSlash (ApC t1 t2) q t' = ApC (itLiftSlash t1 q t') (itLiftSlash t2 q t')
itLiftSlash (AbC t) q t' = AbC (itLiftSlash t (q+1) t')
itLiftSlash (IdC i α) q t = if i < q then IdC i α
                            else if i == q then upIt i t
                                 else IdC (i-1) α
itLiftSlash t q t' = t -- incomplet

upIt :: Int -> RClosure -> RClosure
upIt i t = t -- incomplet

--------------------
-- head reduction υ 
--------------------
υ :: RClosure -> RClosure
υ (Sub (ApC t t') s) = ApC (Sub t s) (Sub t' s)
υ (Sub (AbC t) s) = AbC (Sub t (LiC s))
-- Indices 
υ (Sub (IdC 0 α) (Slash t)) = t
υ (Sub (IdC i α) (Slash _)) = IdC (i-1) α
υ (Sub (IdC 0 α) (LiC _)) = IdC 0 α
υ (Sub (IdC i α) (LiC s)) = Sub (Sub (IdC (i-1) α) s) Up
υ (Sub (IdC i α) Up) = IdC (i+1) α
-- Erase
υ (Sub (ErC 0 α t) (Slash t')) = eraIndices (idxOf t') (Sub t (Slash t')) --  (0,α) ∉ t but Slash decreases the indices.
υ (Sub (ErC i α t) s) =
  let (q,_,b) = whichLiC s
  in if i < q then ErC i α (Sub t s)  
     else if b then ErC (i-1) α (Sub t s) -- Slash
          else ErC (i+1) α (Sub t s)              
-- Duplicate 
υ (Sub (DuC 0 α t) (Slash t')) =
  let red2 = υ (boolAfterα True 0 t) -- C'est tout faux !
      red1 = υ' (boolAfterα False 0 red2)
  in dupIndices (idxOf t') red1
υ (Sub (DuC i α t) s) =
  let (q,t1,b) = whichLiC s
  in if i < q then DuC i α (Sub t s)
     else if b then if i == q
                    then  itLiftSlash t i t1 
                    else DuC (i-1) α (Sub t s) -- Slash
          else DuC (i+1) α (Sub t s)     
--------------------
-- replacement υ'
--------------------
υ' :: RClosure -> RClosure
υ' (Sub (ApC t t') s) = ApC (Sub t s) (Sub t' s)
υ' (Sub (AbC t) s) = AbC (Sub t (LiC s))
-- Indices 
υ' (Sub (IdC 0 α) (Slash t)) = t
υ' (Sub (IdC i α) (Slash _)) = IdC i α
υ' (Sub (IdC 0 α) (LiC _)) = IdC 0 α
υ' (Sub (IdC i α) (LiC s)) = Sub (Sub (IdC (i-1) α) s) Up
υ' (Sub (IdC i α) Up) = IdC (i+1) α
-- Erase
υ' (Sub (ErC 0 α t) (Slash t')) = eraIndices (idxOf t') t 
υ' (Sub (ErC i α t) s) =
  let (q,_,b) = whichLiC s
  in if b then ErC i α (Sub t s)  -- Slash
     else if i < q then ErC i α (Sub t s) -- Up
          else ErC (i+1) α (Sub t s)   
--
υ' (Sub (DuC 0 α t) (Slash t')) =
  let red2 = υ' (boolAfterα True 0 t') 
      red1 = υ' (boolAfterα False 0 red2)
  in dupIndices (idxOf t') red1
υ' (Sub (DuC i α t) (Slash t')) = DuC i α (Sub t (Slash t'))
υ' (Sub (DuC i α t) s) =
  let (q,t1,b) = whichLiC s
  in if b then ErC i α (Sub t s)  -- faux
     else if i < q then ErC i α (Sub t s) -- Up
          else ErC (i+1) α (Sub t s)   

--------------------
-- υ-reduce
--------------------
redυ (Sub (Sub t s) s') = Sub (redυ (Sub t s)) s'
redυ (Sub t s) = υ (Sub t s)
redυ (ApC t t') = ApC (redυ t) (redυ t')
redυ (AbC t) = AbC (redυ t)
redυ (IdC i α) = IdC i α
redυ (ErC i α t) = ErC i α (redυ t)
redυ (DuC i α t) = DuC i α (redυ t)

--------------------
-- υ-normalize
--------------------
nfυ :: RClosure -> RClosure
nfυ t = let t' = redυ t in if t == t' then t else nfυ t' 

--------------------
-- β reduction
--------------------
βυ :: RClosure -> RClosure
βυ (ApC (AbC t) t') = nfυ (Sub t (Slash t'))
βυ (Sub (Sub t s) s') = Sub (βυ (Sub t s)) s'
βυ (Sub t s) = υ (Sub (βυ t) s)
βυ (ApC t t') = ApC (βυ t) (βυ t')
βυ (AbC t) = AbC (βυ t)
βυ (IdC i α) = IdC i α
βυ (ErC i α t) = ErC i α (βυ t)
βυ (DuC i α t) = DuC i α (βυ t)

--------------------
-- Only γω1 and γω2
--------------------
-- drop after α is the transformation αzβ -> αβ
dropAfter :: [Bool] -> [Bool] -> [Bool]
dropAfter [] [] = []
dropAfter [] (x:β) = β
dropAfter (a:α) (b:β) = if a == b then a:(dropAfter α β) else (b:β)

removeADup :: RClosure -> Int -> [Bool] -> RClosure
removeADup (ApC t1 t2) i α = ApC (removeADup t1 i α  ) (removeADup t2 i α  )
removeADup (AbC t)  i α = AbC (removeADup t (i+1) α)
removeADup (IdC j β) i α = 
  if i==j then IdC i (dropAfter α β) else IdC j β
removeADup (ErC j β t) i α = 
  if i==j then ErC i (dropAfter α β) (removeADup t i α)
  else ErC j β (removeADup t i α)
removeADup (DuC j β t) i α = 
  if i==j then DuC i (dropAfter α β) (removeADup t i α)
  else DuC j β (removeADup t i α)
       
-- `struct' contains alls stuctural contractions
-- but ε3 and ε4 (Notice that ε2, which exchanges the name in a duplication,
-- is meanlingless)

struct :: RClosure -> Maybe RClosure
struct t@(DuC i α (ApC t1 t2)) =                 -- γ2 and γ3
  if (i,α++[True]) ∈ t1 && (i,α++[False]) ∈ t1
  then Just (ApC (DuC i α t1) t2)
  else if (i,α++[True]) ∈ t2 && (i,α++[False]) ∈ t2
       then Just (ApC t1 (DuC i α t2))
       else Nothing
struct (DuC i α (AbC t)) = Just (AbC (DuC (i+1) α t))  -- γ1
struct (ApC (ErC i α t1) t2) = Just(ErC i α (ApC t1 t2)) -- ω2
struct (ApC t1 (ErC i α t2)) = Just(ErC i α (ApC t1 t2)) -- ω3
struct t@(AbC (ErC i α t')) =                         -- ω1
  if i > 0 then Just (ErC (i-1) α (AbC t'))
  else Nothing
struct (ErC i α (ErC j β t)) =
  if i < j then Just(ErC j β (ErC i α t))     -- ε1
  else Nothing
struct t = Nothing

structIt :: RClosure -> RClosure
structIt t@(ApC t1 t2) = case struct t of Just t' -> structIt t'
                                          Nothing -> case struct t1 of
                                            Just t1' -> structIt (ApC (structIt t1') (structIt t2))
                                            Nothing -> case struct t2 of
                                              Just t2' -> structIt (ApC (structIt t1) (structIt t2'))
                                              Nothing -> t
structIt (AbC t) = case struct (AbC t) of Just t' -> structIt t'
                                          Nothing -> case struct t of Just t'' -> structIt (AbC (structIt t''))
                                                                      Nothing -> AbC t
structIt (IdC i α) = IdC i α
structIt (ErC i α t) = case struct (ErC i α t) of
  Just t' -> structIt (ErC i α t')
  Nothing -> case struct t of Just t' -> structIt $ ErC i α t'
                              Nothing -> (ErC i α t)
structIt (DuC i α t) = case struct (DuC i α t) of
  Just t' -> structIt (DuC i α t')
  Nothing -> case struct t of Just t' -> structIt $ DuC i α t'
                              Nothing -> (DuC i α t)

γω :: RClosure -> RClosure
γω (DuC i α (ErC j β t)) = 
  if i==j && (α++[True]==β || α++[False]==β)
  then removeADup t i α 
  else ErC j β (DuC i α t)
γω (DuC i α t) = DuC i α (γω t)
γω (ApC t1 t2) = ApC (γω t1) (γω t2)
γω (AbC t) = AbC (γω t)
γω (ErC i α t) = ErC i α (γω t)
γω t = t

-----------------------
-- normalize βυ and γω
-----------------------
limitλυ = 100

nfλυ :: RClosure -> RClosure
nfλυ t = nf limitλυ t
         where nf n t = let t' = γω $ structIt $ βυ t
                        in if t == t' then t else nf (n-1) t'

-- ça bug sur nfλυ (toυ (ch5¤i)) !
--  βυ (toυ (ch5¤i)) donne λ((λ{0,ε} (1,1)▽({1,10} ({1,11} {0,ε}))))
-- alors que ça devrait donner 
-- λ((λ{0,ε} (λ{0,ε} (λ{0,ε} {0,ε}))))
-- je ne distribue pas les λ{0,ε} !

-- ==================== From Λ® to Λυ® ====================
toυ :: RTerm -> RClosure
toυ (App t1 t2) = ApC (toυ t1) (toυ t2)
toυ (Abs t) = AbC (toυ t)
toυ (Ind i α) = IdC i α
toυ (Era i α t) = ErC i α (toυ t)
toυ (Dup i α t) = DuC i α (toυ t)

-- ==========  Examples ==========
c = ApC (AbC (AbC (ErC 0 [] (IdC 1 [])))) (IdC 0 [False])
