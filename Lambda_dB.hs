module Lambda_dB where

import Data.List

data Term = Ap Term Term
          | Ab Term
          | In Int

instance Show Term where
  show (Ap t1 t2)  = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Ab t@(In _)) = "λ" ++ show t
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

-- ========== The U-machine ==========
-- read https://www.dropbox.com/s/4eo36bg482b95si/Lien%20vers%20Bendkowski_Lescanne_counting_environment.pdf?dl=0
-- or https://www.dropbox.com/s/j66bq80mm1g84o9/popl_94pdf?dl=0

data ACTION  = UP | CLOS Term [(ACTION,Int)]

liftEnv :: [(ACTION,Int)] -> [(ACTION,Int)]
liftEnv = map (\(x,i)->(x,i+1))

-- one step of reduction of the U-machine
u1step :: [(Term,[(ACTION,Int)])] -> [(Term,[(ACTION,Int)])]
u1step ((Ap t1 t2,e) : f) = (t1,e) : (t2,e) : f -- APP 
u1step ((Ab t1,f):(t2,g):e) = (t1,((liftEnv f)++[((CLOS t2 g),0)])):e -- LBA-BET
u1step ((In 0,((CLOS t f),0):g):e) = (t,f++g):e -- FVAR
u1step ((In n,((CLOS _ _),0):g):e) = (In (n-1),g):e -- RVAR
u1step ((In n,((UP, 0):g)):e) = (In (n+1),g):e -- VARSHIFT
u1step ((In 0,(_,_):f):e) = (In 0,f):e -- FVARLIFT
u1step ((In n,(a,i):f):e) = (In (n-1),(a,i-1):(UP,0):f):e  -- RVARLIFT

-- computing of the weak normal form
uMachine :: [(Term,[(ACTION,Int)])] -> [(Term,[(ACTION,Int)])]
uMachine st@((Ab m,f):[]) = st
uMachine st@((In _,[]):_) = st
uMachine st = uMachine (u1step st)

-- ==== computing the strong normal form ====
-- from a state
uSN :: (Term,[(ACTION,Int)]) -> Term
uSN (t,e) = case uMachine [(t,e)] of
              (Ab t',f):[] -> Ab (uSN (t', liftEnv f))
              (In n,[]):f -> foldl Ap (In n) (map uSN f)
-- the strong normal form of a term if it exists
sN :: Term -> Term
sN t = uSN (t,[])

-- ==== Another approach ====
-- UNDER WORK  --
data Anvil = UAnvil Term
           | Uup Int Anvil 
           | Uclos Int Anvil Anvil 

-- show
instance Show Anvil where
  show (UAnvil t) = show t
  show (Uup 0 a) = "(" ++ show a ++ ")[↑]"
  show (Uup 1 a) = "(" ++ show a ++ ")[⇑(↑)]"
  show (Uup n a) = "(" ++ show a ++ ")[⇑" ++ show n ++ "(↑)]"
  show (Uclos 0 a a') = "(" ++ show a' ++ ")[" ++ show a ++ "]"
  show (Uclos 1 a a') = "(" ++ show a' ++ ")[⇑(" ++ show a ++ ")]"
  show (Uclos n a a') = "(" ++ show a' ++ ")[⇑" ++ show n ++ "(" ++ show a ++ ")]"
             
lifEn :: Anvil -> Anvil
lifEn (UAnvil t) = UAnvil t
lifEn (Uup i a) = Uup (i+1) a
lifEn (Uclos i a a') = Uclos (i+1) a a' 

-- one step
u :: (Anvil,[Anvil]) -> (Anvil,[Anvil])
-- APP
u (UAnvil (Ap t1 t2),stack) = (UAnvil t1,(UAnvil t2):stack)
u (Uup i (UAnvil (Ap t1 t2)),stack) =
  (Uup i (UAnvil t1),(Uup i (UAnvil t2)) : stack)
u (Uclos i a (UAnvil (Ap t1 t2)),stack) =
   (Uclos i a (UAnvil t1),(Uclos i a (UAnvil t2)) : stack)
-- LBA-BET  (à voir)
u (UAnvil (Ab t),a:stack) = (Uclos 0 a (UAnvil t),stack)
u (Uup i (UAnvil (Ab t)),a:stack) =
   (Uclos 0 a (Uup (i+1) (UAnvil t)),stack)
u (Uclos i a (UAnvil (Ab t)),a':stack) =
   (Uclos 0 a' (Uclos (i+1) a (UAnvil t)),stack)
-- FVAR
u (Uclos 0 a (UAnvil (In 0)),stack) = (a,stack)
-- RVAR
u (Uclos 0 _ (UAnvil (In n)),stack) = (UAnvil (In (n-1)),stack)
-- VARSHIFT
u (Uup 0 (UAnvil (In n)),stack) = (UAnvil (In (n+1)),stack)
-- FVARLIFT
u (Uclos i a (UAnvil (In 0)),stack) = (UAnvil (In 0),stack)
-- RVARLIFT
u (Uclos i a (UAnvil (In n)),stack) =
   (Uup 0 (Uclos (i-1) a (UAnvil (In (n-1)))), stack)
--
u (Uup i a,stack) = let (a',stack') = (a,stack) -- hum
                              in (Uup i a',stack')
u (Uclos i a1 a2,stack) = let (a',stack') = (a1,stack) -- hum 
                         in (Uclos i a' a2,stack') 

-- reduction
u' 0 x = x
u' n x = u' (n-1) (u x)

-- weak normal form
limit_uWN = 10

uWN :: Term ->  (Anvil,[Anvil])
uWN t = u' limit_uWN (UAnvil t,[])
