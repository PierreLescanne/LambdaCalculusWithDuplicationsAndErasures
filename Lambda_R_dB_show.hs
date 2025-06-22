-- Lambda_R_dB_show.hs by Pierre Lescanne
-- Time-stamp: "2025-05-24 15:28:44 pierre" 
module Lambda_R_dB_show where

import Lambda_dB
import Lambda_R_dB
import Lambda_R_dB_Expl_Subs
-- routines for showing and equating terms                    
showBoolStr [] = "ε"
showBoolStr [b] = if b then "1" else "0"
showBoolStr (b1:b2:l) = (if b1 then "1" else "0") ++ showBoolStr (b2:l)

instance Show SubLiftShift where
  show Shift = "↑"
  show (Lift s) = "⇑(" ++ show s ++ ")"

-- The user may choose the kind of display she wants
instance Show RTerm where
  -- show t = showRTerm t -- classic and friendly for interaction
  show t = showLaTeX t -- LaTeX for a paper
  -- show t = showALaGhilezan t -- Silvia Ghilezan, Jelena Ivetic, Pierre Lescanne, and Silvia Likavec. 2014. Resource control and intersection types: an intrinsic connection. arXiv:1412.2219 
  -- show t = showALaGhilezanLaTeX t 
  -- show t = showALaLengrandLaTeX t -- Delia Kesner and Stéphane Lengrand. 2007. Resource operators for lambda-calculus. Inf. Comput. 205, 4 (2007), 419–473.

showRTerm (App t1 t2) = "(" ++ showRTerm t1 ++ " " ++ showRTerm t2 ++ ")"
showRTerm (Abs t@(Ind _ _)) = "λ" ++ showRTerm t
showRTerm (Abs t) = "λ(" ++ showRTerm t ++ ")"
showRTerm (Ind i α) = "⦇" ++ show i ++ "," ++ showBoolStr α ++ "⦈"
showRTerm (Era i α t) = "⦇" ++ show i ++ "," ++ showBoolStr α ++ "⦈ ⊙ " ++ show t
showRTerm (Dup i α t) = "⦇" ++show i ++ "," ++ showBoolStr α ++ "⦈ ▽ " ++ showRTerm t

-- The following functions are for printing easily
-- the LaTeX forms of RTerm for the article <<List types for resource aware languages:   an implicit name approach>>
showBoolLaTeX :: [Bool] -> String
showBoolLaTeX [] = "`e"
showBoolLaTeX [b] = if b then "1" else "0"
showBoolLaTeX (b1:b2:l) = (if b1 then "1" else "0") ++ showBoolLaTeX (b2:l)

showLaTeX :: RTerm -> String
-- showLaTeX (Abs (Abs (Era 0 [] (Ind 1 [])))) = "\\textsf{tt}"
-- showLaTeX (Abs (Era 0 [] (Abs (Ind 0 [])))) = "\\textsf{ff}"
showLaTeX (Ind i α) = "\\ind{" ++ show i ++ "}{" ++ showBoolLaTeX α ++ "}" 
showLaTeX (App t1 t2) = "(" ++ showLaTeX t1 ++ "\\," ++ showLaTeX t2 ++ ")"
showLaTeX (Abs t) = "(\\lambda" ++ showLaTeX t ++")"
showLaTeX (Dup i α t) = "\\dup{" ++ show i ++ "}{" ++  showBoolLaTeX α ++ "}{" ++ showLaTeX t ++ "}"
showLaTeX (Era i α t) = "\\era{" ++ show i ++ "}{" ++  showBoolLaTeX α ++ "}{" ++ showLaTeX t ++ "}"

-- ========================================
-- Fancy Show with explicit names
-- ========================================      

-- Translation from /\®dB synxtax to /\® syntax
-- from "à la Ghilezan et al."
-- to "à la Kesner and Lengrand"

dB2L :: Int -> RTerm -> RTerm
dB2L i (Ind n α) = Ind (i-n-1) α  -- i > n
dB2L i (App t1 t2) = App (dB2L i t1) (dB2L i t2)
dB2L i (Abs t) = Abs (dB2L (i+1) t)
dB2L i (Era n α t) = Era (i-n-1) α (dB2L i t)
dB2L i (Dup n α t) = Dup (i-n-1) α (dB2L i t)

ind2Var :: [((Int, [Bool]), String)]
ind2Var = [((0,[]),"x"),((1,[]),"y"),((2,[]),"z"),((3,[]),"u"),((4,[]),"v")]
          --,((0,[False]),"u"), ((0,[True]),"v"),((0,[False,False]),"w"),((0,[False,True]),"t"),((1,[False]),"s"),((1,[True]),"r")]

rInd2Var :: (Int,[Bool]) -> String
rInd2Var (i, α) = case lookup (i, α) ind2Var of
  Just v -> v
  Nothing -> num2Var i ++ showBoolStr α

rInd2VarLaTeX :: (Int,[Bool]) -> String
rInd2VarLaTeX (i, α) = case lookup (i, α) ind2Var of
  Just v -> v
  Nothing -> num2Var i ++ "_{" ++ showBoolStr α ++ "}"

showALaGhilezan t = showLevel 0 (dB2L 0 t) where
  showLevel _ (Ind n α) = rInd2Var (n,α)
  showLevel i (App t1 t2) = showLevel i t1 ++ " " ++ showLevelWith i t2
    where showLevelWith i (App t1 t2) = "(" ++ showLevel i t1 ++ " " ++ showLevelWith i t2 ++ ")"
          showLevelWith i t = showLevel i t
  showLevel i (Abs t@(App _ _)) = "^" ++ num2Var i  ++".(" ++ showLevel (i+1) t ++ ")"
  showLevel i (Abs t) = "^" ++ num2Var i  ++"." ++ showLevel (i+1) t
  showLevel i (Era n α t) = (rInd2Var (n,α)) ++ "⊙(" ++ showLevel i t ++ ")"
  showLevel i (Dup n α t) = (rInd2Var (n,α)) ++ "<^" ++
                                rInd2Var (n,α++[False]) ++ "_" ++ rInd2Var (n,α++[True]) ++ "(" ++
                                showLevel i t ++ ")"

showALaGhilezanLaTeX t = showLevel 0 (dB2L 0 t) where
  showLevel _ (Ind n α) = rInd2VarLaTeX (n,α)
  showLevel i (App t1 t2) = showLevel i t1 ++ "\\," ++ showLevelWith i t2
    where showLevelWith i (App t1 t2) = "(" ++ showLevel i t1 ++ "\\," ++ showLevelWith i t2 ++ ")" 
          showLevelWith i t = showLevel i t
  showLevel i (Abs t@(App _ _)) = "`l " ++ num2Var i  ++".(" ++ showLevel (i+1) t ++ ")"
  showLevel i (Abs t) = "`l " ++ num2Var i  ++"." ++ showLevel (i+1) t
  showLevel i (Era n α t) = "\\eraG{" ++ (rInd2VarLaTeX (n,α)) ++ "}{" ++ showLevel i t ++"}"
  showLevel i (Dup n α t) = "(\\dupG{" ++ (rInd2VarLaTeX(n,α)) ++ "}{" ++
                                rInd2VarLaTeX (n,α++[False]) ++ "}{" ++ rInd2VarLaTeX (n,α++[True]) ++ "}{" ++
                                showLevel i t ++ "})"

showALaLengrandLaTeX t = showLevel 0 (dB2L 0 t) where
  showLevel _ (Ind n α) = rInd2VarLaTeX (n,α)
  showLevel i (App t1 t2) = showLevel i t1 ++ "\\," ++ showLevelWith i t2
    where showLevelWith i (App t1 t2) = "(" ++ showLevel i t1 ++ "\\," ++ showLevelWith i t2 ++ ")" 
          showLevelWith i t = showLevel i t
  showLevel i (Abs t@(App _ _)) = "`l " ++ num2Var i  ++".(" ++ showLevel (i+1) t ++ ")"
  showLevel i (Abs t) = "`l " ++ num2Var i  ++"." ++ showLevel (i+1) t
  showLevel i (Era n α t) = "\\eraL{" ++ (rInd2VarLaTeX (n,α)) ++ "}{" ++ showLevel i t ++"}"
  showLevel i (Dup n α t) = "(\\dupL{" ++ (rInd2VarLaTeX(n,α)) ++ "}{" ++
                                rInd2VarLaTeX (n,α++[False]) ++ "}{" ++ rInd2VarLaTeX (n,α++[True]) ++ "}{" ++
                                showLevel i t ++ "})"

-- ========== Show  fo RClosure ==========
instance Show RClosure where
  show (ApC t t') = "(" ++ show t ++ " " ++ show t' ++ ")"
  show (AbC t@(IdC _ _)) = "λ" ++ show t
  show (AbC t) = "λ(" ++ show t ++ ")"
  show (IdC i α) = "{" ++ show i ++ "," ++ showBoolStr α ++ "}"
  show (ErC i α t) = "(" ++ show i ++ "," ++ showBoolStr α ++ ")⊙" ++ show t
  show (DuC i α t) = "(" ++show i ++ "," ++ showBoolStr α ++ ")▽" ++ show t
  show (Sub t s) = "(" ++ show t ++ "[" ++ show s ++ "])"

instance Show RSubstitution where
  show Up = "↑"
  show (Slash t) = show t ++ "/"
  show (LiC s) = "⇑(" ++ show s ++ ")"
