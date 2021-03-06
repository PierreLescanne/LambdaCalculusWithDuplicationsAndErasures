-- SystemF.hs by Pierre Lescanne
-- Time-stamp: "2019-01-18 22:13:43 pierre" 

-- This module is an attempt to address an adaptation
-- of System F to /\®.

module SystemF where

import Lambda_R_dB
import Data.List

data TypeF = V Int
           | Ar TypeF TypeF
           | FA TypeF

(→) ty1 ty2 = Ar ty1 ty2

instance Show TypeF where
  --show ty = showBN ty
  show ty = showA ty
    where
      showBN (FA (V 0)) = "⊥"
      showBN (FA (Ar (V 0) (V 0))) = "ident"
      showBN (FA (Ar (V 0) (Ar (V 0) (V 0)))) = "bool"
      showBN (FA (Ar (Ar (V 0) (V 0)) (Ar (V 0) (V 0)))) = "nat"
      showBN ty = showA ty 
-- showA is the canonical show function,
-- showBN is the show function that show ⊥, identity, bool and natural specifically
showA (V i) = show i
showA (Ar ty1 ty2) =  (showWith ty1) ++ "->" ++ (show ty2)
  where showWith (Ar ty1 ty2) = "(" ++ (showWith ty1) ++ "->" ++ (show ty2) ++ ")"
        showWith t = show t
showA (FA ty) = "∀(" ++  show ty ++ ")"

-- show LaTeX
showTypeLaTeX :: TypeF -> String 
showTypeLaTeX (FA (V 0)) = "\bot"
showTypeLaTeX (FA (Ar (V 0) (V 0))) = "\\textsf{ident}"
showTypeLaTeX (FA (Ar (V 0) (Ar (V 0) (V 0)))) = "\\textsf{bool}"
showTypeLaTeX (FA (Ar (Ar (V 0) (V 0)) (Ar (V 0) (V 0)))) = "\\textsf{natTes}"
showTypeLaTeX (V i) = show i
showTypeLaTeX (Ar ty1 ty2) =  (showWith ty1) ++ " \"->\" " ++ (showTypeLaTeX ty2)
  where showWith (Ar ty1 ty2) = "(" ++ (showWith ty1) ++ " \"->\" " ++ (showTypeLaTeX ty2) ++ ")"
        showWith ty = showTypeLaTeX ty
showTypeLaTeX (FA ty) = "\\forall(" ++  showTypeLaTeX ty ++ ")"

instance Eq TypeF where
  (V i) == (V j) = i == j
  (Ar ty1 ty2) == (Ar ty1' ty2') = ty1 == ty1' && ty2 == ty2'
  (FA ty) == (FA ty') = ty == ty'
  _ == _ = False

data Label = Index | Abstract | Apply | Contract | Thin | ForIntro | ForElim TypeF

instance Show Label where
  show Index = "Index"
  show Abstract = "Abstract"
  show Apply = "Apply"
  show Contract = "Duplicate"
  show Thin = "Erase"
  show ForIntro = "∀Intro"
  show (ForElim ty) = "∀Elim (" ++ show ty ++ ")"

showLabelLaTeX :: Label -> String
showLabelLaTeX Index = "\\textit{Index}"
showLabelLaTeX Abstract = "\\textit{Abstract}"
showLabelLaTeX Apply = "\\textit{Apply}"
showLabelLaTeX Contract = "\\textit{Duplicate}"
showLabelLaTeX Thin = "\\textit{Erase}"
showLabelLaTeX ForIntro = "\\forall \\textit{Intro}"
showLabelLaTeX (ForElim ty) = "\\forall \\textit{Elim} (" ++ showTypeLaTeX ty ++ ")"


showContext :: [((Int,[Bool]),TypeF)] -> String
showContext [] = ""
showContext [((i,lb),ty)] = "{" ++ show i ++ "," ++ showBoolStr lb ++ "}:" ++show ty
showContext (((i,lb),ty):g) = "{" ++ show i ++ "," ++ showBoolStr lb ++ "}:" ++show ty ++ ", " ++ showContext g

showContextLaTeX :: [((Int,[Bool]),TypeF)] -> String
showContextLaTeX [] = ""
showContextLaTeX [((i,lb),ty)] = "\\ind{" ++ show i ++ "}{" ++ showBoolLaTeX lb ++ "}{:}" ++showTypeLaTeX ty
showContextLaTeX (((i,lb),ty):g) = "\\ind{" ++ show i ++ "}{" ++ showBoolLaTeX lb ++ "}{:}" ++showTypeLaTeX ty ++ ", " ++ showContextLaTeX g

data TypeTree =
    ZeroAry Label [((Int,[Bool]),TypeF)] RTerm TypeF -- / Γ |- t : σ (Label)
  | UnAry Label TypeTree [((Int,[Bool]),TypeF)] RTerm TypeF -- tree / Γ |- t : σ (Label)
  | BinAry Label TypeTree TypeTree [((Int,[Bool]),TypeF)] RTerm TypeF -- tree1 tree2 / Γ |- t : σ (Label)
instance Show TypeTree where
  -- show tree = show1 tree 1
  show tree = "%% WARNING: this proof tree has been produced automatically.  Do not change it!" ++ showTypeTreeLaTeX tree

show1 :: TypeTree -> Int -> String
show1 (ZeroAry l g t ty) i = showContext g ++ " |- " ++
                             show t ++ ":" ++ show ty  ++
                             " (" ++ show l ++")"
show1 (UnAry l tree g t ty) i = show1 tree i ++ line ++ 
                                " (" ++ show l ++")\n" ++
                                showContext g ++ " |- " ++
                                show t ++ ":" ++ show ty
--   show (BinAry l tree1 tree2 g t ty) = show tree2 ++ lineTy ++ "\n" ++ sign ++ "\n\n" ++
--                                        show tree1 ++ sign ++ line ++ line0 ++ 
--                                        " (" ++ show l ++")\n" ++
--                                        showContext g ++ " |- " ++
--                                        show t ++ ":" ++ show ty

show1 (BinAry l tree1 tree2 g t ty) i = case tree2 of
  (ZeroAry _ _ _ _) -> let shtr2 = show tree2
                           shtr1 = show1 tree1 i
                           space = take (widthLine - (7+length shtr2 + lengthRoot tree1)) (repeat ' ')
                       in shtr1 ++ space ++
                          shtr2 ++ line ++ 
                          " (" ++ show l ++")\n" ++
                          showContext g ++ " |- " ++
                          show t ++ ":" ++ show ty
  otherwise -> take (2*i) (repeat ' ') ++ "== let TREE_" ++ show i ++ " == \n" ++ show1 tree2 (2*i) ++
               "\n\n"++take (2*i) (repeat ' ') ++ "== in == \n" ++ 
               show1 tree1 (2*i+1) ++ signt i ++ line ++ 
               " (" ++ show l ++")\n" ++
               showContext g ++ " |- " ++
               show t ++ ":" ++ show ty

-- widthLine = 130  --my screen at home
widthLine = 144 -- my laptop with "DejaVu Sans Mono Book"
line = "\n" ++  take widthLine (repeat '-')
lineTy = "\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
sign = "                          ■"
signt i = take 50 (repeat ' ') ++ "TREE_" ++ show i

lengthRoot tree = let (g,t,ty) = root tree
                  in 4 + length(showContext g ++ show t ++ show ty) + case tree of
                    ZeroAry _ _ _ _ -> 7
                    otherwise -> 0 
-- Show LaTeX
showTypeTreeLaTeX :: TypeTree -> String
showTypeTreeLaTeX (ZeroAry l g t ty) =
  "\n\\prooftree" ++
  "\n\\using (" ++ showLabelLaTeX l ++ ")" ++
  "\n\\justifies " ++ showContextLaTeX g ++
  " \"|-\" " ++ showLaTeX t ++ "{:}" ++ showTypeLaTeX ty ++
  "\n\\endprooftree"

showTypeTreeLaTeX (UnAry l tree g t ty) = 
  "\n\\prooftree" ++
  showTypeTreeLaTeX tree ++ 
  "\n\\using (" ++ showLabelLaTeX l ++ ")" ++
  "\n\\justifies " ++ showContextLaTeX g ++
  " \"|-\" " ++ showLaTeX t ++ "{:}" ++ showTypeLaTeX ty ++
  "\n\\endprooftree"

showTypeTreeLaTeX (BinAry l tree1 tree2 g t ty) =
  "\n\\prooftree" ++
  showTypeTreeLaTeX tree1 ++ "\\quad" ++
  showTypeTreeLaTeX tree2 ++ 
  "\n\\using (" ++ showLabelLaTeX l ++ ")" ++
  "\n\\justifies " ++ showContextLaTeX g ++
  " \"|-\" " ++ showLaTeX t ++ "{:}" ++ showTypeLaTeX ty ++
  "\n\\endprooftree"

-- ===========  Substitutions in types =================
data Subs = Sla TypeF | Li Subs | Shi

subs :: TypeF -> Subs -> TypeF
subs (Ar ty1 ty2) s = Ar (subs ty1 s) (subs ty2 s)
subs (FA ty) s = FA (subs ty (Li s))
subs (V 0) (Sla ty) = ty
subs (V i) (Sla _) = V (i-1)
subs (V 0) (Li s) = V 0
subs (V i) (Li s) = subs (subs (V (i-1)) s) Shi
subs (V i) Shi = V (i+1)

(↤) :: TypeF -> TypeF -> TypeF
(↤) ty1 ty2 = subs ty1 (Sla ty2)

-- ========== Type Trees ==========

-- root returns the judgment at the root of a type tree
root :: TypeTree -> ([((Int,[Bool]),TypeF)],RTerm,TypeF)
root (ZeroAry _ g t ty) = (g,t,ty)
root (UnAry _ _ g t ty) = (g,t,ty)
root (BinAry _ _ _ g t ty) = (g,t,ty)

label :: TypeTree -> Label
label (ZeroAry l _ _ _) = l
label (UnAry l _ _ _ _ ) = l
label (BinAry l  _ _ _ _ _) = l

ordContxt :: ((Int,[Bool]),TypeF) -> ((Int,[Bool]),TypeF) -> Bool
ordContxt ((i,alpha),_) ((j,beta),_) = i<j || (i==j  && alpha<<beta)
  where [] << (_:_) = True
        (False:_) << (True:_) = True
        (False:l) << (False:l') = l <<l'
        (True:l) << (True:l') = l << l'
        _ << _ = False

(===) :: Eq a => [a] -> [a] -> Bool
([]) === ([]) = True
(x:l) === l' = x `elem` l' && l === delete x l'

-- okTree tells whether a type tree is correct
okTree :: TypeTree -> Bool
okTree (ZeroAry Index g (Ind i alpha) ty) = g == [((i,alpha),ty)]
okTree (ZeroAry _ _ _ _) = False
okTree (UnAry Abstract tree g (Abs t) (Ar ty1 ty2)) =
  let g' = ((0,[]),ty1) : map (\((i,str),a')->((i+1,str),a')) g
  in okTree tree  && root tree == (g',t,ty2)
okTree (BinAry Apply tree1 tree2 g (App t1 t2) ty) =  
  let (g1,t1',ty1) = root tree1
      (g2,t2',ty2) = root tree2
  in okTree tree1 && okTree tree2 && (g1 ++ g2) === g &&
     t1 == t1' && t2 == t2' && ty1 == ty2→ty
okTree (UnAry Contract tree g (Dup i alpha t) ty) =
  let (g',t',ty') = root tree
  in case lookup (i,alpha) g of
    Just ty1 -> case lookup (i,alpha++[False]) g' of
      Just ty2 -> case lookup (i,alpha++[True]) g' of
        Just ty3 ->  ty' == ty && ty1 == ty2 && ty1 == ty3 &&
                     t' == t && okTree tree &&
                     delete ((i,alpha),ty1) g == delete ((i,alpha++[False]),ty2) (delete ((i,alpha++[True]),ty3) g')
        Nothing -> False
      Nothing -> False
    Nothing -> False
okTree (UnAry Thin tree g (Era i alpha t) ty) = 
  let (g',t',ty') = root tree
      remove (i,alpha) (((j,beta),ty):l) =
        if (i,alpha) == (j,beta) then l
        else ((j,beta),ty):(remove (i,alpha) l)
  in okTree tree && g' ==  remove (i,alpha) g && ty == ty' && t == t'
okTree (UnAry ForIntro tree g t (FA ty)) =
  let (g',t',ty') = root tree
      g'' = map (\(x,typ)->(x,subs typ Shi)) g
  in okTree tree && ty == ty' && g'' == g'
okTree (UnAry (ForElim ty1) tree g t ty) = 
  let (g',t',FA ty') = root tree
  in okTree tree && ty == subs ty' (Sla ty1) && g == g'

