module Test_Lambda_R_dB where

import Lambda_dB
import Lambda_R_dB
import Data.List
import Typable
import SystemF
-- ===========
-- == tools ==
-- ===========
-- comparison between `standardize` t and t
stVSid t = standardize t == t
-- comparison between `standardize` and `representative`
stVSrep t = standardize t == representative t
-- It is no a real  normalisation, because the number of reductions is limited.
-- For the examples, it is enough in order to reach the normal form.
-- If it is not enough, change the parameter after !!.
nf t = (redIt lambdaR t)  !! 64
betaNF t =  (redIt betaR t)  !! 16

redIt :: (RTerm -> Maybe RTerm) -> RTerm -> [RTerm]
redIt r t =  let b u = case reduc r u of
                  Nothing -> u
                  Just t' -> t'
            in t : map b (redIt r t)

-- =========================================
-- ========= TEST of Lambda_R_dB  ==========
-- =========================================

----------------------
-- == Miscellaneous ==
----------------------

-- the term index 0
zero = Ind 0 []
-- the term index 1
one = Ind 1 []
-- the term index 2
two = Ind 2 []

--------------------
-- == Combinators ==
--------------------

-- the combinator K
k = Abs (Abs (Era 0 [] (Ind 1 [])))
s' = Abs (Abs (Dup 0 [] (App (App (Ind 2 []) (Ind 0 [False]))
                                 (App (Ind 1 []) (Ind 0 [True])))))
-- the combinator S
s = Abs s'
skk = App (App s k) k
-- the combinator I aka λ{0,ε}
i = Abs (Ind 0 [])
-- the term x x
xx = Dup 0 [] (App (Ind 0 [False]) (Ind 0 [True]))
xxx = Dup 0 [] (Dup 0 [False] (((Ind 0 [False,False])¤(Ind 0 [False,True]))¤(Ind 0 [True])))
lxxx = Abs xxx
xxx' =  Dup 0 [] (Dup 0 [True] (((Ind 0 [False])¤(Ind 0 [True,False]))¤(Ind 0 [True,True])))
lxxx' = Abs xxx'
-- the term  λx. x x aka λ 0 0 aka λ(<(0,ε)({0,0} {0,1}))
w = Abs xx
-- the term (λx. x x) (λx. x x)
-- aka (λ(<(0,ε)({0,0} {0,1})) λ(<(0,ε)({0,0} {0,1})))
ww = w ¤ w

-- the Curry Fix point combinator
y =
  let y0 = Abs ((Ind 1 [False]) ¤ (Dup 0 [] ((Ind 0 [False]) ¤ (Ind 0 [True]))))
      y1 = Abs ((Ind 1 [True]) ¤ (Dup 0 [] ((Ind 0 [False]) ¤ (Ind 0 [True]))))
  in Abs (Dup 0 [] (y0 ¤ y1))

-- == The Church numerals ==
-- n7 is in ΛdB
-- ch7 is in Λ®dB
n0 = Ab (Ab (In 0))
ch0 = readLR n0
ch0' = Abs (Abs (Era 1 [] (Ind 0 [])))

n1 = Ab (Ab (Ap (In 1) (In 0)))
ch1 = readLR n1

-- three forms of 2
n2 = Ab (Ab (Ap (In 1) (Ap (In 1) (In 0))))
ch2 = representative ch2' -- same as nf (chSucc¤ch1) and same readLR n2
ch2' = Abs (Dup 0 [] (Abs (App (Ind 1 [False]) (App (Ind 1 [True]) (Ind 0 [])))))
ch2'' = Abs (Abs (Dup 1 [] ((Ind 1 [True]) ¤ ((Ind 1 [False]) ¤ (Ind 0 [])))))
-- fourth forms of 3,
-- the first one is the representative os the others
-- ch3' is  nf (chSucc¤ch2)
-- ch3 is  also nf (chSucc'¤ch2)
n3 =  Ab (Ab (Ap (In 1) (Ap (In 1) (Ap (In 1) (In 0)))))
ch3 = representative ch3' -- same readLR n3
ch3' = Abs (Abs (Dup 1 [] (Dup 1 [False] (App (Ind 1 [False,False]) (App (Ind 1 [False,True]) (App (Ind 1 [True]) (Ind 0 [])))))))
ch3'' = Abs (Abs (Dup 1 [] (Dup 1 [True] (App (Ind 1 [True,False]) (App (Ind 1 [True,True]) (App (Ind 1 [False]) (Ind 0 [])))))))
ch3''' = Abs (Abs (Dup 1 [] ((Ind 1 [True])¤(Dup 1 [False] ((Ind 1 [False,False])¤((Ind 1 [False,True])¤(Ind 0 [])))))))
-- six forms of 5, the first one is "canonical"
ch5 = representative ch5'
ch5' = nf (chAdd¤ch3¤ch2)
ch5'' = nf (chAdd¤ch2¤ch3)
ch5''' = nf (chSucc¤(chSucc¤ch3))
ch5'''' = Abs (Abs (Dup 1 [] (Dup 1 [False] (Dup 1 [False,False] (Dup 1 [False,False,False] ((Ind 1 [False,False,False,False]) ¤ ((Ind 1 [False,False,False,True])¤((Ind 1 [False,False,True]) ¤ ((Ind 1 [False,True]) ¤ ((Ind 1 [True]) ¤ (Ind 0 [])))))))))))
ch5''''' = Abs (Abs (Dup 1 [] (Dup 1 [False] (Dup 1 [False,False] (Dup 1 [False,False,False] ((Ind 1 [True]) ¤ ((Ind 1 [False,True])¤((Ind 1 [False,False,True]) ¤ ((Ind 1 [False,False,False,True]) ¤ ((Ind 1 [False,False,False,False]) ¤ (Ind 0 [])))))))))))
-- two forms of Successor, both are "canonical"
-- and correspond to two different definitions
chSucc = Abs (Abs (Abs (Dup 1 [] (App (App (Ind 2 []) (Ind 1 [False]))
                                    (App (Ind 1 [True]) (Ind 0 []))))))
chSucc' = Abs (Abs (Abs (Dup 1 [] (App (Ind 1 [False])
                                       (App (App (Ind 2 []) (Ind 1 [True]))
                                            (Ind 0 []))))))
-- Addition
chAdd = Abs (Abs (Abs (Abs (Dup 1 [] (((Ind 3 []) `App` (Ind 1 [False])) `App` (((Ind 2 []) `App` (Ind 1 [True])) `App` (Ind 0 [])))))))

-- Multiplication
chMult = Abs (Abs (Abs (Abs ((Ind 3 []) ¤  ((Ind 2 []) ¤ (Ind 1 [])) ¤ (Ind 0 [])))))

-- Exponential 
chExp = Abs (Abs (Abs (Abs (( two ¤ (Ind 3 [])) ¤ one ¤ zero))))

-- == Variant of Church numerals ==
-- this a variant of Church numerals found in
-- J.L. Krivine "Lambda calul: types et modèles"
-- in the English translation:  J.L. Krivine "Lambda calculus and models"
-- Krivine uses the previous terms: ch0, ch1, ..., ch5, ...
num0  = Abs (Abs (Era 0 [] (Ind 1 [])))
num1 = Abs (Abs (App (Ind 0 []) (Ind 1 [])))
num2 = Abs (Abs (Dup 0 [] ((Ind 0 [False])  ¤ ((Ind 0 [True]) ¤ one))))

-- == Boolean ==
true = Abs (Abs (Era 0 [] (Ind 1 [])))
false = Abs (Era 0 [] (Abs (Ind 0 [])))
nEG = Abs (Abs (Abs ((Ind 2 []) ¤ (Ind 0 []) ¤ (Ind 1 []))))
oR = Abs (Abs (Abs (Abs (Dup 1 [] (((Ind 3 [])¤(Ind 1 [False]))¤(((Ind 2 [])¤(Ind 1 [True]))¤(Ind 0[])))))))
aND = Abs (Abs (Abs (Abs (Dup 0 [] (((Ind 3 [])¤(((Ind 2 [])¤(Ind 1 []))¤(Ind 0 [False]))¤ (Ind 0 [True])))))))
imp = Abs (Abs (Abs (Abs (Dup 1 [] (((Ind 3 [])¤(((Ind 2 [])¤(Ind 1 [False]))¤(Ind 0 []))¤ (Ind 1 [True])))))))
equiv' = Abs (Abs (aND¤(imp¤zero¤one)¤(imp¤one¤zero)))
equiv = Abs (Abs (Abs (Abs (Dup 0 [] (Dup 1 [] (Dup 2 [] ((Ind 3 [])¤((Ind 2 [False])¤(Ind 1 [False])¤(Ind 0 [False]))¤((Ind 2 [True])¤(Ind 0 [True])¤(Ind 1 [True])))))))))

-- Shorthands for Boolean
n b = nf (nEG¤b)
(∨) b1 b2 = nf (oR¤b1¤b2)
(∧) b1 b2 = nf (aND¤b1¤b2)
(⇒) b1 b2 = nf (imp¤b1¤b2)
(⇔) b1 b2 = nf (equiv¤b1¤b2)

-- == List[Boolean] ==
-- singleton false
singF = Abs (Abs ((one¤false)¤zero))
-- doubleton [false,true]
doub12 = Abs (Abs (Dup 1 [] (((Ind 1 [False])¤ch1)¤(((Ind 1 [True])¤ch2)¤zero))))
-- ================================
-- ==== Type trees in System F ====
-- ================================
-- A trivial wrong type tree
foo = ZeroAry Vari [] i nul
-- ===== Composition of types =====
-- Null
nul = FA (V 0)
-- Id
identity = FA(V 0 → V 0)
-- List
list =  FA(((V 1) → ((V 0)→(V 0)))→((V 0)→(V 0)))
listBool = list ←← boolean
listNat = list ←← natural
-- Product
(-*-) ty1 ty2 = FA (V 1 → V 2 → V 0) ←← ty1 ←← ty2
-- Sum
(-+-) ty1 ty2 = FA ((V 1 → V 0) → ((V 2 → V 0) → V 0)) ←← ty1 ←← ty2

-- ===== Church Numerals =====

natural = FA ((V 0→V 0)→(V 0→V 0))

-- ch0 has type natural = ∀((0->0)->(0->0)) given by tree6

tree = UnAry ForIntro tree1 [] ch0 natural
tree1 = UnAry Abstract tree2  [] ch0 ((V 0→V 0)→(V 0→V 0))
tree2 = UnAry Thin tree3 [((0,[]),(V 0→V 0))] t (V 0→V 0)
  where (Abs t) = ch0
tree3 = UnAry Abstract tree4 [] (Abs (Ind 0 [])) (V 0→V 0)
tree4 = ZeroAry Vari [((0,[]),V 0)] (Ind 0 []) (V 0)

-- ch1 has type  ∀((0->0)->(0->0)) given by arbre ("arbre" is "tree" in French)
arbre = UnAry ForIntro arbre1 [] ch1 natural
arbre1 = UnAry Abstract arbre2  [] ch1 ((V 0→V 0)→(V 0→V 0))
arbre2 = UnAry Abstract arbre3 [((0,[]), (V 0→V 0))] cutCh1 (V 0→V 0)  
  where (Abs cutCh1) = ch1
arbre3 = BinAry Apply arbre4 arbre5 [((0,[]),V 0),((1,[]), V 0→V 0)]
                      ((Ind 1 [])¤ (Ind 0 []))  (V 0)
arbre4 = ZeroAry Vari [((1,[]), V 0→V 0)] (Ind 1 []) (V 0→V 0) 
arbre5 = ZeroAry Vari [((0,[]),V 0)] (Ind 0 []) (V 0)

-- ch2 has type  ∀((0->0)->(0->0)) ("arbor" is "tree" in Latin)
arbor = UnAry ForIntro arbor1 [] ch2 natural
arbor1 = UnAry Abstract arbor2  [] ch2 ((V 0→V 0)→(V 0→V 0))
arbor2 = UnAry Abstract arbor3 [((0,[]), (V 0→V 0))] cutCh2 (V 0→V 0)  
  where (Abs cutCh2) = ch2
arbor3 = UnAry Contract arbor4 [((0,[]),V 0),((1,[]), V 0→V 0)] cutCutCh2 (V 0)
  where (Abs (Abs cutCutCh2)) = ch2
arbor4 = BinAry Apply arbor5 arbor6 [((0,[]),V 0),((1,[False]), V 0→V 0),((1,[True]), V 0→V 0)]
                      ((Ind 1 [False])¤((Ind 1 [True]) ¤ (Ind 0 [])))  (V 0)
arbor5 = ZeroAry Vari [((1,[False]), V 0→V 0)] (Ind 1 [False]) (V 0→V 0)
arbor6 = BinAry Apply arbor7 arbor8 g t ty
  where g = [((0,[]),V 0),((1,[True]), V 0→V 0)]
        t = (Ind 1 [True]) ¤ (Ind 0 [])
        ty = V 0
arbor7 = ZeroAry Vari g t ty
  where g = [((1,[True]),V 0→V 0)]
        t = Ind 1 [True]
        ty = V 0→V 0
arbor8 = ZeroAry Vari [((0,[]),V 0)] (Ind 0 []) (V 0)

-- chSucc has type  ∀((0->0)->(0->0)) ->  ∀((0->0)->(0->0)), aka natural→natural
-- ("baum" is "tree" in German)
baum = UnAry Abstract baum1 [] chSucc (natural→natural)
baum1 = UnAry  ForIntro baum2 g t ty
  where g = [((0,[]),natural)]
        Abs t = chSucc
        ty = natural
baum2 = UnAry Abstract baum3 g t ty
  where g = [((0,[]),natural)]
        Abs t = chSucc
        ty = (V 0→V 0)→(V 0→V 0)
baum3 = UnAry Abstract baum4 g t ty
  where g = [((0,[]),V 0→V 0),((1,[]),natural)]
        Abs (Abs t) = chSucc
        ty = V 0→V 0
baum4 = UnAry Contract baum5 g t ty
  where g = [((0,[]),V 0),((1,[]),V 0→V 0),((2,[]),natural)]
        Abs (Abs (Abs t)) = chSucc
        ty = V 0
baum5 = BinAry Apply baum6 arbor6 g t (V 0)
  where g = [((0,[]),V 0),((1,[False]),V 0→V 0),((1,[True]),V 0→V 0),((2,[]),natural)]
        t = ((Ind 2 [])¤(Ind 1 [False]))¤((Ind 1 [True])¤(Ind 0 []))
baum6 = BinAry Apply baum8 arbor5 g t ty
  where g = [((1,[False]),V 0→V 0),((2,[]),natural)]
        t = (Ind 2 [])¤(Ind 1 [False])
        ty = V 0→V 0
baum8 = UnAry (ForElim (V 0)) baum10 g t ty
  where g = [((2,[]),natural)]
        t = Ind 2 []
        ty = (V 0→V 0)→(V 0→V 0)
baum10 = ZeroAry Vari [((2,[]),natural)] (Ind 2 []) natural

-- chAdd has type ∀((0->0)->(0->0)) ->  ∀((0->0)->(0->0)) ("dendron" is "tree" in Greek)
dendron = UnAry Abstract dendron1 g t ty 
  where g = []
        t = chAdd
        ty = natural → (natural → natural)
dendron1 = UnAry Abstract dendron2 g t ty
  where g = [((0,[]),natural)]
        (Abs t) = chAdd
        ty = natural → natural
dendron2 =  UnAry ForIntro dendron3 g t ty
  where g = [((0,[]),natural), ((1,[]),natural)]
        (Abs (Abs t)) = chAdd
        ty = natural
dendron3 = UnAry Abstract dendron4 g t ty
  where g = [((0,[]),natural), ((1,[]),natural)]
        (Abs (Abs t)) = chAdd
        ty = (V 0→V 0)→(V 0→V 0)
dendron4 = UnAry Abstract dendron5 g t ty
  where g = [((0,[]),V 0→V 0), ((1,[]),natural), ((2,[]),natural)]
        (Abs (Abs (Abs t))) = chAdd
        ty = V 0→V 0
dendron5 = UnAry Contract dendron6 g t ty  
  where g = [((0,[]),V 0),((1,[]),V 0→V 0), ((2,[]),natural), ((3,[]),natural)]
        (Abs (Abs (Abs (Abs t)))) = chAdd
        ty = V 0
dendron6 = BinAry Apply dendron7 dendron11 g t ty 
  where g = [((0,[]),V 0),((1,[False]),V 0→V 0), ((1,[True]),V 0→V 0), ((2,[]),natural), ((3,[]),natural)]
        t = ((Ind 3 [])¤(Ind 1 [False]))¤(((Ind 2 [])¤(Ind 1 [True]))¤(Ind 0 []))
        ty = V 0
dendron7 = BinAry Apply dendron8  dendron10 g t ty
  where g = [((1,[False]),V 0→V 0), ((3,[]),natural)]
        t = (Ind 3 [])¤(Ind 1 [False])
        ty = V 0 → V 0
dendron8 = UnAry (ForElim (V 0)) dendron9 g t ty
  where g = [((3,[]),natural)]
        t = Ind 3 []
        ty = (V 0→V 0) → (V 0→V 0)
dendron9 = ZeroAry Vari g t ty
  where g = [((3,[]),natural)]
        t = Ind 3 []
        ty = FA((V 0→V 0) → (V 0→V 0))
dendron10 = ZeroAry Vari g t ty
  where g = [((1,[False]), V 0→V 0)]
        t = Ind 1 [False]
        ty = V 0→V 0
dendron11 = BinAry Apply dendron12 dendron16 g t ty
  where g = [((0,[]),V 0),((1,[True]),V 0→V 0), ((2,[]),natural)]
        t = ((Ind 2 [])¤(Ind 1 [True]))¤(Ind 0 [])
        ty = V 0
dendron12 = BinAry Apply dendron13 dendron15 g t ty
  where g = [((1,[True]),V 0→V 0), ((2,[]),natural)]
        t = (Ind 2 [])¤(Ind 1 [True])
        ty = V 0→V 0
dendron13 = baum8
dendron15 = arbor7
dendron16 = tree4

-- W I = (λ<(0,ε)({0,0} {0,1}) λ{0,ε}) has type ∀(0->0) given by drvo
drvo = BinAry Apply drvo1 drvo2 [] (w¤i) identity
drvo1 = UnAry Abstract drvo5 [] w (identity→identity)
drvo2 = UnAry ForIntro drvo3 [] i (identity)
drvo3 = UnAry Abstract drvo4 [] (Abs (Ind 0 [])) (V 0→V 0)
drvo4 = ZeroAry Vari [((0,[]),V 0)] (Ind 0 []) (V 0)
drvo5 = UnAry Contract drvo6 [((0,[]),identity)] xx identity
drvo6 = BinAry Apply drvo7 drvo9 [((0,[False]),identity),((0,[True]),identity)] (App (Ind 0 [False]) (Ind 0 [True])) identity
drvo7 = UnAry (ForElim identity) drvo8  [((0,[False]),identity)] (Ind 0 [False]) (identity→identity)
drvo8 = ZeroAry Vari  [((0,[False]),identity)] (Ind 0 [False]) (identity)
drvo9 = ZeroAry Vari  [((0,[True]),identity)] (Ind 0 [True]) (identity)


-- ===== Booleans =====
boolean = FA (V 0→(V 0→V 0))

-- false has type boolean = ∀(0->0->0)
bush = UnAry ForIntro bush1 g t ty
  where g = []
        t = false
        ty = boolean
bush1 = UnAry Abstract bush2 g t ty
  where g = []
        t = false
        ty = V 0→(V 0→V 0)
bush2 = UnAry Thin bush3 g t ty
  where g = [((0,[]),V 0)]
        (Abs t) = false
        ty = V 0→V 0
bush3 = UnAry Abstract tree4 g t ty
  where g = []
        t = Abs (Ind 0 [])
        ty = V 0→V 0

-- oR has type boolean → (boolean → boolean) 
buisson = UnAry Abstract buisson1 g t ty
  where g = []
        t = oR
        ty = boolean → (boolean → boolean)
buisson1 = UnAry Abstract buisson2 g t ty
  where g = [((0,[]),boolean)]
        (Abs t) = oR
        ty = boolean → boolean
buisson2 = UnAry ForIntro buisson3  g t ty
  where g = [((0,[]),boolean),((1,[]),boolean)]
        (Abs (Abs t)) = oR
        ty = boolean
buisson3 = UnAry Abstract buisson4 g t ty
  where g = [((0,[]),boolean),((1,[]),boolean)]
        (Abs (Abs t)) = oR
        ty = V 0→(V 0→V 0)
buisson4 = UnAry Abstract buisson5 g t ty
  where g = [((0,[]),V 0),((1,[]),boolean),((2,[]),boolean)]
        (Abs (Abs (Abs t))) = oR
        ty = V 0→V 0
buisson5 = UnAry Contract buisson6 g t ty
  where g = [((0,[]),V 0),((1,[]),V 0),((2,[]),boolean),((3,[]),boolean)]
        (Abs (Abs (Abs (Abs t)))) = oR
        ty = V 0
buisson6 = BinAry Apply buisson7 buisson11 g t ty
  where g = [((0,[]),V 0),((1,[False]),V 0),((1,[True]),V 0),((2,[]),boolean),((3,[]),boolean)]
        (Abs (Abs (Abs (Abs (Dup 1 [] t))))) = oR
        ty = V 0
buisson7 = BinAry Apply buisson8 buisson10 g t ty
  where g = [((1,[False]),V 0),((3,[]),boolean)]
        t = (Ind 3 [])¤(Ind 1 [False])
        ty = V 0→V 0
buisson8 = UnAry (ForElim (V 0)) buisson9 g t ty
  where g = [((3,[]),boolean)]
        t = (Ind 3 [])
        ty = V 0→(V 0→V 0)
buisson9 = ZeroAry Vari g t ty
  where g = [((3,[]),boolean)]
        t = Ind 3 []
        ty = FA(V 0→(V 0→V 0))
buisson10 = ZeroAry Vari g t ty
  where g = [((1,[False]),V 0)]
        t = Ind 1 [False]
        ty = V 0
buisson11 = BinAry Apply buisson12 tree4 g t ty
  where g = [((0,[]),V 0),((1,[True]),V 0),((2,[]),boolean)]
        t = ((Ind 2 [])¤(Ind 1 [True]))¤(Ind 0 [])
        ty = V 0
buisson12 = BinAry Apply buisson14 buisson15 g t ty
  where g = [((1,[True]),V 0),((2,[]),boolean)]
        t = ((Ind 2 [])¤(Ind 1 [True]))
        ty = V 0→V 0    
buisson14 = UnAry (ForElim (V 0)) buisson16 g t ty
  where g = [((2,[]),boolean)]
        t = Ind 2 []
        (FA ty)= boolean 
buisson15 = ZeroAry Vari g t ty
  where g = [((1,[True]),V 0)]
        t = Ind 1 [True]
        ty = V 0
buisson16 = ZeroAry Vari g t ty
  where g = [((2,[]),boolean)]
        t = Ind 2 []
        ty= boolean 

-- ==== List of Booleans ===
-- [false] : listBool
forest = UnAry ForIntro forest1 g t ty
  where g = []
        t = singF
        ty = listBool
forest1 = UnAry Abstract  forest2 g t ty
  where g = []
        t = singF
        (FA ty) = listBool        
forest2 = UnAry Abstract  forest3 g t ty
  where g = [((0,[]),boolean → ((V 0)→(V 0)))]
        (Abs t) = singF
        ty = (V 0)→(V 0)
forest3 = BinAry Apply  forest4 forest6 g t ty
  where g = [((0,[]),V 0),((1,[]),boolean → ((V 0)→(V 0)))]
        (Abs (Abs t)) = singF
        ty = V 0
forest4 = BinAry Apply  forest5 bush g t ty
  where g = [((1,[]),boolean → ((V 0)→(V 0)))]
        t = one¤false
        ty = V 0 → V 0
forest5 = ZeroAry Vari g t ty
  where g =  [((1,[]),boolean → ((V 0)→(V 0)))]
        t = one 
        ty = boolean → (V 0 → V 0)
forest6 = ZeroAry Vari g t ty
  where g =  [((0, []), V 0)]
        t = zero
        ty = V 0

-- [1,2]: listNat
wald = UnAry ForIntro wald1 g t ty
  where g = []
        t = doub12
        ty = listNat
wald1 = UnAry Abstract  wald2 g t ty
  where g = []
        t = doub12
        (FA ty) = listNat        
wald2 = UnAry Abstract  wald3 g t ty
  where g = [((0,[]),natural → ((V 0)→(V 0)))]
        (Abs t) = doub12
        ty = (V 0)→(V 0)
wald3 = UnAry Contract wald4 g t ty
  where g = [((0,[]),V 0),((1,[]),natural → ((V 0)→(V 0)))]
        (Abs (Abs t)) = doub12
        ty = V 0
wald4 = BinAry Apply  wald5 wald7 g t ty 
  where g = [((0,[]),V 0),((1,[False]),natural → ((V 0)→(V 0))),((1,[True]),natural → ((V 0)→(V 0)))]
        (Abs (Abs(Dup _ _ t))) = doub12
        ty = V 0
wald5 = BinAry Apply  wald6 arbre g t ty -- OK
  where g = [((1,[False]),natural → ((V 0)→(V 0)))]
        t = (Ind 1 [False])¤ch1
        ty = V 0 → V 0
wald6 = ZeroAry Vari g t ty
  where g =  [((1,[False]),natural → ((V 0)→(V 0)))]
        t =  Ind 1 [False]
        ty = natural → (V 0 → V 0)
wald7 = BinAry Apply  wald8 wald10 g t ty  
  where g = [((0,[]),V 0),((1,[True]),natural → ((V 0)→(V 0)))]
        t = ((Ind 1 [True])¤ch2)¤zero
        ty = V 0
wald8 = BinAry Apply  wald9 arbor g t ty 
  where g = [((1,[True]),natural → ((V 0)→(V 0)))]
        t = (Ind 1 [True])¤ch2
        ty = V 0 → V 0
wald9  = ZeroAry Vari g t ty  
  where g = [((1,[True]),natural → ((V 0)→(V 0)))]
        t = (Ind 1 [True])
        ty = natural → (V 0 → V 0)
wald10 = ZeroAry Vari g t ty
  where g = [((0,[]),V 0)]
        t = zero
        ty = V 0

--- Local Variables:
--- mode: haskell
--- mode: haskell-indentation
--- End:
