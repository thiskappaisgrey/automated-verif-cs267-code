{-# LANGUAGE NoMonomorphismRestriction #-}

module Boolean where

import Data.List (foldl1)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Diagrams.Backend.SVG qualified as TS
import Diagrams.Prelude qualified as P
import Diagrams.TwoD.Layout.Tree qualified as T
import GHC.Show qualified as Show (Show (..))
import TransitionSystem
import Prelude hiding (State)

-- import Diagrams.Prelude (mkWidth)
--
data BVar
  = V Text
  | P BVar
data BForm
  = Var BVar
  | Not BForm
  | And BForm BForm
  | Or BForm BForm
  | BT
  | BF

-- something
instance Show BVar where
  show (V t) = toString t
  show (P t) = show t <> "'"

instance Show BForm where
  show (Var v) = show v
  show (Not b) = "\\lnot " <> show b
  show (And a b) = "(" <> show a <> " \\land " <> show b <> ")"
  show (Or a b) = show a <> " \\lor " <> show b
  show BT = "T"
  show BF = "F"

-- p1 transition system

-- TODO figure out how to do stuff
p1System' :: TransitionSystem
p1System' =
  TransitionSystem
    { states = map State [0 .. 3]
    , transitions = map (bimap State State) [(0, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]
    , labeling = labels
    }
  where
    labels =
      Map.fromList
        [ (State 3, Set.fromList [Prop "p"])
        ]

-- convenience since there's only 1 property? Too lazy to generalize rn

-- there's only 1 property .. tbh

-- turn all variables in a BForm into prime form
prime :: BForm -> BForm
prime (Var (V t)) = Var (P (V t)) -- only  "prime" a var that isn't already primed
prime (Var s) = Var s -- don't prime a var that is already primed
prime (And s1 s2) = And (prime s1) (prime s2)
prime (Not s) = Not (prime s)
prime (Or s1 s2) = Or (prime s1) (prime s2)
prime a = a

primeWith :: BForm -> Text -> BForm -> BForm
primeWith p tv (Var (P (V t)))
  | t == tv = p -- substitute prime with
  | otherwise = Var (P (V t))
primeWith _ _ (Var s) = Var s -- don't primeWith a var that is already primed
primeWith p tv (And s1 s2) = And (primeWith p tv s1) (primeWith p tv s2)
primeWith p tv (Not s) = Not (primeWith p tv s)
primeWith p tv (Or s1 s2) = Or (primeWith p tv s1) (primeWith p tv s2)
primeWith _ _ a = a

-- TODO figure out how to create a BDD diagram
-- TODO pretty sure I can just pattern-match until I find a fixpoint to reduce the diagram into a bdd
-- https://sites.cs.ucsb.edu/~bultan/courses/267/lectures/l5.pdf
-- For each  x
p1BoolEnc :: BForm
p1BoolEnc = p1BoolEnc' |> foldl1 Or

p1BoolEnc' :: [BForm]
p1BoolEnc' = [And (And (boolEnc curr) (hasP curr)) (And (boolEnc next |> prime) (hasP next |> prime)) | (curr, next) <- trans]
  where
    sts = states p1System'
    labs = labeling p1System'
    trans = transitions p1System'

    boolEnc :: State -> BForm
    boolEnc (State 0) = And (Not (Var (V "x"))) (Not (Var (V "y")))
    boolEnc (State 1) = And (Var (V "x")) (Not (Var (V "y")))
    boolEnc (State 2) = And (Not (Var (V "x"))) (Var (V "y"))
    boolEnc (State 3) = And (Var (V "x")) (Var (V "y"))
    boolEnc (State _) = Var (V "invalid")

    -- bOr :: BForm -> BForm -> BForm
    -- bOr b1 b2 = Or b1 b2
    hasP st
      | Just _ <- Map.lookup st labs =
          Var (V "p")
    hasP _ = Not (Var (V "p"))

p1BoolEncT :: BForm
p1BoolEncT = [And (boolEnc curr) (boolEnc next |> prime) | (curr, next) <- trans] |> foldl1 Or
  where
    sts = states p1System'
    labs = labeling p1System'
    trans = transitions p1System'

    boolEnc :: State -> BForm
    boolEnc (State 0) = And (Not (Var (V "x"))) (Not (Var (V "y")))
    boolEnc (State 1) = And (Var (V "x")) (Not (Var (V "y")))
    boolEnc (State 2) = And (Not (Var (V "x"))) (Var (V "y"))
    boolEnc (State 3) = And (Var (V "x")) (Var (V "y"))
    boolEnc (State _) = Var (V "invalid")

    -- bOr :: BForm -> BForm -> BForm
    -- bOr b1 b2 = Or b1 b2
    hasP st
      | Just _ <- Map.lookup st labs =
          Var (V "p")
    hasP _ = Not (Var (V "p"))

-- TODO figure out how to do reductions.
reduceBform :: BForm -> BForm
reduceBform BT = BT
reduceBform BF = BF
reduceBform (Not BT) = BF
reduceBform (Not BF) = BT
reduceBform (Var a) = Var a
reduceBform (And a b)
  | BT <- reduceBform a = reduceBform b
  | BT <- reduceBform b = reduceBform a
  | BF <- reduceBform a = BF
  | BF <- reduceBform b = BF
  | otherwise = And (reduceBform a) (reduceBform b)
reduceBform (Or a b)
  | BT <- reduceBform a = BT
  | BT <- reduceBform b = BT
  | BF <- reduceBform a = reduceBform b
  | BF <- reduceBform b = reduceBform a
  | otherwise = Or (reduceBform a) (reduceBform b)
reduceBform (Not a)
  | BF <- reduceBform a = BT
  | BT <- reduceBform a = BF
reduceBform (Not a) = Not (reduceBform a)

-- reduceBform a = a  -- TODO dc about other stuff for now..
-- TODO figure out how to compute EX
-- existential quantifier elimination
eqe :: Text -> BForm -> BForm
eqe v ex = reduceBform (Or (primeWith BT v ex) (primeWith BF v ex))

bmain :: IO ()
bmain = do
  -- (State 3) p1System' |> show |> putTextLn
  -- p1BoolEnc |> show |> putTextLn
  -- let f = (And (And (Not (Var (V "x"))) (Var (V "y"))) (And  (Var (P (V "x"))) (Var (P (V "y")))))
  -- TODO compute EX(p)
  -- manually substitute "p" with "p'"
  let exP = And p1BoolEnc (Var (P (V "p")))
  putTextLn "running test"
  -- Then eqe out both x and y
  -- exP |>  show |> putTextLn
  -- TODO
  let order = ["x1", "x2", "x3"]
  -- let x1 = subst BT "x" p1BoolEnc |> reduceBform
  -- let x2 = subst BF "x" p1BoolEnc |> reduceBform
  -- x1 |> show |> putTextLn
  -- x2 |> show |> putTextLn
  -- let x'11 = subst BT "x'" x1 |> reduceBform
  -- let x'12 = subst BF "x'" x1 |> reduceBform
  -- x'11 |> show |> putTextLn
  -- x'12 |> show |> putTextLn
  -- p1BoolEnc |> show |> putTextLn
  let b = (Or (And (Var (V "x1")) (Var (V "x2"))) (Var (V "x3")))
  let b2 = And (Not (Var (V "x1"))) (Var (V "x3"))
  let bdd1 = reduce order b
  let bdd2 = reduce order (And b b2)
  bdd1 |> show |> putTextLn
  -- myBdd |> show |> putTextLn
  drawT bdd1 |> TS.renderSVG "./b1.svg" (P.dims2D 100 100)
  drawT bdd2 |> TS.renderSVG "./b3.svg" (P.dims2D 100 100)

-- Var (P (V "y")) |> subst BF "y'" |> show |> putTextLn
myBdd =
  let order = ["x", "x'", "y", "y'"]
   in reduce order p1BoolEncT
reduce :: [Text] -> BForm -> BDD
reduce [] v = bFormToBdd v
reduce (v : s) bform =
  -- compress the nodes as well
  if r1 == r2
    then r1
    else ITE v r1 r2
  where
    l1 = subst BF v bform |> reduceBform
    l2 = subst BT v bform |> reduceBform
    r1 = reduce s l1
    r2 = reduce s l2

-- TODO calculate BDD of my transition system

-- A straight up translation of egglog doesn't work b/c things work top down in Haskell, where as things work bottom up in Egglog
data BDD
  = ITE Text BDD BDD
  | IT
  | IF
  deriving stock (Show, Eq)

bFormToBdd :: BForm -> BDD
bFormToBdd (Var v) = bvarToBdd v
bFormToBdd BF = IF
bFormToBdd BT = IT

-- bFormToBdd a = ITE
-- not sure..
bvarToBdd :: BVar -> BDD
bvarToBdd (V t) = ITE t IF IT
bvarToBdd (P (V t)) = ITE (t <> "'") IT IF
bvarToBdd _ = ITE "invalid" IT IF

ordering :: Text -> Int
ordering "x" = 1
ordering "x'" = 2
ordering "y" = 3
ordering "y'" = 4
ordering _ = 1000

-- compresses And, 1 leve
bAnd :: BDD -> BDD -> BDD
bAnd IT b2 = b2
bAnd IF _ = IF
bAnd b1 IT = b1
bAnd _ IF = IF
bAnd a@(ITE va la ra) b@(ITE vb lb rb) =
  if oa < ob
    then ITE va (bAnd la b) (bAnd ra b)
    else ITE vb (bAnd a lb) (bAnd a rb)
  where
    oa = ordering va
    ob = ordering vb

-- compresses Or 1 level
bOr :: BDD -> BDD -> BDD
bOr IT _ = IT
bOr IF b2 = b2
bOr _ IT = IT
bOr b1 IF = b1
bOr a@(ITE va la ra) b@(ITE vb lb rb) =
  if oa < ob
    then ITE va (bOr la b) (bOr ra b)
    else ITE vb (bOr a lb) (bOr a rb)
  where
    oa = ordering va
    ob = ordering vb
bCompress :: BDD -> BDD
bCompress (ITE v l r) =
  if l == r
    then l
    else (ITE v l r)
bCompress a = a

-- substitute a variable with
subst :: BForm -> Text -> BForm -> BForm
subst p tv (Var (P (V t)))
  | t <> "'" == tv = p -- substitute prime with
  | otherwise = Var (P (V t))
subst p tv x@(Var (V t))
  | t == tv = p -- substitute prime with
  | otherwise = x
subst p tv (And s1 s2) = And (subst p tv s1) (subst p tv s2)
subst p tv (Not s) = Not (subst p tv s)
subst p tv (Or s1 s2) = Or (subst p tv s1) (subst p tv s2)
subst _ _ a = a

-- BDD digram
toBTree :: BDD -> T.BTree String
toBTree IF = T.leaf "F"
toBTree IT = T.leaf "T"
toBTree (ITE v l r) = T.BNode (toString v) (toBTree l) (toBTree r)

drawT :: BDD -> P.Diagram TS.B
drawT bdd =
  P.pad 1.1 . P.centerXY $
    T.renderTree
      ( \n ->
          P.text n P.# P.fontSizeG 0.5
            <> P.circle 0.5 P.# P.fc P.white
      )
      (P.~~)
      myTree
  where
    Just myTree = T.symmLayoutBin' (P.with & T.slVSep P..~ 1.5) (toBTree bdd)

--
-- tree t = drawT (toBTree myBdd) P.# P.centerXY P.# P.pad 1.1
-- \| otherwise =
-- bFormToBDD a = a
