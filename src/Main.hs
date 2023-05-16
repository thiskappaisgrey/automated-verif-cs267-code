module Main where

import Boolean qualified
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Main.Utf8 qualified as Utf8
import TransitionSystem
import Prelude hiding (State)

-- TODO prob easier to do stuff with a dictionary instead..

-- problem 1
--
p4System :: TransitionSystem
p4System =
  TransitionSystem
    { states = map State [0 .. 3]
    , transitions = map (bimap State State) [(0, 1), (1, 2), (2, 3), (1, 0), (3, 3)]
    , labeling = labels
    }
  where
    labels =
      Map.fromList
        [ (State 0, Set.fromList [Prop "p"])
        , (State 1, Set.fromList [Prop "p", Prop "q"])
        , (State 2, Set.fromList [Prop "p"])
        , (State 3, Set.fromList [Prop "q"])
        ]

exSystem :: TransitionSystem
exSystem =
  TransitionSystem
    { states = map State [1 .. 4]
    , transitions = map (bimap State State) [(1, 2), (2, 3), (3, 4), (3, 1), (4, 3)]
    , labeling = labels
    }
  where
    labels =
      Map.fromList
        [ (State 1, Set.fromList [])
        , (State 2, Set.fromList [])
        , (State 3, Set.fromList [Prop "p"])
        , (State 4, Set.fromList [Prop "p"])
        ]
nestedSystem :: TransitionSystem
nestedSystem =
  TransitionSystem
    { states = map State [0 .. 2]
    , transitions = map (bimap State State) [(0, 0), (0, 1), (1, 2), (2, 2)]
    , labeling = labels
    }
  where
    labels =
      Map.fromList
        [ (State 0, Set.fromList [])
        , (State 1, Set.fromList [Prop "p"])
        , (State 2, Set.fromList [])
        ]

-- TODO to do model checking, I need to implement EX
-- EX - there exists a next state where "p" is true

transClosure :: Transitions -> State -> [State]
transClosure trns s = [state2 | (state1, state2) <- trns, state1 == s]

-- opposite of trans closure
canReach :: Transitions -> State -> [State]
canReach t s = [s1 | (s1, s2) <- t, s2 == s]

-- set of states that sattisfy a property
sat :: Prop -> TransitionSystem -> Set State
sat p (TransitionSystem sts _ lb) = Set.fromList [s0 | s0 <- sts, lb Map.! s0 |> Set.member p]

-- returns a set of states with the property
ex :: Prop -> TransitionSystem -> Set State
-- (Set State, TransitionSystem)
-- for each state in the transitive colusure of
ex p (TransitionSystem sts trns lb) =
  Set.fromList [s0 | s0 <- sts, transClosure trns s0 |> map (\s -> lb Map.! s |> Set.member p) |> or]

-- returns a new transition system with the states labeled
ex' :: Prop -> TransitionSystem -> TransitionSystem
ex' p@(Prop pt) t@(TransitionSystem sts trns lb) = TransitionSystem sts trns lb'
  where
    lb' = foldr (Map.adjust (Set.insert (Prop ("ex " <> pt)))) lb l
    l = ex p t

-- [ | state <- sts]
-- mu calculus - maybe just do it without fixpoints?
-- and call "fix" on the formula?

data Mu
  = P (Set State)
  | Var Text
  | Fix Text (Set State) Mu
  | Or Mu Mu
  | And Mu Mu
  | Not Mu
  | -- TODO I need to be able to um.. get the variable from fix in the formula..
    Ex Mu -- a property is just a set of states that satisfy the property
  deriving stock (Show)

-- Fix (Or (P p) (Ex p (ef p)))

-- TODO figure out how to do nested fixpoints..

-- monadic fix

type MuM = StateT (Map Text (Set State)) (Reader TransitionSystem)

-- interprets a formula into a set of states
-- TODO Maybe I can also use a ReaderT or Reader alg-eff?
interpretMu :: Mu -> MuM (Set State)
interpretMu (P sts) = return sts -- a "property" is just passed a set of states
interpretMu (Or s1 s2) = Set.union <$> interpretMu s1 <*> interpretMu s2
interpretMu (And s1 s2) = Set.intersection <$> interpretMu s1 <*> interpretMu s2
interpretMu (Ex s) = do
  t <- ask
  sts <- interpretMu s
  let ex = concat [canReach (transitions t) s0 | s0 <- Set.toList sts] |> Set.fromList
  return (trace ("ex: " <> show s <> ", " <> show ex) ex)
interpretMu (Var t) = do
  m <- get
  let v = m Map.! t
  return (trace (show t <> "is: " <> show v) v) -- it'll error if the var is unbound but whatever
  -- depends whether greatest or smallest, I guess?
  -- least fixpoint
interpretMu (Fix var arg f) = do
  modify (Map.insert var arg) -- set the var to empty
  new <- interpretMu (trace (show f) f)
  if trace ("fix new: " <> show new) new == arg then return arg else interpretMu (Fix var new f)
interpretMu (Not m) = do
  s <- interpretMu m
  t <- ask
  let sts = Set.fromList $ states t
  let not = Set.difference sts s
  return (trace ("not: " <> show m <> " , " <> show not) not)

runMu :: TransitionSystem -> MuM (Set State) -> Set State
runMu t f = fst $ runReader (runStateT f Map.empty) t

ef :: TransitionSystem -> Set State -> Set State
ef t p = runMu t $ interpretMu $ Fix "y" Set.empty (Or (P p) (Ex (Var "y")))
eg :: TransitionSystem -> Set State -> Set State
eg t p = runMu t $ interpretMu $ Fix "y" Set.empty (And (P p) (Ex (Var "y")))

egf :: TransitionSystem -> Set State -> Set State
egf t p =
  runMu t $
    interpretMu $
      Fix
        "y"
        (states t |> Set.fromList)
        ( Fix
            "z"
            Set.empty
            (And (Or (P p) (Ex (Var "z"))) (Ex (Var "y")))
        )

-- ef t p = runReader $ (runStateT $ interpretMu $ Fix "y" (Or (P p) (Ex (Var "y")))) t

-- using "Prop" as string is a bit more complicate..

-- the "inner" loop is really a state that goes to the states from "p"

-- pass in (sat p t) to start off?
ef' :: Set State -> TransitionSystem -> Set State
ef' p t = if n == trace (show p) p then n else next
  where
    -- this needs to be all of the states that can reach the states in p
    e = concat [canReach (transitions t) s0 | s0 <- Set.toList p] |> Set.fromList
    n = Set.union p e
    next = Set.union n (ef' n t)

-- recurse...???
eg' :: Set State -> TransitionSystem -> Set State
eg' p t = if n == trace (show p) p then n else next
  where
    -- this skips the first iteration.. the other one also skips the first iteration

    -- this needs to be all of the states that can reach the states in p
    e = concat [canReach (transitions t) s0 | s0 <- Set.toList p] |> Set.fromList
    n = Set.intersection p e
    next = Set.intersection n (ef' n t)

-- recurse...???
-- AX = not EX (not p)
ax :: Mu -> Mu
ax p = Not (Ex (Not p))

-- We can use "disjoint" with the set of all states to get "not"

-- also nested fixpoints, not sure how to do that yet?

--  I can just pass in "q" to start off the recursion

-- TODO convert a transition system into a boolean formula - and print it out using diagrams

{- |
 Main entry point.

 The `, run` script will invoke this function.
-}
main :: IO ()
main = do
  -- Boolean.bmain
  -- greatest fixpoint
  let p = P (sat (Prop "p") p4System)
  let q = P (sat (Prop "q") p4System)

  let f1 = Fix "y" (states p4System |> Set.fromList) (And p (Ex (Var "y")))
  let f2 = Fix "y" Set.empty (Or q (And p (ax (Var "y"))))
  let f3 = Fix "y" Set.empty (Fix "z" (states p4System |> Set.fromList) (Or (And q (Ex (Var "z"))) (Ex (Var "y"))))
  putTextLn "hello"
  -- runMu p4System (interpretMu f1) |> show |> putTextLn
  -- runMu p4System (interpretMu f2) |> show |> putTextLn
  runMu p4System (interpretMu f3) |> show |> putTextLn

-- egf  nestedSystem (sat (Prop "p") nestedSystem) |> show |> putTextLn
-- runMu nestedSystem (interpretMu (Not (P (sat (Prop "p") nestedSystem)))) |> show |> putTextLn
-- runMu p4System (interpretMu (And (P (sat (Prop "p") p4System)) (Ex (Var "")))) |> show |> putTextLn
--     -- putTextLn "---"
-- eg'   (sat (Prop "p") exSystem) p1System |> show |> putTextLn

-- transClosure (transitions p1System) (State 3) |> show |> putTextLn
