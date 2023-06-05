{-# LANGUAGE OverloadedStrings #-}

module Main where
import qualified Data.Map.Strict  as Map
import qualified Data.Set  as Set

import Cleff
import Cleff.Fresh
import Cleff.State
import Cleff.Output
import Cleff.Trace

import Data.Text (Text)
import Flow
import Control.Lens hiding ((|>))

import Control.Monad (forM_)

-- TODO essentially - this is a fixpoint computation
-- TODO keep rewriting the graph until no more nodes / edges can be added

-- TODO represent nodes / edges as integers + have a lookup table / database for rules for expansion
-- TODO Stop expanding when there are no more ruels

-- word is infinite - run is accepting if some accepting states appear in the run infinitely many times
data Buchi = Buchi {
  bstates :: [Int] -- list of states as an integer
  , btransitions :: [(Int, Int, Text)] -- transition w/ label as text
  , binitial :: Int -- intial state
  , baccepting ::  [Int] -- list of accepting states
                   }

-- this is accepting if in the trace
-- there exists one state from each accepting set
-- that appears infinitely

-- this is a labled genbuchi rather than a genbuchi
data GenBuchi = GenBuchi {
  gstates :: [(Int, Text)] -- list of states w/ label
  , gtransitions :: [(Int, Int)] -- transition
  , ginitial :: Int -- intial state
  , gaccepting ::  [[Int]] -- set of accepting sets

                         }

-- TODO
genBuchiToBuchi :: Buchi -> GenBuchi
genBuchiToBuchi = error "unimplemented"

data LTLAtom =
    LTrue
  | LFalse
  | ANot LTLAtom
  | Prop Text deriving (Eq, Ord, Show)

-- instance Show LTLAtom where
--   show (LTrue) = "T"
--   show (LFalse) = "F"
--   show (ANot t) = "!" <> show t
--   show (Prop t) = show t

-- 
data LTLNorm =
  Atomic LTLAtom
  | X LTLNorm
  | U LTLNorm LTLNorm
  | R LTLNorm LTLNorm
  | Or LTLNorm LTLNorm
  | And LTLNorm LTLNorm deriving (Eq, Ord, Show)

-- TODO I can encode this as HTML in the pdf
-- instance Show LTLNorm where
--   show (U t1 t2) = "(" <> show t1 <> " U " <> show t2 <> ")"
--   show (R t1 t2) = "(" <> show t1 <> " R " <> show t2 <>")"
--   show (X t1) = "(" <> " X " <> show t1 <>")"
--   show (Or t1 t2) = "(" <> show t1 <> " OR " <> show t2 <> ")"
--   show (And t1 t2) = "(" <> show t1 <> " AND " <> show t2 <> ")"
--   show (Atomic a) = show a

type LTLSet = Set.Set LTLNorm
type NodeSet = Set.Set Int
data DataItem = DataItem {
  _incoming :: NodeSet -- set of nodes
  , _old :: LTLSet -- set of ltl formulas
  , _next :: LTLSet -- set of ltl formulas
  , _new :: LTLSet
                 } deriving (Eq, Show)
makeLenses ''DataItem
-- TODO make a show instance for dataItem
-- instance Show DataItem where
--   show _ = "unimplmented"

  
type Database = Map.Map Int DataItem -- the "keys" are the nodes
type ExpandEffects = '[Fresh Int, State Database,  Output (String, Database), Trace ]

-- https://en.wikipedia.org/wiki/Linear_temporal_logic_to_B%C3%BCchi_automaton
curr1, next1, curr2 :: LTLNorm -> LTLSet -- (curr1, )
curr1 (f1 `U` f2) = Set.singleton f1
curr1 (f1 `R` f2) = Set.singleton f2
curr1 (f1 `Or` f2) = Set.singleton f2
curr1 _ = error "curr 1 not meant to be called"
  
next1 (f1 `U` f2) = Set.fromList [ (f1 `U` f2) ]
next1 (f1 `R` f2) = Set.fromList [(f1 `R` f2)]
next1 (f1 `Or` f2) = Set.empty
next1 _ = error "next 1 not meant to be called"

curr2 (f1 `U` f2) = Set.singleton f2
curr2 (f1 `R` f2) = Set.fromList [f1, f2]
curr2 (f1 `Or` f2) = Set.singleton f1
curr2 _ = error "curr 1 not meant to be called"


-- setExists :: (a -> Bool) -> Set.Set a -> Bool 
-- setExists pred s =
--   Set.filter pred s |> Set.null

-- Wikipedia algorithm.. not what I wnat actually..
-- expand :: ExpandEffects :>> es => (LTLSet, LTLSet, LTLSet, NodeSet) -> Eff es ()
-- expand (curr, old, nxt, inc)
--   | Set.null curr  =
--     do
--       d <- get @(Database)
--       let f =  [ q | (q, v) <- Map.assocs d, ((v ^. next) == nxt) && ( (v ^. now) == old)] -- |> null
--       if null f |> not then
--         do
--           let newd = foldr (\key acc -> Map.update (\v -> over incoming (\i -> Set.union i inc) v |> Just) key acc) d f
--           output ("curr-null1: " <> show f, newd)
--           trace "---- recursion ended on curr-null1  ----"
--           put newd
--         else do
--               k <- fresh @Int
--               let di = DataItem {
--                     _incoming = inc,
--                     _now = old,
--                     _next = nxt
--                                 }
--               db <- get
--               let newd =  Map.insert k di db
--               output ("curr-null2", newd)
--               put newd
--               "---- recursion ended & made new node " <> show k <> " on curr-null2  ----" |> trace
--               expand (nxt, Set.empty, Set.empty, Set.singleton k)
--   | otherwise =do
--     "input: " <> show (curr, old, nxt, inc) |> trace
--     let list = Set.toList curr 
--     forM_ list (\f -> do
--                   trace "f"
--                   let currn = Set.difference curr (Set.singleton f)
--                   let oldn = Set.union old (Set.singleton f)
--                   -- expandF (curr, old, nxt, inc) f
--                   case f of
--                     (Atomic a) ->
--                       case a of
--                         LFalse -> trace "false.. atomic skipped." >> return ()
--                         _ -> do
--                           if ((negAtom a |> Atomic) `Set.member` oldn) then
--                             trace ( "negation in old: " <> show a <> ", old: " <> show oldn) >>return ()
--                             else
--                             trace ("recursion on atomic: " <> show a)  >> expand (currn, oldn, nxt, inc)
--                     (And f1 f2) -> trace ("And: " <> show (And f1 f2)) -- >> expand (
--                                 -- Set.union currn (Set.fromList [f1, f2] `Set.difference` oldn)
--                                 -- , oldn, nxt, inc)
--                     (X g) ->  trace ("X: " <> show (X g)) -- >> expand (curr, old, nxt `Set.union` Set.singleton g, inc)
--                     _ -> do
--                         trace $ "Other: " <> show f
--                         let c1 = currn `Set.union` (curr1 f `Set.difference` oldn)
--                         let c2 = currn `Set.union` (curr2 f `Set.difference` oldn)
--                         let nxtn = nxt `Set.union` next1 f
--                         trace $ "curr1: " <> show c1
--                         trace $ "next1: " <> show nxtn
--                         trace $ "curr2: " <> show c2
--                         expand(c1, oldn, nxtn, inc)
--                         expand (c2, oldn, nxtn, inc)
--                )
                 

negAtom :: LTLAtom -> LTLAtom
negAtom LFalse = LTrue
negAtom p@(Prop _) = ANot p
negAtom (ANot p) = p
negAtom LTrue = LFalse 



expand :: ExpandEffects :>> es => DataItem -> Eff es ()
expand q
  | (q ^. new) |> null =
      do
      d <- get @(Database)
      let f =  [ k | (k, v) <- Map.assocs d
                 , k /= 0 -- any node that's not the initial node
                 , ((v ^. old) == (q ^. old)) && ( (v ^. next) == (q ^. next))
                 ] 
      if null f |> not then
        (do
          let newd = foldr (\key acc -> Map.update (\v -> over incoming (\i -> Set.union i (q ^. incoming)) v |> Just) key acc) d f
          output ("curr-null1: " <> show f, newd)
          "---- self-looping on: " <> show f <> "  ----" |> trace
          put newd)
        else do
              -- add the new node
              k <- fresh @Int
              let qp = DataItem {
                    _incoming = Set.singleton k,
                    _old = Set.empty,
                    _new = (q ^. next),
                    _next = Set.empty
                                }
              db <- get
              let newd =  Map.insert k q db
              output ("curr-null2", newd)
              put newd
              "---- making new node " <> show k <> "  ----" |> trace
              expand qp
        
        
  | otherwise = do
      let nw =  (q ^. new)
      -- pop an element from the set - guaranteed not to be emtpy
      let f = Set.elemAt 0 nw
      let nws = Set.deleteAt 0 nw

      if (f `Set.member` (q ^. old) ) then expand (set new nws q)
        else expandF q f
  where
    expandF :: ExpandEffects :>> es => DataItem -> LTLNorm -> Eff es ()
    expandF q f@(Atomic a) = do
          if ((negAtom a |> Atomic) `Set.member` (q ^. old)) then
            trace ( "negation in old: " <> show f <> ", old: " <> show (q ^. old)) >>return ()
            else
            trace ("recursion on atomic: " <> show f)  >>
            let qp = DataItem {
                    _incoming = q ^. incoming,
                    _old = (q ^. old) `Set.union` Set.singleton f,
                    _new = (q ^. new) `Set.difference` Set.singleton f,
                    _next = (q ^. next)
                              } in
              expand qp
    expandF q f@(Or h k) = do
            let hok = Set.singleton (h `Or` k)
                q1 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = ((q ^. new) `Set.difference` hok) `Set.union` Set.singleton h,
                      _next = (q ^. next)
                                }
                q2 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = ((q ^. new) `Set.difference` hok) `Set.union` Set.singleton k,
                      _next = (q ^. next)
                                }
            expand q1
            expand q2
    expandF q f@(And h k) = do
            let
              hok = Set.singleton (h `And` k)
              q1 = DataItem {
                    _incoming = q ^. incoming,
                    _old = (q ^. old) `Set.union` hok,
                    _new = ((q ^. new) `Set.difference` hok) `Set.union` Set.fromList [h,k] ,
                    _next = (q ^. next)
                              }
            expand q1
    expandF q f@(X h) = do
            let
              hok = Set.singleton f
              q1 = DataItem {
                    _incoming = q ^. incoming,
                    _old = (q ^. old) `Set.union` hok,
                    _new = ((q ^. new) `Set.difference` hok) `Set.union` Set.fromList [h] ,
                    _next = (q ^. next)
                              }
            expand q1
    expandF q f@(U h k) = do
            let hok = Set.singleton f
                q1 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = (q ^. new) `Set.union` Set.singleton h,
                      _next = (q ^. next) `Set.union` hok
                                }
                q2 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = (q ^. new) `Set.union` Set.singleton k,
                      _next = (q ^. next)
                                }
            expand q1
            expand q2
    expandF q f@(R h k) = do
            let hok = Set.singleton f
                q1 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = (q ^. new) `Set.union` Set.fromList [h,k],
                      _next = (q ^. next)
                                }
                q2 = DataItem {
                      _incoming = q ^. incoming,
                      _old = (q ^. old) `Set.union` hok,
                      _new = (q ^. new) `Set.union` Set.singleton k,
                      _next = (q ^. next) `Set.union` hok
                                }
            expand q1
            expand q2
      
      

-- TODO expand new
runInterpretExpand :: (IOE :> es) => Eff (ExpandEffects ++ es) a -> Eff es ((a, Int), Database)
runInterpretExpand s =  runTraceStdout $ runOutputGraph $  runState Map.empty $ runState 0 $ freshEnumToState $ s
-- expand ((f:currRest), old, next, inc) = return ()
  -- TODO pattern match on "f" and do stuff
createGraph :: ExpandEffects :>> es => LTLNorm -> Eff es ()
createGraph f = do
  k <- fresh @Int
  modify (\m -> Map.insert k (DataItem Set.empty Set.empty Set.empty Set.empty) m)
  -- expand (Set.singleton f, Set.empty, Set.empty, Set.singleton k)
  expand (DataItem {
             _incoming = Set.singleton k
             , _old = Set.empty
             , _new = Set.singleton f
             , _next = Set.empty
                   })
  
-- myMain :: IO ()
-- TODO graph to graphviz
-- steps:
-- 1. each state needs to be labeled using all of the propositions in "Curr" that "agree" (as in, don't include both p and (not p))
-- maybe also show the table as well..?

runOutputGraph :: IOE :> es => Eff (Output (String, Database) ': es) a -> Eff es a
runOutputGraph = interpretIO \case
  Output o ->
    -- error "unimplemented"
    print o
    -- TODO print the graph..
    -- putStrLn "hello"
  
-- printGraph :: ExpandEffects :>> es => Eff es ()
-- printGraph = error "unimplemented"



-- TODO graphElemsToDot - use to expand into dot
-- TODO runGraphviz - to run graphviz

myMain :: IO ()
myMain = runIOE $ do
  (_, db) <- runInterpretExpand $ createGraph ((Atomic (Prop "a")) `U` (Atomic (Prop "b")))
  liftIO $ print db
  return ()
  
-- TODO expand algorithm
main :: IO ()
main = do
  -- let d = Map.fromList [(1, DataItem (Set.fromList []) (Set.fromList [Prop "p"]) (Set.fromList [Prop "p"]))
  --                      , (2, DataItem (Set.fromList []) (Set.fromList []) (Set.fromList [Prop "q"])) ]
  -- let nxt = Set.fromList [Prop "p"]
  -- let old = Set.fromList [Prop "p"]
  -- let f =  [q | (q, v) <- Map.assocs d
  --            , ((v ^. next) == nxt)  && ( (v ^. now) == old)
  --            ]
  myMain
  putStrLn "done" --
  -- print f
  
