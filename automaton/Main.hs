{-# LANGUAGE OverloadedStrings #-}

module Main where
import qualified Data.Map.Strict  as Map
import qualified Data.Set  as Set

import Cleff
import Cleff.Fresh
import Cleff.State
import Cleff.Output
import Cleff.Trace

import Flow
import Control.Lens hiding ((|>))

import Control.Monad (forM_)

import Data.GraphViz
import Data.GraphViz.Attributes (Labellable)
import Data.GraphViz.Attributes.Complete   (Label(HtmlLabel, StrLabel), Attribute(Label))
import qualified Data.GraphViz.Attributes.HTML as DH
import              Data.Text.Lazy                      (pack)  
-- TODO essentially - this is a fixpoint computation
-- TODO keep rewriting the graph until no more nodes / edges can be added

-- TODO represent nodes / edges as integers + have a lookup table / database for rules for expansion
-- TODO Stop expanding when there are no more ruels

-- word is infinite - run is accepting if some accepting states appear in the run infinitely many times
data Buchi = Buchi {
  bstates :: [Int] -- list of states as an integer
  , btransitions :: [(Int, Int, String)] -- transition w/ label as text
  , binitial :: Int -- intial state
  , baccepting ::  [Int] -- list of accepting states
                   }

-- this is accepting if in the trace
-- there exists one state from each accepting set
-- that appears infinitely

-- this is a labled genbuchi rather than a genbuchi
data GenBuchi = GenBuchi {
  gstates :: [(Int, String)] -- list of states w/ label
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
  | Prop String deriving (Eq, Ord, Show)


-- 
data LTLNorm =
  Atomic LTLAtom
  | X LTLNorm
  | U LTLNorm LTLNorm
  | R LTLNorm LTLNorm
  | Or LTLNorm LTLNorm
  | And LTLNorm LTLNorm deriving (Eq, Ord, Show)

-- TODO I can encode this as HTML in the pdf

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
-- instance Show LTLAtom where
labAtom (LTrue) = "T"
labAtom (LFalse) = "F"
labAtom (ANot t) = "!" <> labAtom t
labAtom (Prop t) = t
-- instance Show LTLNorm where
labNorm (U t1 t2) = "(" <> labNorm t1 <> " U " <> labNorm t2 <> ")"
labNorm (R t1 t2) = "(" <> labNorm t1 <> " R " <> labNorm t2 <>")"
labNorm (X t1) = "(" <> " X " <> labNorm t1 <>")"
labNorm (Or t1 t2) = "(" <> labNorm t1 <> " || " <> labNorm t2 <> ")"
labNorm (And t1 t2) = "(" <> labNorm t1 <> " && " <> labNorm t2 <> ")"
labNorm (Atomic a) = labAtom a

label :: DataItem -> String
label d =
  "new = {" <> n <> "}\n" <>
  "old = {" <> o <> "}\n" <>
  "next = {" <> nxt <> "}\n"
  where
    n = Set.foldr (\val ac -> ac <> labNorm val <> "," ) "" (d ^. new)
    o = Set.foldr (\val ac -> ac <> labNorm val <> "," ) "" (d ^. old)
    nxt = Set.foldr (\val ac -> ac <> labNorm val <> "," ) "" (d ^. next)
instance Labellable DataItem where
  toLabelValue d = label d |> toLabelValue

  
type Database = Map.Map Int DataItem -- the "keys" are the nodes
type ExpandEffects = '[Output (String, Database), State Int, State Database,   Trace ]

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
                 

negAtom :: LTLAtom -> LTLAtom
negAtom LFalse = LTrue
negAtom p@(Prop _) = ANot p
negAtom (ANot p) = p
negAtom LTrue = LFalse 



-- TODO I can show all the steps by outputing the states considered as well
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
          output ("curr-null-self-loop", newd)
          "---- self-looping on: " <> show f <> "  ----" |> trace
          put newd)
        else do
              -- add the new node
              modify (\k -> (k + 1)::Int)
              k <- get @Int
              let qp = DataItem {
                    _incoming = Set.singleton k,
                    _old = Set.empty,
                    _new = (q ^. next),
                    _next = Set.empty
                                }
              db <- get
              let newd =  Map.insert k q db
              output ("curr-null-new", newd)
              put newd
              "---- making new node " <> show k <> "  ----" |> trace
  
              trace "---- recursion on curr-null-new ---"
              output ("curr-null2-exp",  Map.insert (k + 1) qp newd)

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
            return ()
            -- trace ( "negation in old: " <> show f <> ", old: " <> show (q ^. old)) >>return ()
            else (do
                  let qp = DataItem {
                          _incoming = q ^. incoming,
                          _old = (q ^. old) `Set.union` Set.singleton f,
                          _new = (q ^. new) `Set.difference` Set.singleton f,
                          _next = (q ^. next)
                                    } 
                  k <- get @Int
                  db <- get @Database
                  trace "---- recursion on Atomic ---"
                  output ("Atomic",  Map.insert (k + 1) qp db)
                  expand qp)
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
            k <- get @Int
            db <- get @Database
            trace "---- recursion on Or ---"
            output ("Or",  Map.insert (k + 1) q1 db |> Map.insert (k + 1) q2)

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
            k <- get @Int
            db <- get @Database
            trace "---- recursion on And ---"
            output ("And",  Map.insert (k + 1) q1 db)

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
            k <- get @Int
            db <- get @Database
            trace "---- recursion on X ---"
            output ("X",  Map.insert (k + 1) q1 db)
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
            k <- get @Int
            db <- get @Database
            trace "---- recursion on U ---"
            output ("U",  Map.insert (k + 1) q1 db |> Map.insert (k + 2) q2)
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
runInterpretExpand s =  ignoreTrace $   runState Map.empty $ runState 0 $ runOutputGraph $ s
-- expand ((f:currRest), old, next, inc) = return ()
  -- TODO pattern match on "f" and do stuff
createGraph :: ExpandEffects :>> es => LTLNorm -> Eff es ()
createGraph f = do
  k <- get @Int
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

runOutputGraph :: [IOE, State Int] :>> es => Eff (Output (String, Database) ': es) a -> Eff es a
runOutputGraph = interpret \case
  Output (fn, db) -> do
    k <- get @Int
    liftIO $ do
      writeDBToGraph db ("./output" <> "/" <> fn <> "-" <> show k <> ".png")
    -- TODO print the graph..
    -- putStrLn "hello"
  
-- printGraph :: ExpandEffects :>> es => Eff es ()
-- printGraph = error "unimplemented"



-- TODO graphElemsToDot - use to expand into dot
-- TODO runGraphviz - to run graphviz
writeDBToGraph ::  Database -> String -> IO ()
writeDBToGraph db file =
  do
    let graph = Map.assocs db
    print file
    -- print graph
    let l = "a" :: String
  -- reverse the arrow directoin in graphviz
    let edges =  (concatMap (\(k,v) ->  [(i, k, l) | i <- Set.toList (v ^. incoming)]) graph )
    let params = nonClusteredParams { fmtNode= \(_,l) -> [toLabel l] }
    let g = graphElemsToDot params graph edges 
    runGraphviz g Png file
    return ()
-- convert DB into a lgba first
writeDBToGraph' ::  Database -> String -> IO ()
writeDBToGraph' db file =
  do
    let graph = Map.assocs db
    print file
    -- print graph
    let l = "a" :: String
  -- reverse the arrow directoin in graphviz
    let edges =  (concatMap (\(k,v) ->  [(i, k, l) | i <- Set.toList (v ^. incoming)]) graph )
    let params = nonClusteredParams { fmtNode= \(_,l) -> [toLabel  (Set.foldr (\val ac -> ac <> labNorm val <> "," ) "" ((l ^. old) |> Set.filter isAtomic) ) ] }
    let g = graphElemsToDot params graph edges 
    runGraphviz g Png file
    return ()

  
myMain :: IO ()
myMain = runIOE $ do
  -- p U (q ∧ X (¬q)) 
  (_, db) <- runInterpretExpand $ createGraph   ((Atomic (Prop "p")) `U` ((Atomic (Prop "q")) `And` X (Atomic (ANot (Prop "q")))))
  -- liftIO $ putStrLn $ label (db Map.! 1)
  liftIO $ do
    print db
    print "then: "
    writeDBToGraph' db "./output/out.png"
    writeDBToGraph db "./output/out1.png"
  return ()

isAtomic :: LTLNorm -> Bool
isAtomic (Atomic _) = True
isAtomic _ = False
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
  
