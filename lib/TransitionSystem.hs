module TransitionSystem where
import Prelude hiding (State)

type Transitions = [(State, State)]

newtype Prop = Prop Text deriving newtype (Show, Ord, Eq)

type PropExpr = Set Prop -- convert propositions to set

type Label = Map State PropExpr -- TODO the left side of this should be SET instead

data TransitionSystem = TransitionSystem
  { states :: [State],
    transitions :: Transitions,
    labeling :: Label
  }
  deriving stock (Show)
newtype State = State Int deriving newtype (Show, Num, Eq, Ord)
