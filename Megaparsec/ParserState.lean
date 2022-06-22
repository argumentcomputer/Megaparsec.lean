import Megaparsec.Stream
import Megaparsec.Errors.Result
import Megaparsec.Errors.StreamErrors

namespace ParserState

structure Pos where
  pos : Nat

structure SourcePos where
  sourceName : String
  sourceLine : Pos
  sourceColumn: Pos

structure PosState (S : Type) where
  pstateInput : S
  pstateOffset : Nat
  pstateSourcePos : SourcePos
  pstateLinePrefix : String

structure State (S E : Type) [s : Stream.Stream S] where
  stateInput       : S
  stateOffset      : Nat
  statePosState    : PosState S
  stateParseErrors : List (@StreamErrors.ParseError S E s)

structure Reply (S E A : Type) [Stream.Stream S] where
  state    : State S E
  consumed : Bool
  result   : Result.Result S E A

def longestMatch [Stream.Stream S] (s₁ : State S E) (s₂ : State S E) : State S E :=
  match compare s₁.stateOffset s₂.stateOffset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁


end ParserState
