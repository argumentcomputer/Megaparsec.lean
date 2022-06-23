import Megaparsec.Stream
import Megaparsec.Errors.Result
import Megaparsec.Errors.StreamErrors

namespace ParserState

structure Pos where
  pos : Nat

structure SourcePos where
  name : String
  line : Pos
  column: Pos

structure PosState (S : Type u) where
  input : S
  offset : Nat
  sourcePos : SourcePos
  linePrefix : String

structure State (S E : Type) [s : Stream.Stream S] where
  input       : S
  offset      : Nat
  posState    : @PosState S
  parseErrors : List (@StreamErrors.ParseError S E s)

structure Reply (S E A : Type) [Stream.Stream S] where
  state    : State S E
  consumed : Bool
  result   : Result.Result S E A

def longestMatch [Stream.Stream S] (s₁ : State S E) (s₂ : State S E) : State S E :=
  match compare s₁.offset s₂.offset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

def initialState {S : Type} [stream : Stream.Stream S]
                 (sourceName : String) (xs : S)
                 : State S E :=
  let p₀ := Pos.mk 0
  let posState := PosState.mk xs 0 (SourcePos.mk sourceName p₀ p₀) ""
  State.mk xs 0 posState []

end ParserState
