import Megaparsec.Stream

namespace Types

/-- Basic datatypes used for Megaparsec defintions -/

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

-- Convention, S is state, E is Error, T is token, A is return type.
-- Convention for optimising currying is to apply E, S then M, and leave A for the last type argument.
-- Except for Result, Reply and ParseError where the order is S E A.

structure State (S E : Type) [s : Stream.Stream S] where
  stateInput       : S
  stateOffset      : Nat
  statePosState    : PosState S
  stateParseErrors : List (@Stream.ParseError S E s)

def longestMatch [Stream.Stream S] (s₁ : State S E) (s₂ : State S E) : State S E :=
  match compare s₁.stateOffset s₂.stateOffset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

inductive Result (S E A : Type) [s : Stream.Stream S] where
| ok (x : A)
| err (e : @Stream.ParseError S E s)

structure Reply (S E A : Type) [Stream.Stream S] where
  state    : State S E
  consumed : Bool
  result   : Result S E A

/-- Monad instance for ParsecT and related utilities -/

-- accHints' hs c results in “OK” continuation that will add given
-- hints @hs@ to third argument of original continuation c
def accHints [Stream.Stream S] {M : Type u → Type v}
               -- | Hints to add
             (hs₁ : Errors.Hints T)
               -- | An “OK” continuation to alter
             (c : A → State S E → Errors.Hints T → M B)
                -- | Altered “OK” continuation
             (x : A) (s : State S E) (hs₂ : Errors.Hints T) : M B :=
  c x s (hs₁ ++ hs₂)

-- withHints' hs c makes “error” continuation c use given hints hs.
def withHints [stream : Stream.Stream S] {M : Type u → Type v}
                -- | Hints to use
              (ps' : Errors.Hints (stream.Token))
                -- | Continuation to influence
              (c : @Stream.ParseError S E stream → State S E → M B)
                -- | First argument of resulting continuation
              (e : @Stream.ParseError S E stream) : State S E → M B :=
  match e with
    | Stream.ParseError.trivial pos us ps => c $ Stream.ParseError.trivial pos us (List.join (ps :: ps'))
    | _ => c e

end Types
