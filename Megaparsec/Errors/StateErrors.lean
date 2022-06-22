import Megaparsec.ParserState
import Megaparsec.Errors.StreamErrors

namespace StateErrors

-- accHints' hs c results in “OK” continuation that will add given
-- hints @hs@ to third argument of original continuation c
def accHints [Stream.Stream S] {M : Type u → Type v}
               -- | Hints to add
             (hs₁ : Errors.Hints T)
               -- | An “OK” continuation to alter
             (c : A → ParserState.State S E → Errors.Hints T → M B)
                -- | Altered “OK” continuation
             (x : A) (s : ParserState.State S E) (hs₂ : Errors.Hints T) : M B :=
  c x s (hs₁ ++ hs₂)

-- withHints' hs c makes “error” continuation c use given hints hs.
def withHints [stream : Stream.Stream S] {M : Type u → Type v}
                -- | Hints to use
              (ps' : Errors.Hints (stream.Token))
                -- | Continuation to influence
              (c : @StreamErrors.ParseError S E stream → ParserState.State S E → M B)
                -- | First argument of resulting continuation
              (e : @StreamErrors.ParseError S E stream) : ParserState.State S E → M B :=
  match e with
    | StreamErrors.ParseError.trivial pos us ps => c $ StreamErrors.ParseError.trivial pos us (List.join (ps :: ps'))
    | _ => c e

end StateErrors
