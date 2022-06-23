import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors
import Megaparsec.ParserState
import Megaparsec.Util

namespace Bundle

structure ParseErrorBundle [stream : Stream.Stream S] {E : Type} where
  errors : Util.NonEmptyList (@StreamErrors.ParseError S E stream)
  posState : ParserState.PosState S

def toBundle {S : Type} [stream : Stream.Stream S] {E : Type}
             (s : ParserState.State S E) (errs : Util.NonEmptyList (@StreamErrors.ParseError S E stream))
             : @ParseErrorBundle S stream E :=
  ParseErrorBundle.mk errs s.posState

-- def pretty {S : Type} [stream : Stream.Stream S] {E : Type} (x : @ParseErrorBundle S stream E) : String :=
--   sorry

-- def prettyDo {S : Type} [stream : Stream.Stream S] {E : Type}
--              (drain : @ParseErrorBundle S stream E) (acc : List String)
--              : List String :=
--     match drain.errors with
--     | Util.NonEmptyList.cons x xs =>
--       match xs with
--       | [] => prettyDo xs prettyParserErrorWithOffset
--       | List.cons x' xs' => prettyDo

end Bundle
