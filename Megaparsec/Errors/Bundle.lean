import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors
import Megaparsec.ParserState
import Megaparsec.Util

namespace Bundle

structure ParseErrorBundle [stream : Stream.Stream S] {E : Type} where
  errors : Util.NonEmptyList (@StreamErrors.ParseError S E stream)
  posState : ParserState.PosState S

def toBundle {S : Type} [stream : Stream.Stream S] {E : Type}
             (errs : Util.NonEmptyList (@StreamErrors.ParseError S E stream)) (s : ParserState.State S E)
             : @ParseErrorBundle S stream E :=
  ParseErrorBundle.mk errs s.posState

end Bundle
