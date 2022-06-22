import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors
import Megaparsec.ParserState

namespace Bundle

structure ParseErrorBundle [stream : Stream.Stream S] (E : Type) where
  errors : Util.NonEmptyList (@StreamErrors.ParseError S E stream)
  posState : ParserState.PosState S

end Bundle
