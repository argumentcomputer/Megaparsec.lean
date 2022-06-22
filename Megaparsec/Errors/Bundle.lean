import Megaparsec.Stream
import Megaparsec.ParserState

namespace Bundle

structure ParseErrorBundle [stream : Stream.Stream S] (E : Type) where
  errors : Util.NonEmptyList (@ParseError S E stream)
  posState : ParserState.PosState S

end Bundle
