import Megaparsec.Errors.ParseError
import Megaparsec.ParserState
import YatimaStdLib

namespace Bundle

open Megaparsec.ParserState
open Megaparsec.Errors.ParseError

structure ParseErrorBundle {α E : Type u} where
  errors : NEList (ParseError α E)
  posState : PosState S

def hello := "world"
