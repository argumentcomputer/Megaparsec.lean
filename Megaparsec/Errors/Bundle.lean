import Megaparsec.Errors.StreamErrors
import Megaparsec.ParserState
import YatimaStdLib

namespace Bundle

open Megaparsec.ParserState
open Megaparsec.Errors.StreamErrors

structure ParseErrorBundle {α E : Type u} where
  errors : NEList (ParseError α E)
  posState : PosState S

def hello := "world"
