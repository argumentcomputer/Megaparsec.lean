import Megaparsec.Errors.ParseError
import Megaparsec.ParserState
import YatimaStdLib

namespace Megaparsec.Errors.Bundle

open Megaparsec.ParserState
open Megaparsec.Errors.ParseError

structure ParseErrorBundle (β σ E : Type u) where
  errors : NEList (ParseError β E)
  posState : PosState σ

def hello := "world"

open Megaparsec.ParserState in
def toBundle (s : State β σ E) (errs : NEList (ParseError β E))
             : ParseErrorBundle β σ E :=
  ParseErrorBundle.mk errs s.posState
