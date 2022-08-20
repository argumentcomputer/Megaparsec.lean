import LSpec
import Megaparsec.Common
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.ParserState
import Megaparsec.Errors.Bundle
import YatimaStdLib
import Straume.Coco

open LSpec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Errors.Bundle
open MonadParsec
open Megaparsec.ParserState


instance {α : Type u} : Coco α α where
  coco := id
  replace _ x := x

open Megaparsec.Common

def main : IO Unit := do
  IO.println "Megaparsec demo!"
  let P := Parsec Char String Unit
  let source := "yatimaaaa!"
  let yp := string' P String "yatima"
  let x : (Bool × Either Unit String) <- parseTestP yp source
  if x.1 then
    IO.println "Well parsed."
  else
    IO.println "Parse fail."
  let EB := ParseErrorBundle Char String Unit
  let y : (State Char String Unit × Either EB String) := runParserT' yp (initialState "" source)
  IO.println "Let's see what isn't parsed after we parsed out `yatima`!"
  IO.println y.1.input
