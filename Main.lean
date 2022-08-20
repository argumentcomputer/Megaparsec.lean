import LSpec
import Megaparsec.Common
import Megaparsec.Parsec
import Megaparsec.Errors.Bundle
import YatimaStdLib
import Straume.Coco

open LSpec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Errors.Bundle


instance {α : Type u} : Coco α α where
  coco := id
  replace _ x := x


open Megaparsec.Common

def main : IO Unit := do
  IO.println "Megaparsec demo!"
  let x : (Bool × Either Unit String) <- parseTestP (string' (ParsecT Id Char String Unit) String Unit String Char "yatima") "yatimaaa~"
  if x.1 then
    IO.println "Well parsed."
    match x.2 with
    | .left () => IO.println "Not much got parsed though."
    | .right y => IO.println y
  else
    IO.println "Parse fail."
