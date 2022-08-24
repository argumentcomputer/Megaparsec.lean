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
  let bad := "yatimAaaa!"
  let yp := string P String "yatima"
  let x : (Bool × Either Unit String) <- parseTestP yp source
  if x.1 then
    IO.println "Well parsed."
  else
    IO.println "Parse fail."
  let rp src (p := yp) := runParserT' p (initialState "" src)
  let y := rp source
  IO.println "Let's see what isn't parsed after we parsed out `yatima`!"
  IO.println y.1.input

  let ypp := (string P String "yat") *> (string P String "ima")
  let yb := rp bad ypp
  IO.println "Let's see how the parser fails."
  match yb.2 with
  | .left peb => IO.println $ ToString.toString peb
  | .right _ => IO.println "Hmm, the parser didn't fail. That's a bug!"
  IO.println "But let's make sure that ypp parser actually works."
  let _yg : (Bool × Either Unit String) ← parseTestP ypp source

  let file := System.mkFilePath ["./Tests", "abcd.txt"]
  let h ← IO.FS.Handle.mk file IO.FS.Mode.read false
  let bh := ("", h)
  let S := (String × IO.FS.Handle)
  let Q := ParsecT IO Char S Unit
  -- let abcdp := (string Q S "abcd" <* MonadParsec.eof S String)
  let abcdpnl := do
    let res1 ← (string Q S "ab")
    let res2 ← (string Q S "cd")
    let _nl ← (string Q S "
")
    let _eos ← (MonadParsec.eof S String)
    pure $ res1 ++ res2
  IO.println "Let's see if @ixhaedron's test passes."
  let _ix : (Bool × Either Unit String) ← parseTestTP abcdpnl bh
  let h1 ← IO.FS.Handle.mk (System.mkFilePath ["./Tests", "abcd-no-nl.txt"]) IO.FS.Mode.read false
  let _ixx : (Bool × Either Unit String) ← parseTestTP (string Q S "abcd" <* MonadParsec.eof S String) ("", h1)
