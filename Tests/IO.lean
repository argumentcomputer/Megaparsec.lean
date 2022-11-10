import LSpec

import Megaparsec
import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.Parsec

open LSpec

open MonadParsec
open Megaparsec
open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.Parsec

abbrev PIO := ParsecT IO Char (String × IO.FS.Handle) Unit

def main := do
  let abcdpnl : PIO String := do
    let res1 ← string "ab"
    let res2 ← string "cd"
    discard $ string "\n" <* Megaparsec.eof
    pure $ res1 ++ res2

  let file := System.mkFilePath ["./Tests", "abcd.txt"]
  let fileNoNL := System.mkFilePath ["./Tests", "abcd-no-nl.txt"]

  let h ← IO.FS.Handle.mk file IO.FS.Mode.read false
  let fIO ← parseT abcdpnl ("", h)

  let hnl ← IO.FS.Handle.mk fileNoNL IO.FS.Mode.read false
  let fnlIO ← parseT (string "abcd" <* eof : PIO String) ("", hnl)

  let h' ← IO.FS.Handle.mk file IO.FS.Mode.read false
  let fIO' ←
    parseT (string "ab" *> string "cd" <* eol <* eof : PIO String) ("", h')

  lspecIO $
    withExceptOk "file, manual newline: parsing successful" fIO
      (fun s => test "parsed out 'abcd'" $ s = "abcd") ++

    withExceptOk "file, no newline: parsing successful" fnlIO
      (fun s => test "parsed out 'abcd'" $ s = "abcd") ++

    withExceptOk "file, newline combinator: parsing successful" fIO'
      (fun s => test "parsed out 'cd'" $ s = "cd")
