import LSpec
import Megaparsec.Common
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.ParserState
import Megaparsec.Errors.Bundle
import YatimaStdLib
import Straume.Coco
import Megaparsec.Char
import Megaparsec.Lisp
import Megaparsec.String

open LSpec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Errors.Bundle
open MonadParsec
open Megaparsec.ParserState
open Megaparsec.Char
open Megaparsec.Lisp
open Megaparsec.String

open Megaparsec.Common

private def cs : Parsec Char String Unit Char :=
  let cs : CharSimple (Parsec Char String Unit) String Unit := {}
  cs.char' 'y'

def s := string_simple_pure
def c := char_simple_pure

def laLexer : Parsec Char String Unit String :=
  s.lookAhead ((s.stringP "|" <* (c.eol <|> c.eof *> pure "FIN")) <|> s.stringP " ")

def numP : Parsec Char String Unit Nat :=
  (c.oneOf "0123456789".data) >>= fun x => pure $ x.val.toNat - '0'.val.toNat

def myP : Parsec Char String Unit (List Nat) :=
  many' (numP <* laLexer)

def testMyP : IO Unit := do
  -- Succeeds
  IO.println "Successful parsers."
  let (true1, three) ← parseTestP myP "3 2 1"
  let (true2, five) ← parseTestP myP "5|"
  if true1 == true2 && true1 then
    match three with
    | .right (x :: _) => IO.println s!"{x}"
    | _ => IO.println "3 parser fails"
    match five with
    | .right (x :: _) => IO.println s!"{x}"
    | _ => IO.println "5 parser fails"
  -- Fails
  IO.println "Failing parsers."
  let (false1, _notFive) ← parseTestP myP "5"
  let (false2, _notFiftyFive) ← parseTestP myP "55|"
  if false1 == false2 && (!false1) then
    IO.println "The parsers that need to fail failed."

  pure $ Unit.unit


def main : IO Unit := do
  IO.println "Megaparsec demo!"
  testMyP
  let P := Parsec Char String Unit
  let source := "yatimaaaa!"
  let bad := "yatimAaaa!"
  let yp := string P String Unit Char "yatima"
  let x : (Bool × Either Unit String) <- parseTestP yp source
  if x.1 then
    IO.println "Well parsed."
  else
    IO.println "Parse fail."
  let rp src (p := yp) := runParserT' p (initialState "" src)
  let y := rp source
  IO.println "Let's see what isn't parsed after we parsed out `yatima`!"
  IO.println y.1.input

  let ypp := (string P String Unit Char "yat") *> (string P String Unit Char "ima")
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
    let res1 ← (string Q S Unit Char "ab")
    let res2 ← (string Q S Unit Char "cd")
    let _nl ← (string Q S Unit Char "\n")
    let _eos ← (MonadParsec.eof S String Unit Char)
    pure $ res1 ++ res2
  IO.println "Let's see if @ixahedron's test passes."
  let _ix : (Bool × Either Unit String) ← parseTestTP abcdpnl bh
  let h1 ← IO.FS.Handle.mk (System.mkFilePath ["./Tests", "abcd-no-nl.txt"]) IO.FS.Mode.read false
  let _ixx : (Bool × Either Unit String) ← parseTestTP (string Q S Unit Char "abcd" <* MonadParsec.eof S String Unit Char) ("", h1)

  IO.println "We have also done a lot of work to export specified versions of things."
  let _xx : (Bool × Either Unit Char) ← parseTestP cs "Yatima!"

  IO.println "This stuff is also exported for your convenience."
  let _xxx : (Bool × Either Unit Char) ← parseTestP (char_simple_pure.char' 'Y') "yatima!"

  IO.println "Is eol buggy?"
  let _eol ← parseTestP char_simple_pure.eol "\n"

  IO.println "Is eof buggy?"
  let _eof ← parseTestP char_simple_pure.eof ""

  -- LISP!
  let lp : LispLinearParsers Id String := {}

  IO.println "Is many bugged?!"
  let _many : (Bool × Either Unit (List String)) ← parseTestP (many' (lp.s.stringP "Yatima")) ""
  let _many : (Bool × Either Unit (List String)) ← parseTestP (many' (lp.s.stringP "Yatima")) "YatimaYatimaYat33ma"

  IO.println "Is some bugged?!"
  let _some : (Bool × Either Unit (List String)) ← parseTestP (some' (lp.s.stringP "Yatima")) ""
  let _some : (Bool × Either Unit (List String)) ← parseTestP (some' (lp.s.stringP "Yatima")) "YatimaYatimaYat33ma"

  IO.println "Let's check that sepEndBy1' works..."
  let _dbg2 : (Bool × Either Unit (List String)) ← parseTestP (sepEndBy1' (lp.s.stringP "yatima") lp.ignore) "yatima yatima"

  IO.println "Let's see if Lisp sub-parsers work?"
  let _dbg : (Bool × Either Unit (List String)) ← parseTestP (lp.ignore) "   "
  let _dbg1 : (Bool × Either Unit (List String)) ← parseTestP (lp.ignore) "  ; hello, world!"
  if _dbg.1 && _dbg1.1 then
    IO.println "Whitespace and comment works!"
  else
    IO.println "There's a bug."

  IO.println "Let's parse some Lisp?"
  -- let _xxxx : (Bool × Either Unit Lisp) ← parseTestP (lispParser String) "(((\"a\") \"b\")) ; lol)"
  -- let _xxxx : (Bool × Either Unit Lisp) ← parseTestP (lispParser String) "(\"a\" )"
  let _xxxx : (Bool × Either Unit Lisp) ← parseTestP (lispParser Id String) "(\"hello\" (\"beautiful\" \"world\")) ; ())(lol n1 bug ))())"

  IO.println "FIN"
