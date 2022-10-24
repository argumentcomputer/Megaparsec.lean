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
def sIO := string_parsecT IO (String × IO.FS.Handle)
def cIO := char_parsecT IO (String × IO.FS.Handle)

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

def testStateT : IO Unit := do

  let sample := "“'if at first you don't succeed, try, try, try again!' -- William E. Hickson” -- Day[9]"

  -- Parsec transformed
  let pt : StateT Nat (ParsecT Id Char String Unit) String := do
    MonadStateOf.set $ 1
    let x0 ← MonadStateOf.get
    let ok ← @string (StateT Nat (ParsecT Id Char String Unit))
                     String String Unit Char
                     statetInstance inferInstance
                     "fail me"
    MonadStateOf.set $ x0 + 41
    pure ok

  let parsed ← parseTestP (StateT.run pt 0) sample

  if parsed.1 then
    IO.println "Error #1 in testStateT"
  else
    IO.println "Success #1 in testStateT"

  let pt : StateT Nat (ParsecT Id Char String Unit) String := do
    MonadStateOf.set $ 1
    let x0 ← StateT.get
    (void (@string (StateT Nat (ParsecT Id Char String Unit))
                   String String Unit Char
                   statetInstance inferInstance
                   "fail me") <|> pure ())
    (MonadStateOf.set $ x0 + 41)
    pure "beep boop"

  let parsed ← parseTestP (StateT.run pt 0) sample

  if !parsed.1 then
    IO.println "Error #2 in testStateT"
  else
    IO.println "Success #2 in testStateT"
    match parsed.2 with
    | .right x =>
      IO.println "Success #3 in testStateT"
      match x.2 with
      | 1 => IO.println "Error #4 in testStateT (1)"
      | 42 => IO.println "Success #4 in testStateT (42)"
      | imp => IO.println s!"Impossible error in testStateT ({imp})"
    | .left _ => IO.println "Error #3 in testStateT"


def main : IO Unit := do
  IO.println "Megaparsec demo!"
  testMyP
  let P := Parsec Char String Unit
  let source := "yatimaaaa!"
  let bad := "yatimAaaa!"
  let yp : P String := string "yatima"
  let x : (Bool × Either Unit String) <- parseTestP yp source
  if x.1 then
    IO.println "Well parsed."
  else
    IO.println "Parse fail."
  let rp src (p := yp) := runParserT' p (initialState "" src)
  let y := rp source
  IO.println "Let's see what isn't parsed after we parsed out `yatima`!"
  IO.println y.1.input

  let ypp := (string "yat") *> (string "ima")
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
  let abcdpnl : Q String := do
    let res1 ← (string "ab")
    let res2 ← (string "cd")
    let _nl ← (string "\n")
    let _eos ← Megaparsec.eof
    pure $ res1 ++ res2
  IO.println "Let's see if @ixahedron's test passes."
  let _ix : (Bool × Either Unit String) ← parseTestTP abcdpnl bh
  let h1 ← IO.FS.Handle.mk (System.mkFilePath ["./Tests", "abcd-no-nl.txt"]) IO.FS.Mode.read false
  let abcd : Q String := (string "abcd" <* MonadParsec.eof S String Unit Char)
  let _ixx : (Bool × Either Unit String) ← parseTestTP abcd ("", h1)

  IO.println "Ergonomic version of @ixahedron's test."
  let file := System.mkFilePath ["./Tests", "abcd.txt"]
  let h ← IO.FS.Handle.mk file IO.FS.Mode.read false
  let buffed := ("", h)
  let res ← parseTP
    (sIO.stringP "ab" *> sIO.stringP "cd" <* cIO.eol <* cIO.eof)
    "abcd.txt"
    buffed
  match res with
  | .right _ => IO.println "Ergonomic version works."
  | .left _ => IO.println "Ergonomic version doesn't work."

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

  IO.println "Option works!"
  let optionAsP : Parsec Char String Unit String := string "hello"
  let optionBsP : Parsec Char String Unit String := string "hellraiser"
  -- optionRes is a successful parse holding .none
  let optionRes ← parseTestP (option optionAsP) "hellraiser"
  let optionDo :=
    option optionAsP *>
    optionBsP

  match optionRes.2 with
  | .right y => match y with
    | .none => IO.println "optionRes: OK"
    | _ => IO.println "optionRes: FAIL"
  | _ => IO.println "optionRes: FAIL(1)"

  -- optionResFall is a successful parse holding "hellraiser"
  let optionResFall ← parseTestP optionDo "hellraiser"

  match optionResFall.2 with
  | .right y => IO.println s!"optionResFall: {y} == hellraiser"
  | _ => IO.println "optionResFall: FAIL"

  -- optionResFall1 is a successful parse holding "hellraiser"
  let optionResFall1 ← parseTestP optionDo "hellohellraiser"
  match optionResFall1.2 with
  | .right y => IO.println s!"optionResFall1: {y} == hellraiser"
  | _ => IO.println "optionResFall1: FAIL"

  testStateT

  IO.println "FIN"
