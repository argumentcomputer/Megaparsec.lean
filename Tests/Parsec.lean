import LSpec

import Megaparsec
import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Parsec
import Megaparsec.ParserState
import YatimaStdLib

open LSpec

open MonadParsec
open Megaparsec
open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Parsec
open Megaparsec.ParserState

abbrev P := Parsec Char String Unit

/-
  Let's make sure that duplicate errors aren't reported!
  The expected list should include 'yatima' and 'yatima!' one time each,
  instead of 'yatima' being reported twice.
-/
def duplicateErrorsTest : TestSeq :=
  let p  : P String := string "yatima"
  let p' : P String := string "yatima!"
  group "duplicate errors" $
    withExceptError "parsing fails"
      (parse (p <|> p <|> p') "Yatima")
      fun errors =>
        let es := match errors.errors with
          | ⟦.trivial _ _ exs⟧ => exs.toList
          | _ => [] -- impossible case for further testing
        let shouldBe := [
          ErrorItem.tokens (List.toNEList 'y' "atima".data),
          ErrorItem.tokens (List.toNEList 'y' "atima!".data)
        ]
        test "only one parse error" (errors.errors.toList.length = 1) $
        test "two expected values, not three" (es == shouldBe)


def eofTest : TestSeq :=
  withExceptOk "eof: parsing successful"
    (parse (eof : P Unit) "")
    (fun _ => .done)


def stringTest : TestSeq :=
  let yp : P String := string "yatima"
  let yip : P String := string "yat" *> string "ima"
  let runP p src := Id.run $ do
    let (s, res) ← runParserT' p (initialState "" src)
    match res with
    | .error es => pure $ .error es
    | .ok r => pure $ .ok (s, r)

  group "given string: successful parsers" (
    withExceptOk "yatima: parsing successful"
      (parse yp "yatimaaaa!")
      (fun s => test "parsed out 'yatima'" $ s = "yatima") ++

    withExceptOk "parsing 'yatima' from 'yatimaaaa!': parsing successful"
      (runP yp "yatimaaaa!")
      (fun (s, _) => test "leftover string is 'aaa!'" $ s.input = "aaa!") ++

    withExceptOk "parsing 'yat', then 'ima' from 'yatima!': parsing successful"
      (parse yip "yatima!")
      (fun _ => .done)
  )
  ++
  group "given string: failing parsers" (
    withExceptError "yatimA: parsing fails"
      (parse yp "yatimAaaa!")
      (fun _ => .done) ++

    withExceptError "parsing 'yat', then 'ima' from 'yatimA!': parsing fails"
      (parse yip "yatimA!")
      (fun _ => .done)
  )

def charTest : TestSeq :=
  group "Char.lean combinators" $
    withExceptOk "char' is case-insensitive: parsing successful"
      (parse (char' 'Y' : P Char) "yatima!")
      (fun c => test "parsed out 'y'" $ c = 'y') ++

    withExceptOk "eol: parsing successful"
      (parse (eol : P String) "\n")
      (fun s => test "parsed out newline" $ s = "\n")


def optionTest : TestSeq :=
  let pHello? : P (Option String) := option $ string "hello"
  let pHellr? : P (Option String) := option $ string "hellraiser"
  group "option combinator" $
    withExceptOk "none: parsing successful"
      (parse pHello? "hellraiser")
      (fun h? => withOptionNone "none" h? .done) ++

    withExceptOk "raw some: parsing successful"
      (parse pHellr? "hellraiser")
      (fun h? => withOptionSome "some" h? $ fun _ => .done) ++

    withExceptOk "some following none: parsing successful"
      (parse (pHello? *> pHellr?) "hellraiser")
      (fun h? => withOptionSome "some" h? $ fun h =>
        test "holds 'hellraiser'" $ h = "hellraiser") ++

    withExceptOk "some following some: parsing successful"
      (parse (pHello? *> pHellr?) "hellohellraiser")
      (fun h? => withOptionSome "some" h? $ fun h =>
        test "holds 'hellraiser'" $ h = "hellraiser")


def some'Many'Test : TestSeq :=
  let p := string "Yatima"
  group "some' and many' combinators" $
    withExceptOk "many' on empty string: parsing successful"
      (parse (many' p) "")
      (fun l => test "result is empty list" $ l = []) ++

    withExceptOk "many' on matching string: parsing successful"
      (parse (many' p) "YatimaYatimaYat33ma")
      (fun l => test "result is two reads" $ l = ["Yatima", "Yatima"]) ++

    withExceptError "some' on empty string: parsing fails"
      (parse (some' p) "")
      (fun _ => .done) ++

    withExceptOk "some' on matching string: parsing successful"
      (parse (some' p) "YatimaYatimaYat33ma")
      (fun l => test "result is two reads" $ l = ["Yatima", "Yatima"])


def sepEndBy1'Test : TestSeq :=
  group "sepEndBy1' combinator" $
    withExceptOk "parsing successful"
      (parse (sepEndBy1' (string "yatima") (string " ")) "yatima yatima")
      (fun l => test "result is two reads" $ l = ["yatima", "yatima"])


def parsingTest : TestSeq :=
  let laLexer := (string "|" <* (eof *> pure "FIN")) <|> string " "
  let numP := satisfy Char.isDigit >>=
              fun x => pure$ x.val.toNat - '0'.val.toNat
  let p := many' $ numP <* laLexer
  group "simple parsing" $
    withExceptOk "\"3 2 1\": parsing successful"
      (parse p "3 2 1|")
      (fun ns => test "parsed out 3, 2, 1" $ ns = [3,2,1]) ++

    withExceptOk "\"5|\": parsing successful"
      (parse p "5|")
      (fun ns => test "parsed out 5" $ ns = [5]) ++

    withExceptError "\"5\": parsing fails"
      (parse p "5")
      (fun _ => .done) ++

    withExceptError "\"55|\": parsing fails"
      (parse p "55|")
      (fun _ => .done)

def main := lspecIO $
  duplicateErrorsTest ++
  eofTest ++
  stringTest ++
  charTest ++
  optionTest ++
  some'Many'Test ++
  sepEndBy1'Test ++
  parsingTest
