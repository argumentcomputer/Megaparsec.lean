import LSpec

import Megaparsec.Lisp
import Megaparsec.Parsec
import Megaparsec.Printable
import Megaparsec.Streamable

open LSpec

open Megaparsec.Lisp
open Megaparsec.Parsec
open Megaparsec.Printable
open Megaparsec.Streamable
open LispParser

private def parseAndJoin (p : Parsec β ℘ E (List String)) (src : ℘)
                         [ToString E] [Printable β] [Streamable ℘] :=
  match parse p src with
  | .ok xs => String.join xs
  | .error  es => s!"Error: {es}"

def ignoreTest : TestSeq :=
  let commentSrc := "   ; hello, world!"
  group "ignore" $
    test "all spaces" (parseAndJoin ignore "   " = "   ") $
    test "comment" (parseAndJoin ignore commentSrc = s!"{commentSrc}") $
    test "leading" (parseAndJoin ignore "  (hello)" = "  ")

open Megaparsec.ParserState in
open Megaparsec.Pos in
private def r' : Nat → Nat → Range
  | fc, lc => ⟨⟨"", pos1, ⟨fc⟩⟩, ⟨"", pos1, ⟨lc⟩⟩⟩

private def toParseHW :=
  "(\"hello\" (\"beautiful\" \"world\")) ; ())(lol n1 bug ))())"
private def expectedHW : Lisp :=
  .list ([
    .string ("hello", r' 2 9),
    .list ([
      .string ("beautiful", r' 11 22),
      .string ("world", r' 23 30)
    ], r' 10 31)
  ], r' 1 32)

private def toParseA := "\"a\" ;"
private def expectedA : Lisp := .string ("a", r' 1 4)

private def mkLispTest (str : String) (expected : Lisp) : TestSeq :=
  group s!"{str}" $
    withExceptOk "parsing successful" (parse lispParser str)
    fun resulting => test "as expected" (resulting == expected)

def lispTest : TestSeq :=
  group "lisp parsing" $
    mkLispTest toParseA expectedA
    ++ mkLispTest toParseHW expectedHW

def main := lspecIO $
  ignoreTest
  ++ lispTest
