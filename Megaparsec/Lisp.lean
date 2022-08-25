import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.String
import Megaparsec.ParserState

open MonadParsec
open Megaparsec.Parsec
open Megaparsec.Common
open Megaparsec.String
open Megaparsec.String.Simple
open Megaparsec.ParserState

namespace Megaparsec.Lisp

inductive Number where
| integer : Int → Number
| float : Float → Number
| ratio : (Int × Nat) → Number

instance : ToString Number where
  toString x := match x with
  | .integer i => s!"{i}"
  | .float f => s!"{f}"
  | .ratio (num, denom) => s!"{num}/{denom}"

def specialChars := '"' :: ('\\' :: "()#,'`| ;".data)

inductive Lisp where
| string : (String × Range) → Lisp
| number : (Number × Range) → Lisp
| symbol : (String × Range) → Lisp
| list : (List Lisp × Range) → Lisp

private def strToString (sr : (String × Range)) : String := s!"{sr.1}"
private def numToString (nr : (Number × Range)) : String := s!"{nr.1}"
private def symToString (sr : (String × Range)) : String := match sr.1 with
    | "" => "||"
    | _ => if sr.1.any (specialChars.contains)
           then s!"|{sr.1}|"
           else sr.1
private partial def listLispToList (xsr : (List Lisp × Range)) : List String := match xsr.1 with
| h :: rest => match h with
  | .string s => (strToString s) :: listLispToList (rest, xsr.2)
  | .number n => (numToString n) :: listLispToList (rest, xsr.2)
  | .symbol s => (symToString s) :: listLispToList (rest, xsr.2)
  | .list xsr₁ => (listLispToList xsr₁) ++ listLispToList (rest, xsr.2)
| List.nil => []

-- TODO: Pretty printing?
instance : ToString Lisp where
  toString x := match x with
  | .string s => strToString s
  | .number n => numToString n
  | .symbol s => symToString s
  | .list xs => unwords $ listLispToList xs

def stringP ℘ : Parsec Char ℘ Unit (Range → Lisp) :=
  sorry

def listP ℘ : Parsec Char ℘ Unit (Range → Lisp) :=
  sorry

def numP ℘ : Parsec Char ℘ Unit (Range → Lisp) :=
  sorry

def identifierP ℘ : Parsec Char ℘ Unit (Range → Lisp) :=
  sorry

def quoteP ℘ : Parsec Char ℘ Unit (Range → Lisp) :=
  sorry

def lispExprP ℘ [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char] : Parsec Char ℘ Unit (Range → Lisp) :=
  -- let ps : List (Parsec Char ℘ Unit (Range → Lisp)) := [stringP ℘]
  -- let res : Parsec Char ℘ Unit (Range → Lisp) := choice ps
  choice [
    stringP ℘,
    listP ℘,
    attempt ℘ $ numP ℘
  ]

def lispParser ℘ [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char] : Parsec Char ℘ Unit Lisp :=
  withRange String $ lispExprP ℘
