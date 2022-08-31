import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Char
import Megaparsec.String
import Megaparsec.ParserState

open MonadParsec
open Megaparsec.Parsec
open Megaparsec.Common
open Megaparsec.Char
open Megaparsec.String
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

variable (℘ : Type) [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char] [Inhabited ℘]
abbrev P state := Parsec Char state Unit

structure LinearParsers where
  -- s : StringSimple (P ℘) ℘ Unit := {}
  s := string_simple ℘
  c := char_simple ℘
  quoteAnyChar := c.char '\\' *> c.anySingle
  stringP : Parsec Char ℘ Unit (Range → Lisp) :=
    s.label "string" $ do
    let (str : String) ←
      between (c.char '"') (c.char '"') $
        String.mk <$> (many $ quoteAnyChar <|> c.noneOf "\\\"".data)
    pure $ fun r => Lisp.string (str, r)
  commentP := s.label "comment" $
    c.char ';' *>
    many
      (c.noneOf "\r\n".data) *>
      (c.eol <|> (c.eof *> pure "")) *>
      pure Unit.unit
  ignore := many (c.space1 <|> (commentP *> pure "")) *> pure Unit.unit
  -- numP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- identifierP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- quoteP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry

mutual
  partial def lispParser [Inhabited (Parsec Char ℘ Unit Lisp)]
                         [Inhabited (Parsec Char ℘ Unit (Range → Lisp))]
                         : Parsec Char ℘ Unit Lisp :=
    withRange String lispExprP
  partial def lispExprP [Inhabited (Parsec Char ℘ Unit Lisp)]
                        [Inhabited (Parsec Char ℘ Unit (Range → Lisp))]
                        : Parsec Char ℘ Unit (Range → Lisp) :=
    let p : LinearParsers ℘ := {}
    choiceP [
      p.stringP,
      listP --,
      -- p.s.attempt $ p.numP
    ]
  partial def listP [Inhabited (Parsec Char ℘ Unit Lisp)]
                    [Inhabited (Parsec Char ℘ Unit (Range → Lisp))]
                    : Parsec Char ℘ Unit (Range → Lisp) :=
    let s := string_simple ℘
    let p : LinearParsers ℘ := {}
    s.label "list" $ do
    -- let ys ← @sepEndBy (Parsec Char ℘ Unit) Lisp Char instAlternativeParsecT instInhabitedParsecT lispParser (p.ignore *> pure ' ')
    let ys ← sepEndBy lispParser (p.ignore *> pure ' ')
    pure $ fun r => Lisp.list (ys, r)
end

-- def lispParser ℘ [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char] : Parsec Char ℘ Unit Lisp :=
--   withRange String $ lispExprP ℘
