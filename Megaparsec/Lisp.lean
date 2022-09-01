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

private def strToString (sr : (String × Range)) : String := s!"\"{sr.1}\""
private def numToString (nr : (Number × Range)) : String := s!"{nr.1}"
private def symToString (sr : (String × Range)) : String := match sr.1 with
    | "" => "||"
    | _ => if sr.1.any (specialChars.contains)
           then s!"|{sr.1}|"
           else sr.1
private partial def listLispToList (xsr : (List Lisp × Range)) : List String :=
  let ys := match xsr.1 with
    | h :: rest => match h with
      | .string s => (strToString s) :: listLispToList (rest, xsr.2)
      | .number n => (numToString n) :: listLispToList (rest, xsr.2)
      | .symbol s => (symToString s) :: listLispToList (rest, xsr.2)
      | .list xsr₁ => (listLispToList xsr₁) ++ listLispToList (rest, xsr.2)
    | List.nil => []
  if ys == [] then
    []
  else
    List.cons "(" $ ys ++ [")"]

-- TODO: Pretty printing?
instance : ToString Lisp where
  toString x := match x with
  | .string s => strToString s
  | .number n => numToString n
  | .symbol s => symToString s
  | .list xs => unwords $ listLispToList xs

variable (℘ : Type) [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char] [Inhabited ℘]
abbrev P state := Parsec Char state Unit

variable
  [Inhabited (Parsec Char ℘ Unit Lisp)]
  [Inhabited (Parsec Char ℘ Unit (Range → Lisp))]


mutual
  partial def some' (p : Parsec Char ℘ Unit x) [ToString x] : Parsec Char ℘ Unit (List x)  := do
    dbg_trace "* * * * PARSING WITH SOME * * * *"
    let y ← p
    dbg_trace "SUCCESS 1"
    dbg_trace y
    dbg_trace "* SOME → MANY *"
    let ys ← many p
    dbg_trace "SUCCESS 2"
    dbg_trace ys
    dbg_trace "* * RETURNING FROM SOME * *"
    pure $ List.cons y ys
  partial def many' (p : Parsec Char ℘ Unit x) [ToString x] : Parsec Char ℘ Unit (List x) := do
    dbg_trace "* * * * ENTERING MANY * * * *"
    some' p <|> pure []
end
partial def many1' (p : Parsec Char ℘ Unit x) [ToString x] : Parsec Char ℘ Unit (List x) := some' ℘ p

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
    many' ℘
      (c.noneOf "\r\n".data) *>
      (c.eol <|> (c.eof *> pure "")) *> pure ';'
  -- ignore := (some' ℘ (c.space1 <|> commentP))
  ignore := many' ℘ (c.char ' ' <|> commentP)
  -- numP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- identifierP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- quoteP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry

mutual

  partial def sepEndBy' (p : Parsec Char ℘ Unit x) (sep : Parsec Char ℘ Unit s) : Parsec Char ℘ Unit (List x) :=
    sepEndBy1' p sep <|> pure []

  partial def sepEndBy1' (p : Parsec Char ℘ Unit x) (sep : Parsec Char ℘ Unit s) : Parsec Char ℘ Unit (List x) := do
    let y ← p
    let ys ← ((sep *> sepEndBy' p sep) <|> pure [])
    pure $ List.cons y ys

  partial def lispParser : Parsec Char ℘ Unit Lisp :=
    withRange String lispExprP

  partial def listP : Parsec Char ℘ Unit (Range → Lisp) :=
    let s := string_simple ℘
    let c := char_simple ℘
    let p : LinearParsers ℘ := {}
    s.label "list" $ do
    between (c.char '(') (c.char ')') $ do
      let ys ← sepEndBy' lispParser p.ignore
      pure $ fun r => Lisp.list (ys, r)

  partial def lispExprP : Parsec Char ℘ Unit (Range → Lisp) :=
    let p : LinearParsers ℘ := {}
    choiceP [
      p.s.attempt p.stringP,
      listP --,
      -- p.s.attempt $ p.numP
    ]

end
