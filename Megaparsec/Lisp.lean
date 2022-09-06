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
| list : (List Lisp × Range) → Lisp

private def strToString (sr : (String × Range)) : String := s!"\"{sr.1}\""
private partial def listLispToList (xsr : (List Lisp × Range)) : List String :=
  let ys := match xsr.1 with
    | h :: rest => match h with
      | .string s => (strToString s) :: listLispToList (rest, xsr.2)
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
  | .list xs => unwords $ listLispToList xs

variable (m : Type → Type v) (℘ : Type)
  [MonadParsec (ParsecT m Char ℘ Unit) ℘ String Unit Char]
  [Inhabited (ParsecT m Char ℘ Unit Lisp)]
  [Inhabited (ParsecT m Char ℘ Unit (Range → Lisp))]

mutual
  partial def someP (p : ParsecT m Char ℘ Unit γ) : ParsecT m Char ℘ Unit (List γ) := do
    let y ← p
    let ys ← manyP p
    pure $ y :: ys
  partial def manyP (p : ParsecT m Char ℘ Unit γ) : ParsecT m Char ℘ Unit (List γ) := do
    someP p <|> pure []
  partial def sepEndBy1P (p : ParsecT m Char ℘ Unit γ) (sep : ParsecT m Char ℘ Unit γ') := do
    let y ← p
    let ys ← (sep *> sepEndByP p sep)
    pure $ y :: ys
  partial def sepEndByP (p : ParsecT m Char ℘ Unit γ) (sep : ParsecT m Char ℘ Unit γ') :=
    sepEndBy1P p sep <|> pure []
end

structure LispLinearParsers where
  -- s : StringSimple (P ℘) ℘ Unit := {}
  s := string_parsecT m ℘
  c := char_parsecT m ℘
  quoteAnyChar := c.char '\\' *> c.anySingle
  stringP :=
    s.label "string" $ do
    let (str : String) ←
      between (c.char '"') (c.char '"') $
        String.mk <$> (manyP m ℘ $ quoteAnyChar <|> c.noneOf "\\\"".data)
    pure $ fun r => Lisp.string (str, r)
  commentP := s.label "comment" $
    c.char ';' *>
    manyP m ℘
      ((c.noneOf "\r\n".data) >>= fun x => do
        dbg_trace x
        pure x
      ) *>
      (c.eol <|> (c.eof *> pure ""))
  -- TODO: c.space1 doesn't work for some reason
  -- ignore := (some' ℘ (c.space1 <|> commentP))
  ignore := manyP m ℘ (c.char ' ' <|> (commentP *> c.char ';'))
  -- numP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- identifierP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry
  -- quoteP : Parsec Char ℘ Unit (Range → Lisp) :=
  --   sorry

mutual

  partial def lispParser : ParsecT m Char ℘ Unit Lisp :=
    withRange String lispExprP

  partial def listP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    let p : LispLinearParsers m ℘ := {}
    p.s.label "list" $ do
    between (p.c.char '(') (p.c.char ')') $ do
      let ys ← sepEndByP m ℘ lispParser p.ignore
      pure $ fun r => Lisp.list (ys, r)

  partial def lispExprP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    let p : LispLinearParsers m ℘ := {}
    choice' [
      p.s.attempt p.stringP,
      listP --,
      -- p.s.attempt $ p.numP
    ]

end

structure LispRecursiveParsers where
  lispParser := lispParser m ℘
  lispExprP := lispExprP m ℘
  listP := listP m ℘

structure LispParsers where
  l : LispLinearParsers m ℘ := {}
  r : LispRecursiveParsers m ℘ := {}
  s := l.s
  c := l.c
  quoteAnyChar := l.quoteAnyChar
  stringP := l.stringP
  commentP := l.commentP
  ignore := l.ignore
  listP := r.listP
  lispExprP := r.lispExprP
  lispParser := r.lispParser

def lisp_simple (x : Type)
                [MonadParsec (Parsec Char x Unit) x String Unit Char]
                : LispParsers Id x := {}
def lisp_file : LispParsers IO (String × IO.FS.Handle) := {}
