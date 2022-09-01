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
  [Inhabited ℘]
  [Inhabited (ParsecT m Char ℘ Unit Lisp)]
  [Inhabited (ParsecT m Char ℘ Unit (Range → Lisp))]

mutual
  -- TODO: https://zulip.yatima.io/#narrow/stream/10-lean/topic/_spec_10.20constant.3F/near/19689
  partial def some' (p : ParsecT m Char ℘ Unit x)
                    : ParsecT m Char ℘ Unit (List x) := do
    let y ← p
    let ys ← many p
    pure $ List.cons y ys
  partial def many' (p : ParsecT m Char ℘ Unit x)
                    : ParsecT m Char ℘ Unit (List x) := do
    some' p <|> pure []
end

partial def many1' (p : ParsecT m Char ℘ Unit x)
                   : ParsecT m Char ℘ Unit (List x) :=
  some' m ℘ p

structure LispLinearParsers where
  -- s : StringSimple (P ℘) ℘ Unit := {}
  s := string_parsecT m ℘
  c := char_parsecT m ℘
  quoteAnyChar := c.char '\\' *> c.anySingle
  stringP :=
    s.label "string" $ do
    let (str : String) ←
      between (c.char '"') (c.char '"') $
        String.mk <$> (many $ quoteAnyChar <|> c.noneOf "\\\"".data)
    pure $ fun r => Lisp.string (str, r)
  commentP := s.label "comment" $
    c.char ';' *>
    many' m ℘
      (c.noneOf "\r\n".data) *>
      (c.eol <|> (c.eof *> pure "")) *> pure ';'
  ignore := many' m ℘ (c.char ' ' <|> commentP)

mutual

  -- TODO: https://zulip.yatima.io/#narrow/stream/10-lean/topic/_spec_10.20constant.3F/near/19689
  partial def sepEndBy' (p : ParsecT m Char ℘ Unit x)
                        (sep : ParsecT m Char ℘ Unit s)
                        : ParsecT m Char ℘ Unit (List x) :=
    sepEndBy1' p sep <|> pure []

  partial def sepEndBy1' (p : ParsecT m Char ℘ Unit x)
                         (sep : ParsecT m Char ℘ Unit s)
                         : ParsecT m Char ℘ Unit (List x) := do
    let y ← p
    let ys ← ((sep *> sepEndBy' p sep) <|> pure [])
    pure $ List.cons y ys

  partial def lispParser : ParsecT m Char ℘ Unit Lisp :=
    withRange String lispExprP

  partial def listP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    let p : LispLinearParsers m ℘ := {}
    p.s.label "list" $ do
    between (p.c.char '(') (p.c.char ')') $ do
      let ys ← sepEndBy' lispParser p.ignore
      pure $ fun r => Lisp.list (ys, r)

  partial def lispExprP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    let p : LispLinearParsers m ℘ := {}
    choiceP [
      p.stringP,
      listP
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