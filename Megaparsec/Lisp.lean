import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.MonadParsec
import Megaparsec.Parsec
import Megaparsec.ParserState

import YatimaStdLib

open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.Parsec
open Megaparsec.ParserState
open MonadParsec

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
  deriving Repr, BEq

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
  | .list xs => String.intercalate " " $ listLispToList xs

namespace LispParser

variable {m : Type → Type v} {℘ : Type}
  [im : MonadParsec (ParsecT m Char ℘ Unit) ℘ String Unit Char]

def quoteAnyChar := single (i := im) '\\' *> anySingle (i := im)

def stringP := label (i := im) "string" $ do
  let (str : String) ←
    between (im := im) '"' '"' $
      String.mk <$> (manyP m ℘ Char Unit $ quoteAnyChar <|> noneOf (i := im) "\\\"".data)
  pure $ fun r => Lisp.string (str, r)

def commentP := label (i := im) "comment" $ do
  discard $ single (i := im) ';'
  let comment ← manyP m ℘ Char Unit $ noneOf (i := im) "\r\n".data
  discard $ Megaparsec.Char.eol (im := im) <|> (eof (i := im) *> pure "")
  pure $ s!";{String.mk comment}"

def ignore :=
  manyP m ℘ Char Unit $ single (i := im) ' ' *> pure " " <|> commentP

mutual

  partial def lispParser : ParsecT m Char ℘ Unit Lisp :=
    withRange (i := im) String lispExprP

  partial def listP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    label (i := im) "list" $ do
    between (im := im) '(' ')' $ do
      let ys ← sepEndByP m ℘ Char Unit lispParser ignore
      pure $ fun r => Lisp.list (ys, r)

  partial def lispExprP : ParsecT m Char ℘ Unit (Range → Lisp) :=
    choice' [
      attempt (i := im) stringP,
      listP
    ]

end

end LispParser
