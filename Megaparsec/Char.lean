import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Straume.Coco
import Megaparsec.Common
import Megaparsec.String
import Megaparsec.ParserState

open MonadParsec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Common
open Megaparsec.String
open Megaparsec.ParserState

namespace Megaparsec.Char

universe v

variable (m : Type → Type v) (℘ E : Type) (α : Type := String)
         [MonadParsec m ℘ α E Char] [MonadParsec m ℘ String E Char]
         [Alternative m]

structure CharSimple where
  s : StringSimple m ℘ E := {}
  char (x : Char) : m Char := single m ℘ E α x
  char' (x : Char) : m Char := choice ℘ α E Char [ char x.toLower, char x.toUpper ]
  anySingle : m Char := anySingle m ℘ α E
  newline := char '\n'
  cr := char '\r'
  crlf : m String := s.stringP "\r\n"
  eol : m String :=
    MonadParsec.label ℘ α E Char
      "end of line" $
      (newline *> pure "\n") <|> crlf
  eof : m Unit :=
    MonadParsec.eof ℘ α E Char
  satisfy (f : Char → Bool) := satisfy m ℘ α E f
  noneOf (xs : List Char) := noneOf m ℘ α E xs
  oneOf (xs : List Char) := oneOf m ℘ α E xs
  tab : m Char := char '\t'

def char_simple (℘x : Type) [MonadParsec (Parsec Char ℘x Unit) ℘x String Unit Char] : CharSimple (Parsec Char ℘x Unit) ℘x Unit := {}
def char_simple_pure : CharSimple (Parsec Char String Unit) String Unit := {}

def char_parsecT (mx : Type → Type v) (℘x : Type)
                 [MonadParsec (ParsecT mx Char ℘x Unit) ℘x String Unit Char]
                 : CharSimple (ParsecT mx Char ℘x Unit) ℘x Unit := {}
