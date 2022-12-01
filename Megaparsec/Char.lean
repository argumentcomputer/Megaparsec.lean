import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Straume.Coco
import Megaparsec.Common
import Megaparsec.ParserState

open MonadParsec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Common
open Megaparsec.ParserState

namespace Megaparsec.Char

universe v

variable {m : Type → Type v} {℘ E α : Type}
         [im : MonadParsec m ℘ α E Char]
         [Alternative m] [SeqLeft m] [SeqRight m]

def char' (x : Char) :=
  choice (i := im) [single (i := im) x.toLower, single (i := im) x.toUpper]

def tab := single (i := im) '\t'

def newline := single (i := im) '\n'

def cr := single (i := im) '\r'

def crlf := attempt (i := im) $
  newline (im := im) *> cr (im := im) *> pure "\r\n"

def eol := label (i := im)
  "end of line" $
  (newline (im := im) *> pure "\n") <|> crlf (im := im)

def between (begin' : Char) (end' : Char) (p : m γ) : m γ :=
  Seq.between (single (i := im) begin') (single (i := im) end') p
