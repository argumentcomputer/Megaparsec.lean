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
open Megaparsec.String.Simple
open Megaparsec.ParserState

namespace Megaparsec.Char

universe v

variable (m : Type → Type v) (℘ E : Type) (α : Type := String) [MonadParsec m ℘ α E Char] [Alternative m]

structure CharSimple where
  char (x : Char) : m Char := single m ℘ E α x
  char' (x : Char) : m Char := choiceP ℘ α E Char [ char x.toLower, char x.toUpper ]

instance {α : Type u} : Coco α α where
  coco := id
  replace _ x := x

def char_simple_pure : CharSimple (Parsec Char String Unit) String Unit := {}
