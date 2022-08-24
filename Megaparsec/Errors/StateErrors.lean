import Megaparsec.ParserState
import Megaparsec.Errors.StreamErrors
import Megaparsec.Errors

import Straume.Coco
import Straume.Iterator

namespace StateErrors

open Megaparsec.Errors
open Megaparsec.ParserState
open Straume.Coco
open Straume.Iterator

universe u
variable {α : Type u}
variable (s : Type u) [Coco α s] [Iterable α β]
variable (E : Type u)
variable {m : Type u → Type v}

def hello := "world"
