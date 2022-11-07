import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.ParserState

import YatimaStdLib

open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.ParserState

namespace Megaparsec.Err

def Err (m : Type f → Type v) (β ℘ E : Type u) (ξ : Type f) :=
  (ParseError β E → State β ℘ E → m ξ)

/-
`withHints hs c` adds hints to “ERROR” continuation that will add given
hints @hs@ to third argument of original continuation c.
-/
def withHints (hs : Hints β)
              (f : Err m β ℘ E ξ) : Err m β ℘ E ξ :=
  fun e => match e with
  | .trivial pos us hs₀ =>
      -- we insert the given hints into `hs₀`
      let hs' := (List.join hs).foldl .insert hs₀
      f $ .trivial pos us hs'
  | _ => f e
