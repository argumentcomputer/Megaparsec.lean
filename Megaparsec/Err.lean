import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.ParserState

import YatimaStdLib

open Std (RBMap)

open Std.RBMap (unitMap)

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
      let hs' := unitMap $ List.join hs
      f $ .trivial pos us $ hs₀ ++ hs'
  | _ => f e
