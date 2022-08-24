import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.ParserState

open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.ParserState

namespace Megaparsec.Err

def Err (m : Type f → Type v) (β σ E : Type u) (ξ : Type f) :=
  (ParseError β E → State β σ E → m ξ)

/-
`withHints hs c` adds hints to “ERROR” continuation that will add given
hints @hs@ to third argument of original continuation c.
-/
def withHints (hs : Hints β)
              (f : Err m β σ γ ξ) : Err m β σ γ ξ :=
  fun e => match e with
  | .trivial pos us hs₀ => f $ .trivial pos us (List.join $ hs₀ :: hs)
  | _ => f e
