import Megaparsec.Errors
import Megaparsec.ParserState

open Megaparsec.Errors
open Megaparsec.ParserState

namespace Megaparsec.Ok

def Ok (m : Type f → Type v) (β σ γ : Type u) (ξ : Type f) :=
  (γ → State β σ → Hints β → m ξ)

/-
`accHints hs c` adds hints to “OK” continuation that will add given
hints @hs@ to third argument of original continuation c
-/
def accHints (hs : Hints β)
             (f : Ok m β σ γ ξ) : Ok m β σ γ ξ :=
  fun x s hs₀ => f x s (hs ++ hs₀)
