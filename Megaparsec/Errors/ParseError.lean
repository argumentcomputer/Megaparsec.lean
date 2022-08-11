import Megaparsec.Errors

open Megaparsec.Errors

namespace Megaparsec.Errors.ParseError

inductive ParseError (β E : Type u) where
| trivial (offset: Nat)
          (unexpected: Option (ErrorItem β))
          (expected: List (ErrorItem β))
| fancy (offset: Nat) (expected: List (ErrorFancy E))
