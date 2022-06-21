import Megaparsec.Util

namespace Errors

/-- Error data types -/

inductive ErrorItem (T : Type) where
| tokens (t : Util.NonEmptyList T)
| label (l : Util.NonEmptyList Char)
| eof

abbrev Hints (T : Type) := List (List (ErrorItem T))

instance ord2beq_ei [Ord T] [BEq T] : BEq (ErrorItem T) where
  beq (u v : ErrorItem T) :=
    match u, v with
    | .tokens nelᵤ, .tokens nelᵥ => Util.ord2beq_nel nelᵤ nelᵥ
    | .label nelᵤ, .label nelᵥ => Util.ord2beq_nel nelᵤ nelᵥ
    | .eof, .eof => true
    | _, _ => false

def errorItemMax [Ord T] [BEq T] (e₁ : ErrorItem T) (e₂ : ErrorItem T) : ErrorItem T :=
  match ord2beq_ei.beq e₁ e₂ with
    | true => e₂
    | false => e₁

inductive ErrorFancy (E : Type) where
| fail (msg : String)
| indent (ord : Ordering) (fromPos : Pos) (uptoPos : Pos)
| custom (e : E)

end Errors