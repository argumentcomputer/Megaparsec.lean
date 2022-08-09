import YatimaStdLib

namespace Megaparsec.Errors

universe u

/-- Error data types, and ways to bundle those together. -/

inductive ErrorItem (T : Type u) where
| tokens (t : NEList T)
| label (l : NEList Char)
| eof

abbrev Hints (T : Type u) := List (List (ErrorItem T))

instance ord2beq_ei [Ord T] [BEq T] : BEq (ErrorItem T) where
  beq (u v : ErrorItem T) :=
    match u, v with
    | .tokens nelᵤ, .tokens nelᵥ => NEList.beq nelᵤ nelᵥ
    | .label nelᵤ, .label nelᵥ => NEList.beq nelᵤ nelᵥ
    | .eof, .eof => true
    | _, _ => false

def errorItemMax [Ord T] [BEq T] (e₁ : ErrorItem T) (e₂ : ErrorItem T) : ErrorItem T :=
  match BEq.beq e₁ e₂ with
    | true => e₂
    | false => e₁

inductive ErrorFancy (E : Type u) where
| fail (msg : String)
| indent (ord : Ordering) (fromPos : Pos) (uptoPos : Pos)
| custom (e : E)

end Errors
