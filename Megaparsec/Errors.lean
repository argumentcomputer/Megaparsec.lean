import YatimaStdLib
import Megaparsec.Pos
import Megaparsec.Printable

open Megaparsec.Pos
open Megaparsec.Printable

namespace Megaparsec.Errors

universe u
universe v

/-- Error data types, and ways to bundle those together. -/

-- Pretty-print an `ErrorItem`.
inductive ErrorItem (β : Type u) where
  | tokens (t : NEList β)
  | label (l : NEList Char)
  | eof

def errorItemLength [Printable β] : ErrorItem β → Nat
  | .tokens t => tokensLength t
  | _ => 1

instance [Printable β] : ToString (ErrorItem β) where
  toString
  | .eof => "end of input"
  | .label t => String.mk t.toList
  | .tokens t => showTokens t

instance [ToString β] : ToString (ErrorItem β) where
  toString
  | .eof => "end of input"
  | .label t => String.mk t.toList
  | .tokens t => match t with
    | ⟦x⟧ => s!"{x}"
    | x :| xs => "\"" ++
      NEList.foldl (fun acc token => s!"{acc}{token}") (toString x) xs ++ "\""


--                    TODO: make this a set
--                             |
--                             v
abbrev Hints (⅌ : Type u) := List (List (ErrorItem ⅌))

variable {γ : Type u} [Ord γ] [BEq γ]

instance ord2beq_ei : BEq (ErrorItem γ) where
  beq (x y : ErrorItem γ) :=
    match x, y with
    | .tokens nelᵤ, .tokens nelᵥ => NEList.beq nelᵤ nelᵥ
    | .label nelᵤ, .label nelᵥ => NEList.beq nelᵤ nelᵥ
    | .eof, .eof => true
    | _, _ => false

inductive ErrorFancy (E : Type u) where
  | fail (msg : String)
  | indent (ord : Ordering) (fromPos : Pos) (uptoPos : Pos)
  | custom (e : E)

-- TODO: the og MP defines a `ShowErrorComponent` type class that has an
-- `errorComponentLen` method that would be used here. However, AFAICT it's
-- set to always return 1 by default.
def errorFancyLength : ErrorFancy E → Nat
  | _ => 1

-- Pretty-print an `ErrorFancy`.
instance [ToString E] : ToString (ErrorFancy E) where
  toString
  | .fail msg => msg
  | .custom e => toString e
  | .indent ord fromPos uptoPos =>
    let rel := match ord with
    | .lt => "less than"
    | .eq => "equal to"
    | .gt => "greater than"
    s!"incorrect indentation (got {uptoPos.pos}, should be {rel} {fromPos.pos})"

end Megaparsec.Errors
