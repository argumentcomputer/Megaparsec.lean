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
  deriving BEq

instance [Ord β] : Ord (ErrorItem β) where
  compare
    | .tokens t1, .tokens t2 => compare t1 t2
    | .label l1, .label l2 => compare l1 l2
    | .eof, .eof => .eq
    -- tokens are said to be greater than anything
    | .tokens _, _ => .gt
    -- labels are said to be greater than anything but tokens
    | .label _, .tokens _ => .lt
    | .label _, _ => .gt
    -- eof is said to be less than anything
    | .eof, _ => .lt

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

section ErrorFancy

inductive ErrorFancy (E : Type u) where
  | fail (msg : String)
  | indent (ord : Ordering) (fromPos : Pos) (uptoPos : Pos)
  | custom (e : E)
  deriving BEq

private def compareOrderings : Ordering → Ordering → Ordering
  | .gt, .gt => .eq
  | .gt,   _ => .gt
  | .eq, .gt => .lt
  | .eq, .eq => .eq
  | .eq, .lt => .gt
  | .lt, .lt => .eq
  | .lt,   _ => .lt

/-
  A method to compare indent triples for purposes of the `Ord (ErrorFancy E)`
  instance.

  The `.indent` constructor has the following fields (not in this order):
    - `uptoPos : Pos`, the actual indentation level
    - `fromPos : Pos`, the reference indentation level
    - `ord : Ordering`, the difference (greater than, equal, less than) between
    the reference and the actual indentation levels.

  As such, we first compare on the actual levels, then on reference,
  and then, as a last resort, on the difference between them.
-/
private def compareIndents : (Ordering × Pos × Pos) → (Ordering × Pos × Pos)
                           → Ordering
  | (o1, f1, u1), (o2, f2, u2) =>
    match compare u1 u2, compare f1 f2 with
                  -- we compare orderings as that's the last differing parameter
    | .eq, .eq => compareOrderings o1 o2
    | .eq,  fo => fo
    |  fu,   _ => fu

instance [Ord E] : Ord (ErrorFancy E) where
  compare
    | .fail m1, .fail m2 => compare m1 m2
    | .fail _, _ => .gt
    | .custom e1, .custom e2 => compare e1 e2
    | .custom _, _ => .lt
    | .indent o1 f1 u1, .indent o2 f2 u2 =>
        compareIndents (o1, f1, u1) (o2, f2, u2)
    | .indent _ _ _, .fail _ => .lt
    | .indent _ _ _, .custom _ => .gt


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

end ErrorFancy

end Megaparsec.Errors
