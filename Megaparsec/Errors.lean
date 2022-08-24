import YatimaStdLib
import Megaparsec.Pos

open Megaparsec.Pos

namespace Megaparsec.Errors

universe u
universe v

/-- Error data types, and ways to bundle those together. -/

-- Pretty-print an `ErrorItem`.
inductive ErrorItem (β : Type u) where
  | tokens (t : NEList β)
  | label (l : NEList Char)
  | eof

def errorItemLength : ErrorItem β → Nat
  | .tokens t => t.toList.length
  | _ => 1

-- We have `stringPretty` for String and Char parsing –
-- TODO: define another formatting type class?
instance [ToString β] : ToString (ErrorItem β) where
  toString
  | .eof => "end of input"
  | .label t => String.mk t.toList
  | .tokens t => match t with
    | .uno x => s!"{x}"
    | .cons x xs => "\"" ++
      NEList.foldl (fun acc token => s!"{acc}{token}") (toString x) xs ++ "\""

-- TODO: why are almost all escape sequences unrecognised by Lean?
private def charPretty' : Char → Option String
  -- | '\NUL' => .some "null"
  -- | '\SOH' => .some "start of heading"
  -- | '\STX' => .some "start of text"
  -- | '\ETX' => .some "end of text"
  -- | '\EOT' => .some "end of transmission"
  -- | '\ENQ' => .some "enquiry"
  -- | '\ACK' => .some "acknowledge"
  -- | '\BEL' => .some "bell"
  -- | '\BS' => .some "backspace"
  | '\t' => .some "tab"
  | '\n' => .some "newline"
  -- | '\v' => .some "vertical tab"
  -- | '\f' => .some "form feed"
  | '\r' => .some "carriage return"
  -- | '\SO' => .some "shift out"
  -- | '\SI' => .some "shift in"
  -- | '\DLE' => .some "data link escape"
  -- | '\DC1' => .some "device control one"
  -- | '\DC2' => .some "device control two"
  -- | '\DC3' => .some "device control three"
  -- | '\DC4' => .some "device control four"
  -- | '\NAK' => .some "negative acknowledge"
  -- | '\SYN' => .some "synchronous idle"
  -- | '\ETB' => .some "end of transmission block"
  -- | '\CAN' => .some "cancel"
  -- | '\EM' => .some "end of medium"
  -- | '\SUB' => .some "substitute"
  -- | '\ESC' => .some "escape"
  -- | '\FS' => .some "file separator"
  -- | '\GS' => .some "group separator"
  -- | '\RS' => .some "record separator"
  -- | '\US' => .some "unit separator"
  -- | '\DEL' => .some "delete"
  -- | '\160' => .some "non-breaking space"
  | _ => .none

private def charPretty : Char → String
  | ' ' => "space"
  | ch  => (charPretty' ch).getD $ s!"'{ch}'"

private def stringPretty : NEList Char → String
  | .uno x => charPretty x
  | .cons '\r' (.uno '\n') => "crlf newline"
  | xs =>
    let f c := match charPretty' c with
      | .none => s!"{c}"
      | .some pretty => s!"<{pretty}>"
    s!"\"{String.join $ f <$> xs.toList}\""

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
