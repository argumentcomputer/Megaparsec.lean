import Megaparsec.Errors
import Megaparsec.Printable
import YatimaStdLib

open Std (RBMap)

open Megaparsec.Errors
open Megaparsec.Printable

namespace Megaparsec.Errors.ParseError

section

inductive ParseError (β E : Type u) where
  | trivial (offset: Nat)
            (unexpected: Option (ErrorItem β))
            (expected: RBMap (ErrorItem β) Unit
                             (cmp : ErrorItem β → ErrorItem β → Ordering))
  | fancy (offset: Nat) (expected: RBMap (ErrorFancy E) Unit
                             (cmp : ErrorFancy E → ErrorFancy E → Ordering))

-- Get the offset of a `ParseError`.
def errorOffset : ParseError β E → Nat
  | .trivial offset _ _ => offset
  | .fancy   offset _   => offset

/-
  Because we want to not require any instances in structures and type class
  definitions, we define this not particularly well-defined function that
  merges two unit maps regardless of `cmp` functions, always merging _into_
  the first `RBMap`, i.e. the result will have `cmp` function of
  the first argument.

  This function is very jackal and ideally should not be used at all.

  TODO: better solution that still doesn't involve `Ord` in `ParseError`?
-/
def mergeKeySetsAny (t₁ : RBMap α Unit cmp₁) (t₂ : RBMap α Unit cmp₂)
                    : RBMap α Unit cmp₁ :=
  t₂.foldl (init := t₁) fun t₁ a b₂ =>
    t₁.insert a <|
      match t₁.find? a with
      | some b₁ => b₁
      | none => b₂

end

section

variable {β : Type u} [Printable β]
variable {E : Type u} [ToString E]

def NEList.spanToLast (ne : NEList α) : (List α × α) :=
  let rec go
    | ⟦x⟧, acc => (acc, x)
    | x :| xs, acc => go xs (x :: acc)
  go ne []

-- Print a pretty list where items are separated with commas and the word
-- “or” according to the rules of English punctuation.
def orList : NEList String → String
  | ⟦x⟧ => x
  | ⟦x,y⟧ => s!"{x} or {y}"
  | xs => let (lxs, last) := NEList.spanToLast xs
    String.intercalate ", " lxs ++ ", or " ++ last

-- Transform a list of error messages into their textual representation.
def messageItemsPretty (pref : String) (ts : List String) : String :=
  match NEList.nonEmpty ts with
  | .none => ""
  | .some ts => s!"{pref} {orList ts}\n"

/-
  Pretty-print a textual part of a `ParseError`, that is, everything
  except for its position. The rendered `String` always ends with a
  newline.
-/
open Std.RBMap in
def parseErrorTextPretty : ParseError β E → String
  | .trivial _ us es =>
    if us.isNone && es.isEmpty
      then "unknown parse error\n"
      else
        let o := Option.map (fun ei => [toString ei]) us
        messageItemsPretty "unexpected " (o.getD []) ++
        messageItemsPretty "expecting " (List.map toString $ toList es.keys)
  | .fancy _ es =>
    if es.isEmpty
      then "unknown fancy parse error"
      else String.intercalate "\n" $ List.map toString $ toList es.keys

def parseErrorPretty (e : ParseError β E) : String :=
  s!"offset={errorOffset e}:\n{parseErrorTextPretty e}"

instance : ToString (ParseError β E) where
  toString := parseErrorPretty

end
