import Megaparsec.Errors
import Megaparsec.Printable

open Std (RBSet)

open Megaparsec.Errors
open Megaparsec.Printable

namespace Megaparsec.Errors.ParseError

section

inductive ParseError (β E : Type u) where
  | trivial (offset: Nat)
            (unexpected: Option (ErrorItem β))
            (expected: RBSet (ErrorItem β)
                             (cmp : ErrorItem β → ErrorItem β → Ordering))
  | fancy (offset: Nat) (expected: RBSet (ErrorFancy E)
                             (cmp : ErrorFancy E → ErrorFancy E → Ordering))

/-
  This instance compares two `ParseError`s, completely disregarding the
  comparison function of its `RBSet`s. Use with caution.
-/
instance [BEq β] [BEq E] : BEq (ParseError β E) where beq
  | .trivial o1 u1 e1, .trivial o2 u2 e2 =>
      o1 == o2 && u1 == u2 && e1.toList == e2.toList
  | .fancy o1 e1, .fancy o2 e2 =>
      o1 == o2 && e1.toList == e2.toList
  | _, _ => false

-- Get the offset of a `ParseError`.
def errorOffset : ParseError β E → Nat
  | .trivial offset _ _ => offset
  | .fancy   offset _   => offset

/-
  Because we want to not require any instances in structures and type class
  definitions, we define this not particularly well-defined function that
  merges two sets regardless of `cmp` functions, always merging _into_
  the first `RBSet`, i.e. the result will have `cmp` function of
  the first argument.

  This function is very jackal and ideally should not be used at all.

  TODO: better solution that still doesn't involve `Ord` in `ParseError`?
-/
def mergeSetsAny (t₁ : RBSet α cmp₁) (t₂ : RBSet α cmp₂)
                    : RBSet α cmp₁ :=
  t₂.foldl (init := t₁) .insert

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
def parseErrorTextPretty : ParseError β E → String
  | .trivial _ us es =>
    if us.isNone && es.isEmpty
      then "unknown parse error\n"
      else
        let o := Option.map (fun ei => [toString ei]) us
        messageItemsPretty "unexpected " (o.getD []) ++
        messageItemsPretty "expecting " (List.map toString $ es.toList)
  | .fancy _ es =>
    if es.isEmpty
      then "unknown fancy parse error"
      else String.intercalate "\n" $ List.map toString $ es.toList

def parseErrorPretty (e : ParseError β E) : String :=
  s!"offset={errorOffset e}:\n{parseErrorTextPretty e}"

instance : ToString (ParseError β E) where
  toString := parseErrorPretty

end
