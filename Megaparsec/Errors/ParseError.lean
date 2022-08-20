import Megaparsec.Errors

open Megaparsec.Errors

namespace Megaparsec.Errors.ParseError

inductive ParseError (β E : Type u) where
  | trivial (offset: Nat)
            (unexpected: Option (ErrorItem β))
            (expected: List (ErrorItem β))
  --                 TODO: I think this should be a Set
  --                                 |
  --                                 v
  | fancy (offset: Nat) (expected: List (ErrorFancy E))

-- Get the offset of a `ParseError`.
def errorOffset : ParseError β E → Nat
  | .trivial offset _ _ => offset
  | .fancy   offset _   => offset

section

variable {β : Type u} [ToString β]
variable {E : Type u} [ToString E]

def NEList.spanToLast (ne : NEList α) : (List α × α) :=
  let rec go
    | .uno x, acc => (acc, x)
    | .cons x xs, acc => go xs (x :: acc)
  go ne []

-- Print a pretty list where items are separated with commas and the word
-- “or” according to the rules of English punctuation.
def orList : NEList String → String
  | .uno x => x
  | .cons x (.uno y) => s!"{x} or {y}"
  | xs => let (lxs, last) := NEList.spanToLast xs
    String.intercalate ", " lxs ++ ", or " ++ last

-- Transform a list of error messages into their textual representation.
def messageItemsPretty (pref : String) (ts : List String) : String :=
  match NEList.nonEmpty ts with
  | .none => ""
  | .some ts => s!"{pref} {orList ts}\n"

-- TODO: orig MP has `messageItemsPretty`, might want to add it. But it uses Set :(
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
        messageItemsPretty "expecting " (List.map toString es)
  | .fancy _ es =>
    if es.isEmpty
      then "unknown fancy parse error"
      else String.intercalate "\n" $ List.map toString es

def parseErrorPretty (e : ParseError β E) : String :=
  s!"offset={errorOffset e}:\n{parseErrorTextPretty e}"

instance : ToString (ParseError β E) where
  toString := parseErrorPretty

end
