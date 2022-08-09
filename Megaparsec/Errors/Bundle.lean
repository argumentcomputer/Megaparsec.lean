import Megaparsec.Errors.ParseError
import Megaparsec.ParserState
import YatimaStdLib

namespace Megaparsec.Errors.Bundle

open Megaparsec.ParserState
open Megaparsec.Errors.ParseError

structure ParseErrorBundle (β σ E : Type u) where
  errors : NEList (ParseError β E)
  posState : PosState σ

-- Helper that makes necessary functions for `ParseErrorBundle.toErrorString`.
private def makePEBfs [ToString β] [ToString E] : ((String → String) × PosState σ) → ParseError β E → ((String → String) × PosState σ)
  | (o, pst), e =>
    let (msline, pst') := ((.none : Option String), pst)-- reachOffset (errorOffset e) pst
    let epos := pst'.sourcePos
    let offendingLine := match msline with
      | .none => ""
      | .some sline =>
        let elen := match e with
          | .trivial _     none _ => 1
          | .trivial _ (some x) _ => errorItemLength x
          | .fancy   _         xs =>
            xs.foldl (fun acc e => max acc (errorFancyLength e)) 1
        let rpshift := epos.column.pos - 1
        let pointerLen :=
          if rpshift + elen > sline.length
            then sline.length - rpshift + 1
            else elen
        let pointer := String.mk $ List.replicate pointerLen '^'
        let lineNumber := s!"{epos.line.pos}"
        let padding := String.mk $ List.replicate (lineNumber.length + 1) ' '
        let rpadding :=
          if pointerLen > 0 then String.mk $ List.replicate rpshift ' ' else ""
        s!"{padding}|\nlineNumber | {sline}\n{padding}| {rpadding}{pointer}\n"
    let outChunk :=
      s!"\n{sourcePosPretty epos}:\n{offendingLine}{parseErrorTextPretty e}"
    (o ∘ (fun x => outChunk ++ x), pst')

/-
  Pretty-print a `ParseErrorBundle`. All `ParseError`s in the bundle will
  be pretty-printed in order together with the corresponding offending
  lines by doing a single pass over the input stream. The rendered `String`
  always ends with a newline.
-/
instance [ToString β] [ToString E] : ToString (ParseErrorBundle β σ E) where
  toString b :=
    let (r, _) := NEList.foldl makePEBfs (id, b.posState) b.errors
    String.drop (r "") 1

open Megaparsec.ParserState in
def toBundle (s : State β σ E) (errs : NEList (ParseError β E))
             : ParseErrorBundle β σ E :=
  ParseErrorBundle.mk errs s.posState
