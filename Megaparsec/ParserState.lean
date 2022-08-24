import Megaparsec.Errors.Result
import Megaparsec.Errors.ParseError
import Megaparsec.Pos

import Straume.Coco
import Straume.Iterator

open Megaparsec.Errors.ParseError
open Megaparsec.Pos

open Straume.Coco
open Straume.Iterator

/-  -/
namespace Megaparsec.ParserState

structure SourcePos where
  name : String
  line : Pos
  column: Pos

-- Pretty-print a `SourcePos`.
def sourcePosPretty : SourcePos → String
  | ⟨n, l, c⟩ => let lcStr := s!"{l.pos}:{c.pos}"
    if n.isEmpty then lcStr else s!"{n}:{lcStr}"

universe u

-- variable (β : Type u)
-- variable (s : Type u) -- [Coco α s] [Iterable α β]
-- variable (E : Type u)

/- Calculates line / column on demand. -/
structure PosState (σ : Type u) where
  input : σ
  offset : Nat
  sourcePos : SourcePos
  tabWidth : Nat
  linePrefix : String

/- Supports parsing by tracking consumed parts of stream and tracking errors. -/
structure State (β σ E : Type u) where
  input       : σ
  offset      : Nat
  posState    : PosState σ
  parseErrors : List (ParseError β E)

-- TODO: DEPENDENT PARSING IN HIGHER UNIVERSES S S
/- A result of evaluation of a particular parser. -/
open Megaparsec.Errors.Result in
structure Reply (β σ γ E : Type u) where
  state    : @State β σ E
  consumed : Bool
  result   : Result β γ E

def longestMatch (s₁ : @State β σ E) (s₂ : @State β σ E) : @State β σ E :=
  match compare s₁.offset s₂.offset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

/- State smart constructor. -/
def initialState (sourceName : String) (xs : σ) : @State β σ E :=
  let p₀ := Pos.mk 0
  let posState := PosState.mk xs 0 (SourcePos.mk sourceName p₀ p₀) 2 ""
  State.mk xs 0 posState []
