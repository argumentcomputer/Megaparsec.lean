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

structure Range where
  first : SourcePos
  last : SourcePos

instance : ToString Range where
  toString x := s!"<{sourcePosPretty x.first},{sourcePosPretty x.last}>"

universe u

-- variable (β : Type u)
-- variable (s : Type u) -- [Coco α s] [Iterable α β]
-- variable (E : Type u)

/- Calculates line / column on demand. -/
structure PosState (℘ : Type u) where
  input : ℘
  offset : Nat
  sourcePos : SourcePos
  tabWidth : Nat
  linePrefix : String

/- Supports parsing by tracking consumed parts of stream and tracking errors. -/
structure State (β ℘ E : Type u) where
  input       : ℘
  offset      : Nat
  posState    : PosState ℘
  parseErrors : List (ParseError β E)

-- TODO: DEPENDENT PARSING IN HIGHER UNIVERSES S S
/- A result of evaluation of a particular parser. -/
open Megaparsec.Errors.Result in
structure Reply (β ℘ γ E : Type u) where
  state    : @State β ℘ E
  consumed : Bool
  result   : Result β γ E

def longestMatch (s₁ : @State β ℘ E) (s₂ : @State β ℘ E) : @State β ℘ E :=
  match compare s₁.offset s₂.offset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

/- State smart constructor. -/
def initialState (sourceName : String) (xs : ℘) : @State β ℘ E :=
  let p₀ := Pos.mk 0
  let posState := PosState.mk xs 0 (SourcePos.mk sourceName p₀ p₀) 2 ""
  State.mk xs 0 posState []
