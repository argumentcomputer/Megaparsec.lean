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

universe u

-- variable (β : Type u)
-- variable (s : Type u) -- [Coco α s] [Iterable α β]
-- variable (E : Type u)

/- Calculates line / column on demand. -/
structure PosState (s : Type u) where
  input : s
  offset : Nat
  sourcePos : SourcePos
  tabWidth : Nat
  linePrefix : String

/- Supports parsing by tracking consumed parts of stream and tracking errors. -/
structure State (β s : Type u) where
  input       : s
  offset      : Nat
  posState    : PosState s
  parseErrors : List (ParseError β s)

-- TODO: DEPENDENT PARSING IN HIGHER UNIVERSES S S
/- A result of evaluation of a particular parser. -/
open Megaparsec.Errors.Result in
structure Reply (β s γ E : Type u) where
  state    : @State β s
  consumed : Bool
  result   : Result β γ E

def longestMatch (s₁ : @State β s) (s₂ : @State β s) : @State β s :=
  match compare s₁.offset s₂.offset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

/- State smart constructor. -/
def initialState (sourceName : String) (xs : s) : @State β s :=
  let p₀ := Pos.mk 0
  let posState := PosState.mk xs 0 (SourcePos.mk sourceName p₀ p₀) 2 ""
  State.mk xs 0 posState []
