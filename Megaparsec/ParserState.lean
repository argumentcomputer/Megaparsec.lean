import Megaparsec.Errors.Result
import Megaparsec.Errors.StreamErrors

import Straume.Coco
import Straume.Iterator

open Straume.Coco
open Straume.Iterator

open Megaparsec.Errors.StreamErrors

namespace Megaparsec.ParserState

structure Pos where
  pos : Nat

structure SourcePos where
  name : String
  line : Pos
  column: Pos

universe u
variable {α : Type u}
variable (s : Type u) [Coco α s] [Iterable α β]
variable (E : Type u)

structure PosState where
  input : s
  offset : Nat
  sourcePos : SourcePos
  linePrefix : String

structure State where
  input       : s
  offset      : Nat
  posState    : PosState s
  parseErrors : List (ParseError β s)

open Megaparsec.Errors.Result in
structure Reply where
  state    : @State β s
  consumed : Bool
  result   : Result α E

def longestMatch (s₁ : @State β s) (s₂ : @State β s) : @State β s :=
  match compare s₁.offset s₂.offset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

def initialState (sourceName : String) (xs : s) : @State β s :=
  let p₀ := Pos.mk 0
  let posState := PosState.mk xs 0 (SourcePos.mk sourceName p₀ p₀) ""
  State.mk xs 0 posState []

end ParserState
