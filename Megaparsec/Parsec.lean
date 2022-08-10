import Megaparsec.ParserState
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Errors.StateErrors
import Megaparsec.Errors.StreamErrors
import Straume.Chunk
import Straume.Coco
import Straume.Flood
import Straume.Iterator

import YatimaStdLib

namespace Megaparsec.Parsec

universe u
universe v

open Megaparsec.ParserState
open Megaparsec.Errors
open Megaparsec.Errors.StreamErrors

open Straume.Flood
open Straume.Chunk
open Straume.Coco
open Straume.Iterator

structure Consumed where
structure Empty where

class Outcome (tag : Type) where
  consumed? : Bool
instance : Outcome Consumed where
  consumed? := true
instance : Outcome Empty where
  consumed? := false

/- Adds capability of reporting a successful parse to a monad. -/
def OkT (m : Type u → Type v) (β s : Type u) (γ : Type v) (ξ : Type u) :=
  (γ → State β s → Hints β → m ξ)

/- Adds capability of reporting a failed parse to a monad. -/
def ErrT (m : Type u → Type v) (β s E : Type u) (ξ : Type u) :=
  (ParseError β E → State β s → m ξ)

/-
Note: `ParsecT m β s E γ` is the actual `ParsecT` from the previous code base.
Note: `ParsecT m β s E γ` (note absence of ξ) will have kind `Type u → Type (max u v)`.
It is perfect to define a monad. -/
def ParsecT (m : Type u → Type v) (β s E : Type u) (γ : Type v) (ξ : Type u)
            : Type (max u v) :=
  let ok := OkT m β s γ ξ
  let err := ErrT m β s E ξ
  State β s →
    (Consumed × ok) →
    (Consumed × err) →
    (Empty × ok) →
    (Empty × err) →
    m ξ

def runOkT {o : Type} [Outcome o] : (o × OkT m β s γ ) → m ξ :=
  sorry

-- TODO: move to Straume
-- instance : Flood Id α where
--   flood x _ := id x

-- abbrev Parsec := ParsecT Id

-- -def runParsecT {E : Type} [s : Stream.Stream S] [m : Monad M] {A : Type}
-- -               (parser : @ParsecT S M E s m A) (s₀: ParserState.State S E)
-- -               : M (ParserState.Reply S E A) :=

-- -  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
-- -  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
-- -  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
-- -  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩

-- -  parser.unParser (ParserState.Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

def runParsecT {m : Type u → Type v} {β s E : Type u} {γ : Type v} {ξ : Type u}
               (parser : ParsecT m β s E γ ξ) (s₀ : State β s) :=
  let run_cok  := fun y (s₁ : @State  β s) _h => pure $ Reply.mk (s₁ : State β s) true (.ok y) -- pure ⟨s₁, true,  .ok y⟩
  -- let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  -- let run_eok  := fun y s₁ _h => pure ⟨s₁, false, .ok y⟩
  -- let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  sorry

end Megaparsec.Parsec
