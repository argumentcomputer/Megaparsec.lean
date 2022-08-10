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
  make : tag
  consumed? : Bool
instance : Outcome Consumed where
  make := Consumed.mk
  consumed? := true
instance : Outcome Empty where
  make := Empty.mk
  consumed? := false

def Ok (m : Type f → Type v) (β s γ : Type u) (ξ : Type f) :=
  (γ → State β s → Hints β → m ξ)

def Err (m : Type f → Type v) (β s E : Type u) (ξ : Type f) :=
  (ParseError β E → State β s → m ξ)

private def doParsecT (m : Type u → Type v) (β s E γ ξ : Type u) :=
  let ok := Ok m β s γ ξ
  let err := Err m β s E ξ
  State β s →
    (Consumed × ok) →
    (Consumed × err) →
    (Empty × ok) →
    (Empty × err) →
    m ξ

/-
Note: `ParsecT m β s E γ` is the actual `ParsecT` from the previous code base.
Note: `ParsecT m β s E γ` (note absence of ξ) will have kind `Type u → Type (max u v)`.
It is perfect to define a monad. -/
def ParsecT (m : Type u → Type v) (β s E γ : Type u) :=
  ∀ (ξ : Type u), doParsecT m β s E γ ξ

def runOk (o : Type) {β s γ E : Type u}
          [Outcome o] [Monad m] : (o × Ok m β s γ (Reply β s γ E)) :=
  (Outcome.make, fun y s₁ _ => pure ⟨ s₁, Outcome.consumed? o, .ok y ⟩)

-- TODO: pick two additional letters for unbound module-wise universes
def runErr (o : Type) {β s γ E : Type u}
           [Outcome o] [Monad m] : (o × Err m β s E (Reply β s γ E)) :=
  (Outcome.make, fun err s₁ => pure ⟨ s₁, Outcome.consumed? o, .err err ⟩)

-- TODO: move to Straume
instance : Flood Id α where
  flood x _ := id x

abbrev Parsec := ParsecT Id

def runParsecT {m : Type u → Type v} {β s E γ : Type u}
               (parser : ParsecT m β s E γ) (s₀ : State β s) [Monad m] : m (Reply β s γ E) :=
  parser (Reply β s γ E) s₀
         (runOk Consumed) (runErr Consumed)
         (runOk Empty) (runErr Empty)

end Megaparsec.Parsec
