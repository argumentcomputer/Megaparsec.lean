import Megaparsec.Err
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
-- import Megaparsec.Errors.StateErrors
-- import Megaparsec.Errors.StreamErrors
import Megaparsec.Ok
import Megaparsec.ParserState
import Straume.Chunk
import Straume.Coco
import Straume.Flood
import Straume.Iterator

import YatimaStdLib

namespace Megaparsec.Parsec

universe u

open Megaparsec.Err
open Megaparsec.Errors
-- open Megaparsec.Errors.StreamErrors
open Megaparsec.Ok
open Megaparsec.ParserState

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

def ParsecTF (m : Type u → Type v) (β σ E γ ξ : Type u) :=
  let ok := Ok m β σ γ ξ
  let err := Err m β σ E ξ
  State β σ →
    (Consumed × ok) →
    (Consumed × err) →
    (Empty × ok) →
    (Empty × err) →
    m ξ

/-
Note: `ParsecT m β σ E` (note absence of γ) will have kind `Type u → Type (max u v)`.
It is perfect to define a monad. -/
def ParsecT (m : Type u → Type v) (β σ E γ : Type u) :=
  ∀ (ξ : Type u), ParsecTF m β σ E γ ξ

def runOk (o : Type) {β σ γ E : Type u}
          [Outcome o] [Monad m] : (o × Ok m β σ γ (Reply β σ γ E)) :=
  (Outcome.make, fun y s₁ _ => pure ⟨ s₁, Outcome.consumed? o, .ok y ⟩)

-- TODO: pick two additional letters for unbound module-wise universes
def runErr (o : Type) {β σ γ E : Type u}
           [Outcome o] [Monad m] : (o × Err m β σ E (Reply β σ γ E)) :=
  (Outcome.make, fun err s₁ => pure ⟨ s₁, Outcome.consumed? o, .err err ⟩)

-- TODO: move to Straume
instance : Flood Id α where
  flood x _ := id x

abbrev Parsec := ParsecT Id

def runParsecT {m : Type u → Type v} {β σ E γ : Type u}
               (parser : ParsecT m β σ E γ) (s₀ : State β σ) [Monad m] : m (Reply β σ γ E) :=
  parser (Reply β σ γ E) s₀
         (runOk Consumed) (runErr Consumed)
         (runOk Empty) (runErr Empty)

/- Pure doesn't consume. -/
instance : Pure (ParsecT m β σ E) where
  pure x := fun _ s _ _ ((_ : Empty), f) _ => f x s []

/- Map over happy paths. -/
instance : Functor (ParsecT m β σ E) where
  map φ ta :=
    -- TODO: use projections to update under composition in a less verbose way
    fun xi s ((_: Consumed), f) cerr ((_: Empty), g) eerr =>
      ta xi s (Consumed.mk, (f ∘ φ)) cerr (Empty.mk, (g ∘ φ)) eerr

/- Bind into the happy path, accumulating hints about errors. -/
instance : Bind (ParsecT m β σ E) where
  bind ta φ :=
    fun xi s ((_: Consumed), f) ((_ : Consumed), fe) ((_ : Empty), g) ((_ : Empty), ge) =>

      let mok ψ ψe x s' hs :=
        (φ x) xi s'
              (Consumed.mk, f)
              (Consumed.mk, fe)
              (Empty.mk, accHints hs ψ)
              (Empty.mk, withHints hs ψe)

      ta xi s (Consumed.mk, (mok f fe)) (Consumed.mk, fe) (Empty.mk, (mok g ge)) (Empty.mk, ge)

instance : Seq (ParsecT m β σ E) where
  seq tφ thunk :=
    fun xi s ((_ : Consumed), f) ((_ : Consumed), fe) ((_ : Empty), g) ((_ : Empty), ge) =>

      let mok ψ ψe x s' hs :=
        (thunk ()) xi s'
                   (Consumed.mk, f ∘ x)
                   (Consumed.mk, fe)
                   (Empty.mk, accHints hs (ψ ∘ x))
                   (Empty.mk, withHints hs ψe)

      tφ xi s
         (Consumed.mk, mok f fe)
         (Consumed.mk, fe)
         (Empty.mk, mok g ge)
         (Empty.mk, ge)

instance : Monad (ParsecT m β σ E) := {}
