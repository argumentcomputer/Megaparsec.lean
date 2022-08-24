import Megaparsec.Err
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Errors.StreamErrors
-- import Megaparsec.Errors.StateErrors
-- import Megaparsec.Errors.StreamErrors
import Megaparsec.Ok
import Megaparsec.ParserState
import Straume
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

open Straume
open Straume.Flood
open Straume.Chunk
open Straume.Coco
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection

structure Consumed where
structure Empty where

class Outcome (tag : Type) where
  make : tag
  consumed? : Bool
  U : tag → tag → tag := fun x _ => x
instance : Outcome Consumed where
  make := Consumed.mk
  consumed? := true
instance : Outcome Empty where
  make := Empty.mk
  consumed? := false

def ParsecTF (m : Type u → Type v) (β σ E γ ξ : Type u) :=
  let ok := Ok m β σ E γ ξ
  let err := Err m β σ E ξ
  State β σ E →
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
          [Outcome o] [Monad m] : (o × Ok m β σ E γ (Reply β σ γ E)) :=
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
               (parser : ParsecT m β σ E γ) (s₀ : State β σ E) [Monad m] : m (Reply β σ γ E) :=
  parser (Reply β σ γ E) s₀
         (runOk Consumed) (runErr Consumed)
         (runOk Empty) (runErr Empty)

/- Pure doesn't consume. -/
instance : Pure (ParsecT m β σ E) where
  pure x := fun _ s _ _ ((_ : Empty), f) _ => f x s []

/- Map over happy paths. -/
instance : Functor (ParsecT m β σ E) where
  map φ ta :=
    fun xi s cok cerr eok eerr =>
      ta xi s (cok.1, (cok.2 ∘ φ)) cerr (eok.1, (eok.2 ∘ φ)) eerr

/- Bind into the happy path, accumulating hints about errors. -/
-- TODO: use functors over (x, y) to update parsecs.
open Outcome in
instance : Bind (ParsecT m β σ E) where
  bind ta φ :=
    fun xi s cok cerr eok eerr =>

      let mok ψ ψe x s' hs :=
        (φ x) xi s'
              cok
              cerr
              (eok.1, accHints hs ψ)
              (eerr.1, withHints hs ψe)

      ta xi s (U cok.1 cerr.1, mok cok.2 cerr.2)
              cerr
              (U eok.1 eerr.1, mok eok.2 eerr.2)
              eerr

open Outcome in
instance : Seq (ParsecT m β σ E) where
  seq tφ thunk :=
    fun xi s cok cerr eok eerr =>

      let mok ψ ψe x s' hs :=
        (thunk ()) xi s'
                   (cok.1, cok.2 ∘ x)
                   cerr
                   (eok.1, accHints hs (ψ ∘ x))
                   (eerr.1, withHints hs ψe)

      tφ xi s
         (U cok.1 cerr.1, mok cok.2 cerr.2)
         cerr
         (U eok.1 eerr.1, mok eok.2 eerr.2)
         eerr

instance : Monad (ParsecT m β σ E) := {}

/- Second-biased way to return a state with the most processed tokens. -/
def longestMatch (s₀ : State β σ E) (s₁ : State β σ E) : State β σ E :=
  if s₀.offset > s₁.offset then s₀ else s₁

open StreamErrors in
open Outcome in
instance : Alternative (ParsecT m β σ E) where
  failure := fun _ s _ _ _ eerr => eerr.2 (.trivial s.offset Option.none []) s
  orElse guess thunk :=
    fun xi s cok cerr eok eerr =>
      let fallback err ms :=
        let nge ψ err' s' := ψ (mergeErrors err' err) (longestMatch ms s')
        let ng x s' hs := eok.2 x s' (toHints s'.offset err ++ hs)
        (thunk ()) xi s cok (cerr.1, nge cerr.2) (eok.1, ng) (eerr.1, nge eerr.2)
    guess xi s cok cerr eok (eerr.1, fallback)

---=========================================================--
---================= IMPORTANT FUNCTIONS ===================--
---=========================================================--

open Megaparsec.Errors.Bundle

/- Extracts the end result from ParsecT run and presents it as a tuple under inner monad. -/
def runParserT' {m : Type u → Type v} {β σ E γ : Type u}
                (p : ParsecT m β σ E γ) (s₀ : State β σ E) [Monad m]
                : m (State β σ E × (Either (ParseErrorBundle β σ E) γ)) := do
  let reply ← runParsecT p s₀
  let s₁ := reply.state
  pure $
    match reply.result with
    | .ok x =>
      match NEList.nonEmpty $ s₁.parseErrors with
      | .none => (s₁, Either.right x)
      | .some pes => (s₁, .left $ toBundle s₀ pes)
    | .err e => (s₁, .left (toBundle s₀ $ List.toNEList e s₁.parseErrors))

def parseTestTP {m : Type → Type v} {β σ E : Type} {γ : Type}
                (p : ParsecT m β σ E γ) (xs : σ) (srcName := "(test run)") [ToString E] [ToString β] [ToString γ] [Monad m] [MonadLiftT m IO]
                : IO (Bool × Either Unit γ) := do
  let reply ← liftM $ runParserT' p (initialState srcName xs)
  match reply.2 with
  | .left e => IO.println e >>= fun _ => pure $ (false, Either.left ())
  | .right y => IO.println y >>= fun _ => pure $ (true, Either.right y)

/- Extracts the end result from Parsec run and presents it as a tuple as is (under Id monad). -/
def runParserS (p : Parsec β σ E γ) (s₀ : State β σ E) :=
  runParserT' p s₀

/- Finally parse something out of a Parsec.
Works over some polymorphic input type `σ`. -/
def runParserP (p : Parsec β σ E γ) (srcName : String) (xs : σ) :=
  (runParserS p (initialState srcName xs)).2

/- Synonym for `runParserP`. -/
def parseP (p : Parsec β σ E γ) (srcName : String) (xs : σ) :=
  runParserP p srcName xs

/- Test some parser polymorphically. -/
def parseTestP (p : Parsec β σ E γ) (xs : σ) [ToString γ]
               : IO (Bool × Either Unit γ) :=
  match parseP p "" xs with
  -- TODO: Learn to print errors!
  | .left _e => IO.println "There were some errors." >>= fun _ => pure $ (false, Either.left ())
  | .right y => IO.println y >>= fun _ => pure $ (true, Either.right y)

---===========================================================--
---================= USER-FACING FUNCTIONS ===================--
---===========================================================--

-- /- Extracts the end result from ParsecT over a stream.
-- This is a "decorative" wrapper around generic runParserT'.

-- We ask for:

--  1. Some monad. `[Monad monad]`.
--  2. Equipped with a facility to refill a buffer. `[Flood monad bufferedSource]`.
--  3. A way to extract some composite value `[Coco bufferedSource]`.
--  TODO?
-- -/
-- def runParserT (p : ParsecT monad atomic bufferedSource error result)
--                (s₀ : State atomic bufferedSource error)
--                [Monad monad]
--                [Flood monad bufferedSource]
--                [Coco composite bufferedSource]
--                [Iterable composite atomic]
--                [Inhabited α]
--                [Inhabited (monad (Chunk α × bufferedSource))]
--                -- ⊢
--                [@Straume monad bufferedSource Chunk composite atomic] :=
--   runParserT' p s₀

-- /- Finally parse something out of a Parsec over a stream.
-- Works over some stream `σ`.
-- This is a "decorative" wrapper around generic runParserP -/
-- def runParser (p : Parsec atomic bufferedSource error result)
--               (sourceName : String)
--               (xs : bufferedSource)
--               [Coco composite bufferedSource]
--               [Iterable composite atomic]
--               [Inhabited α] :=
--   runParserP p sourceName

-- /- Synonym for `runParser`. -/
-- def parse (p : Parsec atomic bufferedSource error result)
--           (sourceName : String)
--           (xs : bufferedSource)
--           [Coco composite bufferedSource]
--           [Iterable composite atomic]
--           [Inhabited α] :=
--   @runParser atomic bufferedSource error result composite

-- /- Test some parser over stream.
-- This is a "decorative" wrapper around generic parseTestP. -/
-- def parseTest (p : Parsec β σ E γ) (xs : σ) [ToString γ]
--               [Monad m] [@Straume m ℘ Chunk α β] [Iterable α β] [Iterable.Bijection β α] :=
--   parseTestP p xs
