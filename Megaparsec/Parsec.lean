import Megaparsec.Err
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Errors.StreamErrors
-- import Megaparsec.Errors.StateErrors
-- import Megaparsec.Errors.StreamErrors
import Megaparsec.Ok
import Megaparsec.ParserState
import Megaparsec.Printable
import Megaparsec.Streamable
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
open Megaparsec.Printable
open Megaparsec.Streamable

open Straume
open Straume.Flood
open Straume.Chunk
open Straume.Coco
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection

section

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

/-
Note: `ParsecT m β ℘ E` (note absence of γ) will have kind `Type u → Type (max u v)`.
It is perfect to define a monad. -/
def ParsecT (m : Type u → Type v) (β ℘ E γ : Type u) :=
  ∀ (ξ : Type u),
  let ok := Ok m β ℘ E γ ξ
  let err := Err m β ℘ E ξ
  State β ℘ E →
    (Consumed × ok) →
    (Consumed × err) →
    (Empty × ok) →
    (Empty × err) →
    m ξ

def runOk (o : Type) {β ℘ γ E : Type u}
          [Outcome o] [Monad m] : (o × Ok m β ℘ E γ (Reply β ℘ γ E)) :=
  (Outcome.make, fun y s₁ _ => pure ⟨ s₁, Outcome.consumed? o, .ok y ⟩)

-- TODO: pick two additional letters for unbound module-wise universes
def runErr (o : Type) {β ℘ γ E : Type u}
           [Outcome o] [Monad m] : (o × Err m β ℘ E (Reply β ℘ γ E)) :=
  (Outcome.make, fun err s₁ => pure ⟨ s₁, Outcome.consumed? o, .err err ⟩)

-- TODO: move to Straume
instance : Flood Id α where
  flood x _ := id x

abbrev Parsec := ParsecT Id

def runParsecT {m : Type u → Type v} {β ℘ E γ : Type u}
               (parser : ParsecT m β ℘ E γ) (s₀ : State β ℘ E) [Monad m] : m (Reply β ℘ γ E) :=
  parser (Reply β ℘ γ E) s₀
         (runOk Consumed) (runErr Consumed)
         (runOk Empty) (runErr Empty)

/- Pure doesn't consume. -/
instance : Pure (ParsecT m β ℘ E) where
  pure x := fun _ s _ _ ((_ : Empty), f) _ => f x s []

/- Map over happy paths. -/
instance : Functor (ParsecT m β ℘ E) where
  map φ ta :=
    fun xi s cok cerr eok eerr =>
      ta xi s (cok.1, (cok.2 ∘ φ)) cerr (eok.1, (eok.2 ∘ φ)) eerr

/- Bind into the happy path, accumulating hints about errors. -/
-- TODO: use functors over (x, y) to update parsecs.
open Outcome in
instance : Bind (ParsecT m β ℘ E) where
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
instance : Seq (ParsecT m β ℘ E) where
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

instance : Monad (ParsecT m β ℘ E) := {}

/- Second-biased way to return a state with the most processed tokens. -/
def longestMatch (s₀ : State β ℘ E) (s₁ : State β ℘ E) : State β ℘ E :=
  if s₀.offset > s₁.offset then s₀ else s₁

open StreamErrors in
open Outcome in
instance [Ord β] : Alternative (ParsecT m β ℘ E) where
  failure := fun _ s _ _ _ eerr =>
    let empty : Std.RBSet (ErrorItem β) compare := default
    eerr.2 (.trivial s.offset .none empty) s
  orElse guess thunk :=
    fun xi s cok cerr eok eerr =>
      let fallback err ms :=
        let nge ψ err' s' := ψ (mergeErrors err' err) (longestMatch ms s')
        let ng x s' hs := eok.2 x s' (toHints s'.offset err ++ hs)
        (thunk ()) xi s cok (cerr.1, nge cerr.2) (eok.1, ng) (eerr.1, nge eerr.2)
    guess xi s cok cerr eok (eerr.1, fallback)

-- open StreamErrors in
-- open Outcome in
-- instance : Alternative (Parsec β ℘ E) where
--   failure := fun _ s _ _ _ eerr => eerr.2 (.trivial s.offset Option.none []) s
--   orElse guess thunk :=
--     fun xi s cok cerr eok eerr =>
--       let fallback err ms :=
--         let nge ψ err' s' := ψ (mergeErrors err' err) (longestMatch ms s')
--         let ng x s' hs := eok.2 x s' (toHints s'.offset err ++ hs)
--         (thunk ()) xi s cok (cerr.1, nge cerr.2) (eok.1, ng) (eerr.1, nge eerr.2)
--     guess xi s cok cerr eok (eerr.1, fallback)

instance [Ord β] : Inhabited (ParsecT m β ℘ E γ) where
  default := Alternative.failure


---=========================================================--
---================= IMPORTANT FUNCTIONS ===================--
---=========================================================--

open Megaparsec.Errors.Bundle

/- Extracts the end result from ParsecT run and presents it as a tuple under inner monad. -/
def runParserT' {m : Type u → Type v} {β ℘ E γ : Type u}
                (p : ParsecT m β ℘ E γ) (s₀ : State β ℘ E) [Monad m]
                : m (State β ℘ E × (Except (ParseErrorBundle β ℘ E) γ)) := do
  let reply ← runParsecT p s₀
  let s₁ := reply.state
  pure $
    match reply.result with
    | .ok x =>
      match NEList.nonEmpty $ s₁.parseErrors with
      | .none => (s₁, .ok x)
      | .some pes => (s₁, .error $ toBundle s₀ pes)
    | .err e => (s₁, .error (toBundle s₀ $ List.toNEList e s₁.parseErrors))

def parseTestTP {m : Type → Type v} {β ℘ E : Type} {γ : Type}
                (p : ParsecT m β ℘ E γ) (xs : ℘) (srcName := "(test run)") [ToString E] [Printable β] [ToString γ] [Monad m] [MonadLiftT m IO] [Streamable ℘]
                : IO (Bool × Except Unit γ) := do
  let reply ← liftM $ runParserT' p (initialState srcName xs)
  match reply.2 with
  | .error e => IO.println e >>= fun _ => pure $ (false, .error ())
  | .ok y => IO.println y >>= fun _ => pure $ (true, .ok y)

/- Extracts the end result from Parsec run and presents it as a tuple as is (under Id monad). -/
def runParserS (p : Parsec β ℘ E γ) (s₀ : State β ℘ E) :=
  runParserT' p s₀

/- Finally parse something out of a Parsec.
Works over some polymorphic input type `℘`. -/
def runParserP (p : Parsec β ℘ E γ) (srcName : String) (xs : ℘) :=
  (runParserS p (initialState srcName xs)).2

/- Synonym for `runParserP`. -/
def parseP (p : Parsec β ℘ E γ) (srcName : String) (xs : ℘) :=
  runParserP p srcName xs

def parseTP (p : ParsecT m β ℘ E γ) (srcName : String) (xs : ℘) [Monad m] :=
  runParserT' p (initialState srcName xs) >>=
    fun y => pure y.2

def parseT (p : ParsecT m β ℘ E γ) (xs : ℘) [Monad m] :=
  parseTP p "" xs

def parse (p : Parsec β ℘ E γ) (xs : ℘) :=
  parseP p "" xs

end

def parsesT? (p : ParsecT m β ℘ E γ) (xs : ℘) [Monad m] :=
  parseT p xs >>= (pure ∘ Except.isOk)

def parses? (p : Parsec β ℘ E γ) (xs : ℘) :=
  Except.isOk $ parse p xs

/- Test some parser polymorphically. -/
def parseTestP (p : Parsec β ℘ E γ) [ToString γ] [Printable β] [ToString E]
  (xs : ℘) [Streamable ℘] : IO (Bool × Except Unit γ) :=
  match parseP p "" xs with
  | .error es => IO.println s!"{es}" >>= fun _ => pure $ (false, .error ())
  | .ok y => IO.println y >>= fun _ => pure $ (true, .ok y)

def parseTest (p : Parsec β ℘ E γ) [ToString γ] [Printable β] [ToString E] (xs : ℘) [Streamable ℘] : String :=
  match parseP p "" xs with
  | .error es => s!"Err: {es}"
  | .ok y => s!"Ok: {y}"
