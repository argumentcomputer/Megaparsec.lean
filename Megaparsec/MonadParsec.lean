import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.Errors.StreamErrors
import Megaparsec.Parsec
import Megaparsec.ParserState
import Straume
import Straume.Chunk
import Straume.Iterator

import YatimaStdLib

open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.Errors.StreamErrors
open Megaparsec.Parsec
open Megaparsec.ParserState
open Straume
open Straume.Chunk
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection
open Straume.Iterator renaming toList → Iterable.toList

namespace MonadParsec

/-- MonadParsec class and their instances -/

/- Monads m that implement primitive parsers.
Thus, you see `m γ`, read it "parser m-gamma".  -/
class MonadParsec (m : Type u → Type v) (℘ α : Type u) (β E : outParam (Type u)) where
  /- Stop parsing wherever we are, and report ParseError. -/
  parseError : ParseError β E → m γ
  /- If `m γ` consumed no input, replace the names of expected tokens with `nameOverride`. -/
  label (nameOverride : String) : m γ → m γ
  /- Hides expected token error messages when `m γ` fails. -/
  hidden (p : m γ) : m γ := label "" p
  /- Attempts to parse with `m γ` and backtrack on failure.
  Used for arbitrary look-ahead.
  Consult megaparsec docs for pitfalls:
  https://hackage.haskell.org/package/megaparsec-9.2.1/docs/src/Text.Megaparsec.Class.html#try -/
  attempt : m γ → m γ
  /- Parse with `m γ` without consuming.
  Fail on fail.
  Combine with `attempt` if you need to recover.
  -/
  lookAhead : m γ → m γ
  /- Succeeds if `m γ` fails. Doesn't consume, nor modify state.
  Useful for "longest match" rule implementation. -/
  notFollowedBy : m γ → m PUnit
  /- Use recovery function `φ` to recover from failure in `m γ`. -/
  withRecovery : (φ : ParseError β E → m γ) → m γ → m γ
  /- Observes errors as they happen, without backtracking. -/
  observing : m γ → m (Either (ParseError β E) γ)
  /- The parser only succeeds at the end of the stream. -/
  eof : m PUnit
  /- If `φ` is `.some`, parse the token.
  Otherwise, accumulate `.none`s into `acc` for error reporting. -/
  token : (φ : β → Option γ) → (acc : List (ErrorItem β)) → m γ
  /- Parse `y` tokens from the beginning of the stream, such that y = |x| > 0, if `φ x y`.
  Backtrack on fail.
  -/
  tokens : (φ : α → α → Bool) → (x : α) → m α
  /- Never fail to parse zero or more tokens with `φ`.

  Optional `String` is a way to name the expected token.
  For example:

  `takeWhileP (.some "symbol of Korean alphabet") f` = `many (satisfy f <?> "symbol of Korean alphabet")`

  `takeWhileP .none` f = `many (satisfy f)`.
  -/
  takeWhileP : Option String → (β → Bool) → m α
  /- Like `takeWhileP`, but fail if there are zero matches.

  Optional `String` a way to name the expected token.

  For example:

  `takeWhile1P (.just "symbol of Korean alphabet")` f = `many (satisfy f <?> "symbol of Korean alphabet")`

  `takeWhile1P .none` f = `many (satisfy f)`.
  -/
  takeWhile1P : Option String → (β → Bool) → m α
  /- Parses `n` tokens at the beginning of the stream.
  Backtracks if there are not enough tokens.

  NB! This is not a best-effort take, like we have it in Straume!
  It has to guarantee that if it succeds, the requested amount of tokens is returned!

  Optional `String` is a way to name the expected group of tokens.

  For example:

  `takeP (.some "protobuf message") n` = `count n (anySingle <?> "protobuf message")`

  `takeP .none n` = `count n anySingle`.
  -/
  takeP : Option String → Nat → m α
  /- Ditto. -/
  getParserState : m (State β ℘ E)
  /- Ditto. -/
  updateParserState : (State β ℘ E → State β ℘ E) → m PUnit

universe u
universe v

private def hs₀ (β σ E : Type u) (_ : State β σ E) (_ : ParseError β E) : Hints β := []
private def hs' (β σ E : Type u) (s' : State β σ E) (e : ParseError β E) := toHints (State.offset s') e
private def nelstr (x : Char) (xs : String) := match NEList.nonEmptyString xs with
  | .some xs' => NEList.cons x xs'
  | .none => NEList.uno x

instance theInstance {m : Type u → Type v} {α β σ E : Type u}
                     [Monad m] [Iterable α β] [Iterable.Bijection β α] [Inhabited α] [@Straume m σ Chunk α β]
                     [ToString β]
                     : MonadParsec (ParsecT m β σ E) σ α β E where

  parseError e := fun _xi s _cok _cerr _eok eerr => eerr.2 e s

  label l p := fun xi s cok cerr eok eerr =>
    let el := Option.map ErrorItem.label (NEList.nonEmptyString l)
    let f x s' hs :=
      match el with
      | .none => cok.2 x s' $ refreshLastHint hs .none
      | .some _ => cok.2 x s' hs
    let g x s' hs :=
      eok.2 x s' $ refreshLastHint hs el
    let ge err := eerr.2 $
      match err with
      | ParseError.trivial pos us _ => .trivial pos us (Option.option [] (fun x => [x]) el)
      | _ => err
    p xi s (cok.1, f) cerr (eok.1, g) (eerr.1, ge)

  attempt p := fun xi s cok _ eok eerr =>
    let forceBacktrack e _ := eerr.2 e s
    p xi s cok (Consumed.mk, forceBacktrack) eok (Empty.mk, forceBacktrack)

  lookAhead p := fun xi s _ cerr eok eerr =>
    let forceBacktrack x _ _ := eok.2 x s [] -- TODO: why not forward hints?
    p xi s (Consumed.mk, forceBacktrack) cerr (Empty.mk, forceBacktrack) eerr

  notFollowedBy p := fun xi s _ _ eok eerr => do
    let o := s.offset
    let y : (Chunk β × σ) ← Straume.take1 α s.input
    let c2e := ErrorItem.tokens ∘ NEList.uno
    let subject : ErrorItem β := match y.1 with
    -- TODO: Here and in many other places, we have two branches that are the same because Parsec doesn't care about .fin vs .cont
    -- TODO: Perhaps, we should use Terminable and extract values
    | .nil => ErrorItem.eof -- If by the time we call notFollowedBy the stream is empty, treat it as eof.
    | .cont c => c2e c
    | .fin (c, _reason) => c2e c -- It's ok to work with .fin, because we never consume.
    let ok _ _ _ := eerr.2 (.trivial o subject []) s
    let err _ _ := eok.2 PUnit.unit s []
    p xi s (Consumed.mk, ok) (Consumed.mk, err) (Empty.mk, ok) (Empty.mk, err)

  withRecovery φ p := fun xi s cok cerr eok _ =>
    let err (fHs := (hs₀ β σ E)) e sFail :=
      let ok ψ := fun x s' _hs => ψ x s' (fHs s' e)
      let err _ _ := cerr.2 e sFail
      (φ e) xi sFail (cok.1, ok cok.2) (Consumed.mk, err) (eok.1, ok eok.2) (Empty.mk, err)
    p xi s cok (Consumed.mk, err) eok (Empty.mk, err $ hs' β σ E)

  observing p := fun xi s cok _ eok _ =>
    let err (fHs := (hs₀ β σ E)) e s' := cok.2 (.left e) s' (fHs s' e)
    p xi s (cok.1, cok.2 ∘ .right) (Consumed.mk, err) (eok.1, eok.2 ∘ .right) (Empty.mk, err (hs' β σ E))

  eof := fun _ s _ _ eok eerr => do
      let y : (Chunk β × σ) ← Straume.take1 α s.input
      dbg_trace y.1
      let err c := eerr.2 (.trivial s.offset (.some $ ErrorItem.tokens $ NEList.uno c) ([.eof])) s
      match y.1 with
      | .nil => eok.2 PUnit.unit s []
      | .cont c => err c
      | .fin (c, _) => err c

  token ρ errorCtx := fun _ s cok _ _ eerr => do
    -- TODO: Uhh, if y : γ, then we should really not call these variables "y"
    -- In reality, they are cctx ot csctx.
    let y : (Chunk β × σ) ← Straume.take1 α s.input
    let test c := match ρ c with
    | .none =>
      eerr.2 (.trivial s.offset (.some $ ErrorItem.tokens $ NEList.uno c) errorCtx) s
    | .some y' => cok.2 y' {s with offset := s.offset + 1, input := y.2} []
    match y.1 with
    | .nil => eerr.2 (.trivial s.offset (.some ErrorItem.eof) errorCtx) s
    | .cont c => test c
    | .fin (c, _) => test c

  tokens f l := fun _ s cok _ eok eerr => do
    let n : Nat := Iterable.length l
    let y : (Chunk α × σ) ← Straume.takeN n s.input
    let unexpect pos' u :=
      let got := pure u
      let want := match NEList.nonEmpty (Iterable.toList l) with
        | .none => []
        | .some nel => [ ErrorItem.tokens nel ]
      ParseError.trivial pos' got want
    let test r := if f l r
      then
        let s' := { s with offset := s.offset + n, input := y.2 }
        (if n == 0 then eok.2 else cok.2) r s' []
      else
        let got₀ := match NEList.nonEmpty (Iterable.toList r) with
        | .none => ErrorItem.label (nelstr 'F' "ailed to parse empty input")
        | .some nel => ErrorItem.tokens nel
        eerr.2 (unexpect s.offset got₀) s
    match y.1 with
    | .nil => eerr.2 (unexpect s.offset ErrorItem.eof) s
    | .cont cs => test cs
    | .fin (cs, _) => test cs

  takeWhileP ol ρ := fun _ s cok _ eok _ => do
    let y : (Chunk α × σ) ← Straume.takeWhile ρ s.input
    let hs := match ol >>= NEList.nonEmptyString with
    | .none => []
    | .some l => [ [ ErrorItem.label l ] ]
    match y.1 with
    | .nil => eok.2 default {s with input := y.2} hs
    -- TODO: Maybe it's just <$> for Chunk? Do we have Functor? I forget.
    | .cont cs => cok.2 cs  {s with input := y.2, offset := s.offset + Iterable.length cs} hs -- TODO: Why hs, not [] ?
    | .fin (cs, _) => cok.2 cs  {s with input := y.2, offset := s.offset + Iterable.length cs} hs -- TODO: Why hs, not [] ?
    -- TODO: This is COPY PASTA!

  takeWhile1P ol ρ := fun _ s cok _ _ eerr => do
    let el : Option (ErrorItem β) := -- TODO: why doesn't `ErrorItem.label <$> (ol >>= NEList.nonEmptyString)` work?!
      match ol with
      | .none => .none
      | .some ll => match NEList.nonEmptyString ll with
        | .none => .none
        | .some lll => .some $ ErrorItem.label lll
    let hs : Hints β := -- el >>= ( (List.concat []) ∘ (List.concat []) )
      match el with
      | .none => []
      | .some ell => [[ell]]
    let want := hs.headD []
    let res cs y := do
      let n := Iterable.length cs
      if (n == 0) then
        let yb : (Chunk β × σ) ← (Straume.take1 α s.input)
        let got c := .some (ErrorItem.tokens $ NEList.uno c)
        match yb.1 with
        | .nil =>
          eerr.2 (.trivial s.offset (.some ErrorItem.eof) want) s
        | .cont c =>
          eerr.2 (.trivial s.offset (got c) want) s
        | .fin (c, _) =>
          eerr.2 (.trivial s.offset (got c) want) s
      else
        cok.2 cs {s with offset := s.offset + n, input := y.2} hs
    let y : (Chunk α × σ) ← Straume.takeWhile ρ s.input
    match y.1 with
    | .nil =>
      let got := .some ErrorItem.eof
      eerr.2 (.trivial s.offset got want) s
    | .cont cs => res cs y
    | .fin (cs, _) => res cs y

  takeP ol n := fun _ s cok _ _ eerr => do
    -- TODO: Copypasta
    let el : Option (ErrorItem β) := -- TODO: why doesn't `ErrorItem.label <$> (ol >>= NEList.nonEmptyString)` work?!
      match ol with
      | .none => .none
      | .some ll => match NEList.nonEmptyString ll with
        | .none => .none
        | .some lll => .some $ ErrorItem.label lll
    let hs : Hints β := -- el >>= ( (List.concat []) ∘ (List.concat []) )
      match el with
      | .none => []
      | .some ell => [[ell]]
    let want := hs.headD []
    let y : (Chunk α × σ) ← Straume.takeN n s.input
    let ok cs := cok.2 cs {s with offset := s.offset + n, input := y.2} hs
    match y.1 with
    | .nil => eerr.2 (.trivial s.offset (.some ErrorItem.eof) want) s
    | .cont cs => ok cs
    | .fin (cs, _) =>
      let len := (Iterable.length cs)
      if len ≠ n then
        eerr.2 (.trivial (s.offset + len) (.some ErrorItem.eof) want) s
      else
        ok cs

  getParserState := fun _ s _ _ eok _ =>
    eok.2 s s []

  updateParserState φ := fun _ s _ _ eok _ =>
    eok.2 PUnit.unit (φ s) []
