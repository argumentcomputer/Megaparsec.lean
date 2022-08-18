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

namespace MonadParsec

/-- MonadParsec class and their instances -/

/- Monads m that implement primitive parsers.
Thus, you see `m γ`, read it "parser m-gamma".  -/
class MonadParsec (m : Type u → Type v) (α β ℘ E : outParam (Type u)) where
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
  /- The parser at the end of the stream. -/
  eof : m PUnit
  /- If `φ` is `.some`, parse the token.
  Otherwise, accumulate `.none`s into `acc` for error reporting. -/
  token : (φ : β → Option γ) → (acc : List (ErrorItem β)) → m γ
  /- Parse `y` tokens from the beginning of the stream, such that y = |x| > 0, if `φ x y`.
  Succed if |x| = 0.
  Backtrack on fail.
  -/
  tokens : (φ : α → α → Bool) → (x : α) → m γ
  /- Never fail to parse zero or more tokens with `φ`.

  Optional `String` is a way to name the expected token.
  For example:

  `takeWhileP (.just "symbol of Korean alphabet") f` = `many (satisfy f <?> "symbol of Korean alphabet")`

  `takeWhileP .none` f = `many (satisfy f)`.
  -/
  takeWhileP : Option String → (β → Bool) → m α
  /- Like `takeWhileP`, but fail if there are zero matches.

  Optional `String` is a way to name the expected token.

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
  takeP : Option String → n → m α
  /- Ditto. -/
  getParserState : m (State β ℘ E)
  /- Ditto. -/
  updateParserState : (State β ℘ E → State β ℘ E) → m PUnit

universe u
universe v

private def hs₀ (β σ E : Type u) (_ : State β σ E) (_ : ParseError β E) : Hints β := []
private def hs' (β σ E : Type u) (s' : State β σ E) (e : ParseError β E) := toHints (State.offset s') e

instance theInstance {m : Type u → Type v} {α β σ E : Type u}
                     [Monad m] [Iterable α β] [Iterable.Bijection β α] [@Straume m σ Chunk α β]
                     : MonadParsec (ParsecT m β σ E) α β σ E where
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
    | .nil => ErrorItem.eof -- If by the time we call notFollowedBy the stream is empty, treat it as eof.
    | .cont c => c2e c
    | .fin (c, _reason) => c2e c -- It's ok to work with .fin, because we never consume.
    let unexpect u := ParseError.trivial o (.some u) []
    let ok _ _ _ := eerr.2 (unexpect subject) s
    let err _ _ := eok.2 PUnit.unit s []
    p xi s (Consumed.mk, ok) (Consumed.mk, err) (Empty.mk, ok) (Empty.mk, err)
  withRecovery φ p := fun xi s cok cerr eok eerr =>
    let err (fHs := (hs₀ β σ E)) e sFail :=
      let ok ψ := fun x s' _hs => ψ x s' (fHs s' e)
      let err _ _ := cerr.2 e sFail
      (φ e) xi sFail (cok.1, ok cok.2) (Consumed.mk, err) (eok.1, ok eok.2) (Empty.mk, err)
    p xi s cok (Consumed.mk, err) eok (Empty.mk, err $ hs' β σ E)
  observing p := fun xi s cok cerr eok eerr =>
    let err (fHs := (hs₀ β σ E)) e s' := cok.2 (.left e) s' (fHs s' e)
    p xi s (cok.1, cok.2 ∘ .right) (Consumed.mk, err) (eok.1, eok.2 ∘ .right) (Empty.mk, err (hs' β σ E))
  eof := sorry
  token := sorry
  tokens := sorry
  takeWhileP := sorry
  takeWhile1P := sorry
  takeP := sorry
  getParserState := sorry
  updateParserState := sorry
