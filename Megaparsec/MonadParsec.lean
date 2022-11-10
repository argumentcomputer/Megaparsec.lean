import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.Errors.StreamErrors
import Megaparsec.Parsec
import Megaparsec.ParserState
import Megaparsec.Streamable
import Straume
import Straume.Chunk
import Straume.Iterator

import YatimaStdLib

open Std (RBSet)

open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.Errors.StreamErrors
open Megaparsec.Parsec
open Megaparsec.ParserState
open Megaparsec.Streamable
open Straume
open Straume.Chunk
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection
open Straume.Iterator renaming toList → Iterable.toList

namespace MonadParsec

/-- MonadParsec class and their instances -/

/- Monads m that implement primitive parsers.
Thus, you see `m γ`, read it "parser m-gamma".

On type variables:

- `α` is the composite type, which is a type of finite chunks that can be parsed out of `℘`.
- `β` is the atomic type. That's the type of tokens parsed out of source `℘`.
- `℘` is the source type. Tokens can be read out of the source via `Straume` facilities. `Straume` allows for transparently reading from files. If you want to read from a file, this type would be `(String × IO.FS.Handle)`. It would mean that finite chunks of type `String` are emitted from a, perhaps-larger-than-RAM file handled with somethign of type `IO.FS.Handle`. See `Main.lean` for a usage example! It's really simple!
- `E` is the custom error type. For quick and dirty parsers, it's `Unit`, but if you want to get fancy, you can create custom errors and construct those based on your parser's fails.
- `γ` is the type of the thing we're parsing out of the source.

-/
class MonadParsec (m : Type u → Type v) (℘ α E β : Type u) where
  /- Stop parsing wherever we are, and report ParseError. -/
  parseError : ParseError β E → m γ
  /- If `m γ` consumed no input, replace the names of expected tokens with `nameOverride`. -/
  label (nameOverride : String) : m γ → m γ
  /- Hides expected token error messages when `m γ` fails. -/
  hidden (p : m γ) : m γ := label "" p
  /- Attempts to parse with `m γ` and backtrack on failure.
  Normally used to alternate between parsers with the same prefixes.
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

private def hs₀ (β ℘ E : Type u) (_ : State β ℘ E) (_ : ParseError β E) : Hints β := []
private def hs' (β ℘ E : Type u) (s' : State β ℘ E) (e : ParseError β E) := toHints (State.offset s') e
private def nelstr (x : Char) (xs : String) := match NEList.nonEmptyString xs with
  | .some xs' => NEList.cons x xs'
  | .none => NEList.uno x

@[default_instance]
instance theInstance {m : Type u → Type v} {α β ℘ E : Type u} [Streamable ℘]
                     [Monad m] [Iterable α β] [Iterable.Bijection β α] [Inhabited α] [@Straume m ℘ Chunk α β] [Ord β] [Ord E]
                     : MonadParsec (ParsecT m β ℘ E) ℘ α E β where

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
      | ParseError.trivial pos us _ =>
        let empty : RBSet (ErrorItem β) compare := default
        .trivial pos us (Option.option empty .single el)
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
    let y : (Chunk β × ℘) ← Straume.take1 α s.input
    let c2e := ErrorItem.tokens ∘ NEList.uno
    let subject : ErrorItem β := match y.1 with
    -- TODO: Here and in many other places, we have two branches that are the same because Parsec doesn't care about .fin vs .cont
    -- TODO: Perhaps, we should use Terminable and extract values
    | .nil => ErrorItem.eof -- If by the time we call notFollowedBy the stream is empty, treat it as eof.
    | .cont c => c2e c
    | .fin (c, _reason) => c2e c -- It's ok to work with .fin, because we never consume.
    let empty : RBSet (ErrorItem β) compare := default
    let ok _ _ _ := eerr.2 (.trivial o subject empty) s
    let err _ _ := eok.2 PUnit.unit s []
    p xi s (Consumed.mk, ok) (Consumed.mk, err) (Empty.mk, ok) (Empty.mk, err)

  withRecovery φ p := fun xi s cok cerr eok _ =>
    let err (fHs := (hs₀ β ℘ E)) e sFail :=
      let ok ψ := fun x s' _hs => ψ x s' (fHs s' e)
      let err _ _ := cerr.2 e sFail
      (φ e) xi sFail (cok.1, ok cok.2) (Consumed.mk, err) (eok.1, ok eok.2) (Empty.mk, err)
    p xi s cok (Consumed.mk, err) eok (Empty.mk, err $ hs' β ℘ E)

  observing p := fun xi s cok _ eok _ =>
    let err (fHs := (hs₀ β ℘ E)) e s' := cok.2 (.left e) s' (fHs s' e)
    p xi s (cok.1, cok.2 ∘ .right) (Consumed.mk, err) (eok.1, eok.2 ∘ .right) (Empty.mk, err (hs' β ℘ E))

  eof := fun _ s _ _ eok eerr => do
      let y : (Chunk β × ℘) ← Straume.take1 α s.input
      let singleton : RBSet (ErrorItem β) compare := .single .eof
      let err c := eerr.2 (.trivial s.offset (.some $ ErrorItem.tokens $ NEList.uno c) singleton) s
      match y.1 with
      | .nil => eok.2 PUnit.unit s []
      | .cont c => err c
      | .fin (c, _) => err c

  token ρ errorCtx := fun _ s cok _ _ eerr => do
    -- TODO: Uhh, if y : γ, then we should really not call these variables "y"
    -- In reality, they are cctx ot csctx.
    let y : (Chunk β × ℘) ← Straume.take1 α s.input
    let set := .ofList errorCtx compare
    let test c := match ρ c with
    | .none =>
      eerr.2 (.trivial s.offset (.some $ ErrorItem.tokens $ NEList.uno c) set) s
    | .some y' =>
      let offset' := s.offset + 1
      cok.2 y' {s with offset := offset', input := y.2, posState := reachOffsetNoLine offset' s.posState } []
    match y.1 with
    | .nil => eerr.2 (.trivial s.offset (.some ErrorItem.eof) set) s
    | .cont c => test c
    | .fin (c, _) => test c

  tokens f l := fun _ s cok _ eok eerr => do
    let n : Nat := Iterable.length l
    let y : (Chunk α × ℘) ← Straume.takeN n s.input
    let unexpect pos' u :=
      let got := pure u
      let want := match NEList.nonEmpty (Iterable.toList l) with
        | .none => (default : RBSet (ErrorItem β) compare)
        | .some nel => .single (ErrorItem.tokens nel)
      ParseError.trivial pos' got want
    let test r := if f l r
      then
        let offset' := s.offset + n
        let s' := { s with offset := offset', input := y.2, posState := reachOffsetNoLine offset' s.posState }
        (if n == 0 then eok.2 else cok.2) r s' []
      else
        let got₀ := match NEList.nonEmpty (Iterable.toList r) with
        -- TODO: There is a significant discrepancy between this implementaiton and Haskell
        -- Because here we handle empty r, whereas the original implementation doesn't.
        --
        -- I have a feeling it's a bug in the original implementation.
        | .none => ErrorItem.label (nelstr 'F' "ailed to parse empty input")
        | .some nel => ErrorItem.tokens nel
        eerr.2 (unexpect s.offset got₀) s
    match y.1 with
    | .nil => eerr.2 (unexpect s.offset ErrorItem.eof) s
    | .cont cs => test cs
    | .fin (cs, _) => test cs

  takeWhileP ol ρ := fun _ s cok _ eok _ => do
    let y : (Chunk α × ℘) ← Straume.takeWhile ρ s.input
    let hs := match ol >>= NEList.nonEmptyString with
    | .none => []
    | .some l => [ [ ErrorItem.label l ] ]
    match y.1 with
    | .nil => eok.2 default {s with input := y.2} hs
    -- TODO: Maybe it's just <$> for Chunk? Do we have Functor? I forget.
    | .cont cs =>
      let offset' := s.offset + Iterable.length cs
      cok.2 cs { s with input := y.2, offset := offset', posState := reachOffsetNoLine offset' s.posState } hs -- TODO: Why hs, not [] ?
    | .fin (cs, _) =>
      let offset' := s.offset + Iterable.length cs
      cok.2 cs { s with input := y.2, offset := offset', posState := reachOffsetNoLine offset' s.posState } hs -- TODO: Why hs, not [] ?
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
    let want := .ofList (hs.headD []) compare
    let res cs y := do
      let n := Iterable.length cs
      if (n == 0) then
        let yb : (Chunk β × ℘) ← (Straume.take1 α s.input)
        let got c := .some (ErrorItem.tokens $ NEList.uno c)
        match yb.1 with
        | .nil =>
          eerr.2 (.trivial s.offset (.some ErrorItem.eof) want) s
        | .cont c =>
          eerr.2 (.trivial s.offset (got c) want) s
        | .fin (c, _) =>
          eerr.2 (.trivial s.offset (got c) want) s
      else
        let offset' := s.offset + n
        cok.2 cs { s with offset := offset', input := y.2, posState := reachOffsetNoLine offset' s.posState } hs
    let y : (Chunk α × ℘) ← Straume.takeWhile ρ s.input
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
    let want := .ofList (hs.headD []) compare
    let y : (Chunk α × ℘) ← Straume.takeN n s.input
    let ok cs :=
      let offset' := s.offset + n
      cok.2 cs { s with offset := offset', input := y.2, posState := reachOffsetNoLine offset' s.posState } hs
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

instance [Monoid w] [OfNat w 1] [Monad m] [Ord β] [Ord E]
         [mₚ : MonadParsec m ℘ α E β]
         [mₗ : MonadLiftT m (RWST r w σ m)]
         : MonadParsec (RWST r w σ m) ℘ α E β where
  parseError err := mₗ.monadLift $ mₚ.parseError ℘ α err
  label l p := fun r s => mₚ.label ℘ α E β l (p r s)
  attempt st := fun r s => mₚ.attempt ℘ α E β (st r s)
  lookAhead st := fun r s => do
    let (x, _, _) ← mₚ.lookAhead ℘ α E β (st r s)
    pure (x, s, One.one)
  notFollowedBy st := fun r s => do
    mₚ.notFollowedBy ℘ α E β $ void $ st r s
    pure (Unit.unit, s, One.one)
  withRecovery φ p := fun r s =>
    mₚ.withRecovery ℘ α (fun e => (φ e) r s) (p r s)
  observing p := fun r s =>
    Either.Correctness.fixs' s <$> mₚ.observing ℘ α (p r s)
  eof := mₗ.monadLift $ mₚ.eof ℘ α E β
  token ρ errorCtx := mₗ.monadLift $ mₚ.token ℘ α E ρ errorCtx
  tokens f l := mₗ.monadLift $ mₚ.tokens ℘ E β f l
  takeWhileP ol ρ := mₗ.monadLift $ mₚ.takeWhileP ℘ E ol ρ
  takeWhile1P ol ρ := mₗ.monadLift $ mₚ.takeWhile1P ℘ E ol ρ
  takeP ol n := mₗ.monadLift $ mₚ.takeP ℘ E β ol n
  getParserState := mₗ.monadLift $ mₚ.getParserState α
  updateParserState φ := mₗ.monadLift $ mₚ.updateParserState α φ

instance statetInstance
         [Monad m] [Alternative m] [Ord β] [Ord E]
         [mₚ : MonadParsec m ℘ α E β]
         : MonadParsec (StateT σ m) ℘ α E β where
  parseError err := liftM $ mₚ.parseError ℘ α err
  label l p := (mₚ.label ℘ α E β l) ∘ p
  attempt st := (mₚ.attempt ℘ α E β) ∘ st
  lookAhead st := (mₚ.lookAhead ℘ α E β) ∘ st
  notFollowedBy st x :=
    Monad.seqComp (mₚ.notFollowedBy ℘ α E β (Prod.fst <$> st x)) $ pure (Unit.unit, x)
  withRecovery cont st x :=
    mₚ.withRecovery ℘ α (fun e => (cont e) x) $ st x
  observing p x :=
    Either.Correctness.fixs x <$> (mₚ.observing ℘ α $ p x)
  eof := liftM $ mₚ.eof ℘ α E β
  token p errorCtx :=
    liftM $ mₚ.token ℘ α E p errorCtx
  tokens f l :=
    liftM $ mₚ.tokens ℘ E β f l
  takeWhileP ol ρ := liftM $ mₚ.takeWhileP ℘ E ol ρ
  takeWhile1P ol ρ := liftM $ mₚ.takeWhile1P ℘ E ol ρ
  takeP ol n := liftM $ mₚ.takeP ℘ E β ol n
  getParserState := liftM $ mₚ.getParserState α
  updateParserState φ := liftM $ mₚ.updateParserState α φ

def withRange (α : Type u) (p : ParsecT m β ℘ E (Range → γ)) [i : MonadParsec (ParsecT m β ℘ E) ℘ α E β] : ParsecT m β ℘ E γ := do
  let s₀ : State β ℘ E ← MonadParsec.getParserState α
  let first := s₀.posState.sourcePos
  let go ← p
  let s₁ : State β ℘ E ← MonadParsec.getParserState α
  let last := s₁.posState.sourcePos
  pure $ go (Range.mk first last)

end MonadParsec

namespace Megaparsec

open MonadParsec

section

def parseError {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec m ℘ α E β] {γ : Type u}
  : Megaparsec.Errors.ParseError.ParseError β E → m γ :=
  MonadParsec.MonadParsec.parseError ℘ α

def label {m: Type u → Type v} {℘ α E β: Type u} [i : MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : String → m γ → m γ :=
  MonadParsec.MonadParsec.label ℘ α E β

def hidden {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : m γ → m γ :=
  MonadParsec.MonadParsec.hidden ℘ α E β

def attempt {m: Type u → Type v} {℘ α E β: Type u} [i : MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : m γ → m γ :=
  MonadParsec.MonadParsec.attempt ℘ α E β

def lookAhead {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : m γ → m γ :=
  MonadParsec.MonadParsec.lookAhead ℘ α E β

def notFollowedBy {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : m γ → m PUnit :=
  MonadParsec.MonadParsec.notFollowedBy ℘ α E β

def withRecovery {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : (Megaparsec.Errors.ParseError.ParseError β E → m γ) → m γ → m γ :=
  MonadParsec.MonadParsec.withRecovery ℘ α

def observing {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β] {γ : Type u}
  : m γ → m (Either (Megaparsec.Errors.ParseError.ParseError β E) γ) :=
  MonadParsec.MonadParsec.observing ℘ α

def eof {m: Type u → Type v} {℘ α E β: Type u} [i : MonadParsec.MonadParsec m ℘ α E β] : m PUnit :=
  MonadParsec.MonadParsec.eof ℘ α E β

def token {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : (β → Option γ) → (List (Megaparsec.Errors.ErrorItem β)) → m γ :=
  MonadParsec.MonadParsec.token ℘ α E

def tokens {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : (α → α → Bool) → α → m α :=
  MonadParsec.MonadParsec.tokens ℘ E β

def takeWhileP {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : Option String → (β → Bool) → m α :=
  MonadParsec.MonadParsec.takeWhileP ℘ E

def takeWhile1P {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : Option String → (β → Bool) → m α :=
  MonadParsec.MonadParsec.takeWhile1P ℘ E

def takeP {m: Type u → Type v} {℘ α E β: Type u} [ MonadParsec.MonadParsec m ℘ α E β] : Option String -> Nat -> m α :=
  MonadParsec.MonadParsec.takeP ℘ E β

def getParserState {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : m (Megaparsec.ParserState.State β ℘ E) :=
  MonadParsec.MonadParsec.getParserState α

def updateParserState {m: Type u → Type v} {℘ α E β: Type u} [MonadParsec.MonadParsec m ℘ α E β]
  : (Megaparsec.ParserState.State β ℘ E → Megaparsec.ParserState.State β ℘ E)-> m PUnit :=
  MonadParsec.MonadParsec.updateParserState α

end

end Megaparsec
