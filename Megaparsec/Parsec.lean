import Megaparsec.ParserState
import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors
import Megaparsec.Errors.StateErrors
import Megaparsec.Errors.Bundle

namespace Parsec

/-!
Parsec transformer and abbreviation runners and relevant instances.

Please find the most important functions for the users in the end of the file.
-/

/-- Parsec transformer, designed to add MonadParsec capability to any given monad M. -/
structure ParsecT (E : Type) [stream : Stream.Stream S] [m : Monad M] (A : Type) where
  -- TODO: Rewrite it as Lean 4 transformers (with `def`).
  unParser :
    (B : Type) → (ParserState.State S E) →
    -- Return A with State S E and Hints into M B
    (A → ParserState.State S E → Errors.Hints (stream.Token) → M B) →          -- Consumed-OK
    -- Report errors with State into M B
    (@StreamErrors.ParseError S E stream → ParserState.State S E → M B) →      -- Consumed-Error
    -- Return A with State S E and Hints into M B
    (A → ParserState.State S E → Errors.Hints (stream.Token) → M B) →          -- Empty-OK
    -- Report errors with State into M B
    (@StreamErrors.ParseError S E stream → ParserState.State S E → M B) →      -- Empty-Error
    M B

/-- Just add MonadParsec to Id. -/
abbrev Parsec E S [stream : Stream.Stream S] := @ParsecT S Id E stream Id.instMonadId

def runParsecT {E : Type} [s : Stream.Stream S] [m : Monad M] {A : Type}
               (parser : @ParsecT S M E s m A) (s₀: ParserState.State S E)
               : M (ParserState.Reply S E A) :=
  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  parser.unParser (ParserState.Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

def pPure [s : Stream.Stream S] [m : Monad M] (x : A) : @ParsecT S M E s m A :=
  ParsecT.mk $ fun b s _ _ eok _ => eok x s []

instance [s : Stream.Stream S] [m : Monad M] : Pure (@ParsecT S M E s m) where
  pure := pPure

def pMap [s : Stream.Stream S] [m : Monad M] (f: U → V) (x : @ParsecT S M E s m U) : @ParsecT S M E s m V :=
  ParsecT.mk (fun (b s cok cerr eok eerr) => (x.unParser b s (cok ∘ f) cerr (eok ∘ f) eerr))

instance [s : Stream.Stream S] [m : Monad M] : Functor (@ParsecT S M E s m) where
  map := pMap

def pBind [s : Stream.Stream S] [m : Monad M]
          (p : @ParsecT S M E s m A) (k : A → @ParsecT S M E s m B) : @ParsecT S M E s m B :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let mcok x s' hs := ParsecT.unParser (k x) B s' cok cerr (StateErrors.accHints hs cok) (StateErrors.withHints hs cerr)
    let meok x s' hs := ParsecT.unParser (k x) B s' cok cerr (StateErrors.accHints hs eok) (StateErrors.withHints hs eerr)
    p.unParser B s mcok cerr meok eerr

instance mprsₜ [s : Stream.Stream S] [m : Monad M] : Monad (@ParsecT S M E s m) where
  bind := pBind

/-- Alternative instance for ParsecT -/
def pZero [s : Stream.Stream S] [m: Monad M] : @ParsecT S M E s m A :=
  ParsecT.mk $ fun _ s _ _ _ eerr => eerr (StreamErrors.ParseError.trivial s.offset Option.none []) s

def pPlus [s : Stream.Stream S] [m : Monad M] [Ord (s.Token)] [BEq (Stream.Stream.Token S)]
          (p₁ : @ParsecT S M E s m A) (p₂ : @ParsecT S M E s m A) : @ParsecT S M E s m A :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let meer err ms :=
        let ncerr err' s' := cerr (StreamErrors.mergeError err' err) (ParserState.longestMatch ms s')
        let neok x s' hs := eok x s' (StreamErrors.toHints s'.offset err ++ hs)
        let neerr err' s' := eerr (StreamErrors.mergeError err' err) (ParserState.longestMatch ms s')
        p₂.unParser B s cok ncerr neok neerr
    p₁.unParser B s cok cerr eok eerr

instance altpₜ [s : Stream.Stream S] [Ord (s.Token)] [BEq (s.Token)] [m: Monad M] : Alternative (@ParsecT S M E s m) where
  failure := pZero
  orElse p₁ p₂ := pPlus p₁ (p₂ Unit.unit)

--=========================================================--
--================= IMPORTANT FUNCTIONS ===================--
--=========================================================--

def runParserT' [m : Monad M] {S : Type} [stream : Stream.Stream S] {E A : Type}
                (parser : @ParsecT S M E stream m A) (s₀ : ParserState.State S E)
                : M (ParserState.State S E × Util.Either (@Bundle.ParseErrorBundle S stream E) A) := do
  let reply ← runParsecT parser s₀
  let s₁ := reply.state
  pure $
    match reply.result with
    | .ok x => match Util.nonEmpty (reply.state.parseErrors) with
              | .none => (s₁, Util.Either.right x)
              | .some pes => (s₁, .left (Bundle.toBundle s₀ pes))
    | .err e => (s₁, Util.Either.left (Bundle.toBundle s₀ $ Util.NonEmptyList.cons e s₁.parseErrors))

def runParser' {S : Type} [stream : Stream.Stream S] {E A : Type}
               (parser : @Parsec E S stream A) (state : ParserState.State S E)
               : ParserState.State S E × Util.Either (@Bundle.ParseErrorBundle S stream E) A :=
  runParserT' parser state

def runParser {S : Type} [stream : Stream.Stream S] {E A : Type}
              (parser : @Parsec E S stream A) (sourceName : String) (xs : S)
              : Util.Either (@Bundle.ParseErrorBundle S stream E) A :=
  (runParser' parser (ParserState.initialState sourceName xs)).2

def parse [stream : Stream.Stream S] {E A : Type}
          (parser : @Parsec E S stream A) (sourceName : String) (xs : S)
          : Util.Either (@Bundle.ParseErrorBundle S stream E) A :=
  runParser parser sourceName xs

def parseTest [stream : Stream.Stream S] {E A : Type} [ToString A]
              (parser : @Parsec E S stream A) (xs : S)
              : IO Unit :=
  match parse parser "" xs with
  | .left e => IO.println "There were some errors."
  | .right y => IO.println y

end Parsec
