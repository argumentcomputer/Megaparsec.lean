import Megaparsec.Types
import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors

namespace Parsec

/-!
Parsec transformer and abbreviation runners and relevant instances.

Please find the most important functions for the users in the end of the file.
-/

/-- Parsec transformer, designed to add MonadParsec capability to any given monad M. -/
structure ParsecT (E : Type) [stream : Stream.Stream S] [m : Monad M] (A : Type) where
  -- TODO: Rewrite it as Lean 4 transformers (with `def`).
  unParser :
    (B : Type) → (Types.State S E) →
    -- Return A with State S E and Hints into M B
    (A → Types.State S E → Errors.Hints (stream.Token) → M B) →    -- Consumed-OK
    -- Report errors with State into M B
    (@StreamErrors.ParseError S E stream → Types.State S E → M B) →      -- Consumed-Error
    -- Return A with State S E and Hints into M B
    (A → Types.State S E → Errors.Hints (stream.Token) → M B) →    -- Empty-OK
    -- Report errors with State into M B
    (@StreamErrors.ParseError S E stream → Types.State S E → M B) →      -- Empty-Error
    M B

/-- Just add MonadParsec to Id. -/
abbrev Parsec E S [stream : Stream.Stream S] := @ParsecT S Id E stream Id.instMonadId

def runParsecT (E : Type) [s : Stream.Stream S]
               [m : Monad M] (A : Type)
               (x : @ParsecT S M E s m A) (s₀: Types.State S E) : M (Types.Reply S E A) :=
  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  x.unParser (Types.Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

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
    let mcok x s' hs := ParsecT.unParser (k x) B s' cok cerr (Types.accHints hs cok) (Types.withHints hs cerr)
    let meok x s' hs := ParsecT.unParser (k x) B s' cok cerr (Types.accHints hs eok) (Types.withHints hs eerr)
    p.unParser B s mcok cerr meok eerr

instance mprsₜ [s : Stream.Stream S] [m : Monad M] : Monad (@ParsecT S M E s m) where
  bind := pBind

/-- Alternative instance for ParsecT -/
def pZero [s : Stream.Stream S] [m: Monad M] : @ParsecT S M E s m A :=
  ParsecT.mk $ fun _ s _ _ _ eerr => eerr (StreamErrors.ParseError.trivial s.stateOffset Option.none []) s

def pPlus [s : Stream.Stream S] [m : Monad M] [Ord (s.Token)] [BEq (Stream.Stream.Token S)]
          (p₁ : @ParsecT S M E s m A) (p₂ : @ParsecT S M E s m A) : @ParsecT S M E s m A :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let meer err ms :=
        let ncerr err' s' := cerr (StreamErrors.mergeError err' err) (Types.longestMatch ms s')
        let neok x s' hs := eok x s' (StreamErrors.toHints s'.stateOffset err ++ hs)
        let neerr err' s' := eerr (StreamErrors.mergeError err' err) (Types.longestMatch ms s')
        p₂.unParser B s cok ncerr neok neerr
    p₁.unParser B s cok cerr eok eerr

instance altpₜ [s : Stream.Stream S] [Ord (s.Token)] [BEq (s.Token)] [m: Monad M] : Alternative (@ParsecT S M E s m) where
  failure := pZero
  orElse p₁ p₂ := pPlus p₁ (p₂ Unit.unit)

--=========================================================--
--================= IMPORTANT FUNCTIONS ===================--
--=========================================================--

-- def parse [Stream S] (Parsec E S A) String S : Util.Either ()

end Parsec