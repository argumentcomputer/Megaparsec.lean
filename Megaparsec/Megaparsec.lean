import Std.Data.HashSet
import Mathlib.Algebra.Group.Defs -- for Monoid

namespace Megaparsec

structure Pos where
  pos : Nat

structure SourcePos where
  sourceName : String
  sourceLine : Pos
  sourceColumn: Pos

structure PosState (S: Type) where
  pstateInput : S
  pstateOffset : Nat
  pstateSourcePos : SourcePos
  pstateLinePrefix : String

inductive NonEmptyList (A: Type) where
| nil (x: A)
| cons (x: A) (xs: NonEmptyList A)
  deriving BEq

inductive ErrorItem (T: Type) where
| tokens (t: NonEmptyList T)
| label (l: NonEmptyList Char)
| eof

def ord2beq (T: Type) [Ord T] (x y: T): Bool :=
  compare x y == Ordering.eq

def ord2beq_nel (T: Type) [Ord T] (x y: NonEmptyList T): Bool :=
  match x, y with
  | .cons u x₁, .cons v y₁ => ord2beq T u v && ord2beq_nel T x₁ y₁
  | .nil u, .nil v => ord2beq T u v
  | _, _ => false

instance ord2beq_ei [Ord T]: BEq (ErrorItem T) where
  beq (u v: ErrorItem T) :=
    match u, v with
    | .tokens nelᵤ, .tokens nelᵥ => ord2beq_nel T nelᵤ nelᵥ
    | .label nelᵤ, .label nelᵥ => ord2beq_nel Char nelᵤ nelᵥ
    | .eof, .eof => true
    | _, _ => false

class Stream (S: Type) where
  Token : Type
  ordToken : Ord Token
  hashToken : Hashable Token
  beqEi : BEq (ErrorItem Token)
  hashEi : Hashable (ErrorItem Token)
  Tokens : Type
  ordTokens : Ord Tokens
  tokenToChunk : Token → Tokens
  tokensToChunk : List Token → Tokens
  chunkToTokens : Tokens → List Token
  chunkEmpty : Tokens → Bool
  take1 : S → Option (Token × S)
  taknN : Nat → S → Option (Token × S)
  takeWhile : (Token → Bool) → S → (Tokens × S)

-- Convention, S is state, E is Error, T is token, A is return type.
-- Convention for optimising currying is to apply E, S then M, and leave A for the last type argument.
-- Except for Result, Reply and ParseError where the order is S E A.

inductive ErrorFancy (E: Type) where
| fail (msg: String)
| indent (ord: Ordering) (fromPos: Pos) (uptoPos: Pos)
| custom (e: E)

inductive ParseError (S E: Type) [Stream S] where
| trivial (offset: Nat) (unexpected: ErrorItem (Stream.Token S)) (expected: List (ErrorItem (Stream.Token S)))
| fancy (offset: Nat) (expected : List (ErrorFancy E))

structure State (S E: Type) [Stream S] where
  stateInput       : S
  stateOffset      : Nat
  statePosState    : PosState S
  stateParseErrors : List (ParseError S E)

abbrev Hints (T : Type) := List (ErrorItem T)

inductive Result (S E A: Type) [Stream S] where
| ok (x : A)
| err (e : ParseError S E)

inductive Either (L: Type u) (R: Type v) where
| left (l : L)
| right (r : R)

inductive Maybe (R: Type u) where
| just (ok: R)
| nothing

inductive Surely (L: Type u) where
| ok
| error (err: L)

structure Reply (S E A: Type) [Stream S] where
  state    : State S E
  consumed : Bool
  result   : Result S E A

structure ParsecT (E S: Type) [stream: Stream S] (M: Type → Type) [Monad M] (A: Type) where
  unParser :
    (B : Type) → (State S E) →
    -- Return A with State S E and Hints into M B
    (A → State S E → Hints (stream.Token) → M B) → -- Consumed-OK
    -- Report errors with State into M B
    (ParseError S E → State S E → M B) →            -- Consumed-Error
    -- Return A with State S E and Hints into M B
    (A → State S E → Hints (stream.Token) → M B) → -- Empty-OK
    -- Report errors with State into M B
    (ParseError S E → State S E → M B) →            -- Empty-Error
    M B

def runParsecT (E S: Type) [Stream S] (M: Type → Type) [Monad M] (A: Type) (x: ParsecT E S M A) (s₀: State S E): M (Reply S E A) :=
  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  x.unParser (Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

def pPure [Stream S] [Monad M] (x: A): (ParsecT E S M A) :=
  ParsecT.mk $ λ b s _ _ eok _ => eok x s []

instance [Stream S] [Monad M]: Pure (ParsecT E S M) where
  pure := pPure

def pMap [Stream S] [Monad M] (f: U → V) (x: ParsecT E S M U): ParsecT E S M V :=
  ParsecT.mk (λ (b s cok cerr eok eerr) => (x.unParser b s (cok ∘ f) cerr (eok ∘ f) eerr))

instance [Stream S] [Monad M]: Functor (ParsecT E S M) where
  map := pMap


-- | Monads M that implement primitive parsers
class MonadParsec (E S : Type) (M: Type → Type) [Monad M] [Alternative M] [stream : Stream S] where
  -- | Stop parsing wherever we are, and report @err@
  parseError (A: Type) (err: ParseError S E): M A
  -- | If there's no input consumed by @parser@, labels expected token with name @name_override@
  label (A: Type) (name_override: String) (parser: M A): M A
  -- | Hides expected token error messages when @parser@ fails
  hidden (A: Type) (parser: M A): M A :=
    label A "" parser
  -- | Attempts to parse with @parser@ and backtracks on failure, for arbitrary look ahead. See megaparsec docs for pitfalls:
  -- https://hackage.haskell.org/package/megaparsec-9.2.1/docs/src/Text.Megaparsec.Class.html#try
  attempt (A: Type) (parser: M A): M A
  -- | Uses @parser@ to look ahead without consuming. If @parser@ fails, fail. Combine with 'attempt' if the latter is undesirable.
  lookAhead (A: Type) (parser: M A): M A
  -- | Succeeds if @parser@ fails without consuming or modifying parser state, useful for "longest match" rule implementaiton.
  notFollowedBy (A: Type) (parser: M A): M Unit
  -- | Uses @phi@ to recover from failure in @parser@.
  withRecovery (A: Type) (phi: ParseError S E → M A) (parser: M A): M A
  -- | Observes 'ParseError's as they happen, without backtracking.
  observing (A: Type) (parser: M A): M (@Either (ParseError S E) A)
  -- | The parser at the end of the Stream.
  eof: M Unit
  -- | Parser @'token' matcher expected@ accepts tokens for which @matcher@ returns '.just', accumulates '.noithing's into an 'Std.HashSet' for error reporting.
  token (A: Type) (matcher: Token → Maybe A) (acc: @Std.HashSet (ErrorItem stream.Token) stream.beqEi stream.hashEi): M A
  -- | Parser @'tokens' matcher chunk@ parses a chunk in a stream by comparing against @matcher@, backtracking on fail. For example: `tokens (==) "xyz"` would parse (Tokens "xyz") out of "xyzzy", leaving "zy" unparsed.
  tokens (A: Type) (matcher: Tokens → Tokens → Bool) (chunk: Tokens): M Tokens
  -- | Never fails to parse zero or more individual tokens based on a predicate. `takeWhileP (Just "name") predicate` is equivalent to `many (satisfy predicate <?> "name")`.
  takeWhileP (A: Type) (name: Maybe String) (predicate: Token → Bool): M Tokens
  -- | takeWhileP variant that fails if there were zero matches
  takeWhile1P (A: Type) (name: Maybe String) (predicate: Token → Bool): M Tokens
  -- | Backtracks if there aren't enough tokens in a stream to be returned as a chunk. Otherwise, take the amount of tokens and return the chunk
  takeP (A: Type) (name: Maybe String) (n: Nat): M Tokens
  -- | Return current 'State' of the parser
  getParserState: M (State S E)
  -- | Update parser state with @phi@.
  updateParserState (phi: (State S E → State S E)): M Unit


-- util

def fixs {A B C : Type} (c : C) : Either A (B × C) → (Either A B) × C
  | .left a => ⟨ .left a, c ⟩
  | .right ⟨ a, b ⟩ => ⟨ .right a, c ⟩

def fixs' {A B C W : Type} [m : Monoid W] (c : C) : Either A (B × C × W) → (Either A B) × C × W
  | .left a => ⟨ .left a, c, m.one ⟩
  | .right ⟨ a, b, w ⟩ => ⟨ .right a, c, w ⟩

def updatePair {A B C : Type} (c : C) : A × B → A × C
  | ⟨ a, _ ⟩ => ⟨ a, c ⟩

def fst {A B : Type} : A × B → A
  | ⟨ a, _⟩ => a 

def seqComp {A B : Type} {M : Type → Type} [Monad M] (ma : M A) (mb : M B) :=
  ma >>= λ _ => mb
--

instance (E S : Type) [Monad M] [Alternative M] [Stream S] [mₚ: MonadParsec E S M] : MonadParsec E S (StateT σ M) where
  parseError A err := liftM (mₚ.parseError A err)
  label A f st := (mₚ.label E S (A × σ) f) ∘ st
  attempt A st := mₚ.attempt E S (A × σ) ∘ st
  lookAhead A state x := mₚ.lookAhead E S (A × σ) (state x)
  notFollowedBy A state x := seqComp (mₚ.notFollowedBy E S A (fst <$> state x)) (pure (Unit.unit , x))
  withRecovery A cont state x := mₚ.withRecovery (A × σ) (fun e => (cont e) x) (state x)
  observing A f x := fixs x <$> (mₚ.observing (A × σ) (f x))
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S A e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S A ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S A ms p)
  takeP A l n := liftM (mₚ.takeP E S A l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

-- | RWS monad and its transformer and 

def void {A : Type} {M : Type → Type} [Monad M] (ma : M A) : M Unit :=
  (λ _ => Unit.unit) <$> ma

def RWST (R W S : Type u) (M : Type u → Type v) (A : Type u) : Type (max u v) :=
  R → S → M (A × S × W)

instance (R W S : Type) (M : Type → Type) [m : Monoid W]  [Monad M] : Monad (RWST R W S M) where
  map f x := λ r s => do {
    let (a, s, w) <- x r s
    pure (f a, s, w)
  }
  pure x := λ _ s => pure (x,s,m.one)
  bind m k := λ r s => do {
    let (a, s', w) <- m r s
    let (b, s'', w') <- (k a) r s
    pure (b, s'', w * w') }

instance (R W S : Type) (M : Type → Type) 
         [Monoid W] [Monad M] [mₐ : Alternative M] : Alternative (RWST R W S M) where
  failure := λ _ _ => mₐ.failure
  orElse a b := λ r s => mₐ.orElse (a r s) (λ _ => b Unit.unit r s)

instance (E S W : Type) (M : Type → Type) [Monad M] [m : Monoid W] : MonadLiftT M (RWST R W S M) where
  monadLift ma := λ _ s => do
    let a <- ma
    pure (a, s, m.one)
    
-- MonadParsec instance for RWST

instance (E S W : Type) [m : Monoid W] (M : Type → Type)
         [Monad M] [Alternative M] [Stream S]
         [mₚ : MonadParsec E S M] 
         [MonadLiftT M (RWST R W S M)] : MonadParsec E S (RWST R W S M) where
  parseError A err := liftM (mₚ.parseError A err)
  label A n m := λ r s => mₚ.label E S (A × S × W) n (m r s)
  attempt A st := λ r s => mₚ.attempt E S (A × S × W) (st r s)
  lookAhead A st := λ r s => do
    let (x,_,_) <- mₚ.lookAhead E S (A × S × W) (st r s)
    pure (x,s,m.one)
  notFollowedBy A state := λ r s => do
    mₚ.notFollowedBy E S Unit (void (state r s))
    pure (Unit.unit, s, m.one)
  withRecovery A n m := λ r s => mₚ.withRecovery (A × S × W) (fun e => (n e) r s) (m r s)
  observing A m := λ r s => fixs' s <$> mₚ.observing (A × S × W) (m r s)
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S A e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S A ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S A ms p)
  takeP A l n := liftM (mₚ.takeP E S A l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

end Megaparsec
