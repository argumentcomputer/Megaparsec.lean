import Std.Data.HashSet

namespace Megaparsec

structure Pos where
  pos : Nat

structure SourcePos where
  sourceName : String
  sourceLine : Pos
  sourceColumn: Pos

class Stream (S: Type) where
  Token : Type
  ordToken : Ord Token
  beqToken : BEq Token
  Tokens : Type
  ordTokens : Ord Tokens
  tokenToChunk : Token -> Tokens
  tokensToChunk : List Token -> Tokens
  chunkToTokens : Tokens -> List Token
  chunkEmpty : Tokens -> Bool
  take1 : S -> Option (Token × S)
  taknN : Nat -> S -> Option (Token × S)
  takeWhile : (Token -> Bool) -> S -> (Tokens × S)

-- Convention, S is state, E is Error, T is token, A is return type.
-- Convention for optimising currying is to apply E, S then M, and leave A for the last type argument.
-- Except for Result, Reply and ParseError where the order is S E A.
structure PosState (S: Type) where
  pstateInput : S
  pstateOffset : Nat
  pstateSourcePos : SourcePos
  pstateLinePrefix : String

inductive NonEmptyList (A: Type) where
| nil (x: A)
| cons (x: A) (xs: NonEmptyList A)

inductive ErrorItem (T: Type) [BEq T] where
| tokens (t: NonEmptyList T)
| label (l: NonEmptyList Char)
| eof

inductive ErrorFancy (E: Type) where
| fail (msg: String)
| indent (ord: Ordering) (fromPos: Pos) (uptoPos: Pos)
| custom (e: E)

inductive ParseError (S E: Type) [Stream S] where
| trivial (offset: Nat) (unexpected: (@ErrorItem (Stream.Token S) (Stream.beqToken S))) (expected: List (ErrorItem (Stream.Token S)))
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

structure Either (L: Type u) (R: Type v) where
  left: L
  right: R

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

structure ParsecT (E S: Type) [Stream S] (M: Type -> Type) [Monad M] (A: Type) where
  unParser :
    (B : Type) -> (State S E) ->
    -- Return A with State S E and Hints into M B
    (A -> State S E -> Hints (Stream.Token S) -> M B) -> -- Consumed-OK
    -- Report errors with State into M B
    (ParseError S E -> State S E -> M B) ->              -- Consumed-Error
    -- Return A with State S E and Hints into M B
    (A -> State S E -> Hints (Stream.Token S) -> M B) -> -- Empty-OK
    -- Report errors with State into M B
    (ParseError S E -> State S E -> M B) ->              -- Empty-Error
    M B

def runParsecT (E S: Type) [Stream S] (M: Type -> Type) [Monad M] (A: Type) (x: ParsecT E S M A) (s₀: State S E): M (Reply S E A) :=
  -- I bet there's a way to apply types to a list of four functions with Applicative or something, but it's good enough for the time being.
  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  x.unParser (Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

def pMap (E S: Type) [Stream S] (M: Type -> Type) [Monad M] (U V: Type) (f: U -> V) (x: ParsecT E S M U) : ParsecT E S M V  :=
  ParsecT.mk (λ (b s cok cerr eok eerr) => (x.unParser b s (cok ∘ f) cerr (eok ∘ f) eerr))

-- | Monads M that implement primitive parsers
class MonadParsec (E S: Type) [Stream S] (M: Type -> Type) [Monad M] [Alternative M] where
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
  withRecovery (A: Type) (phi: ParseError S E -> M A) (parser: M A): M A
  -- | Observes 'ParseError's as they happen, without backtracking.
  observing (A: Type) (parser: M A): M (@Either (ParseError S E) A)
  -- | The parser at the end of the Stream.
  eof: M Unit
  -- |
  token (A: Type) (matcher: Token -> Maybe A) (acc: Std.HashSet (ErrorItem Stream.Token)): M A

-- #check StateT
-- #check liftM
-- #check "Esiet sveicināti!"
-- #check Unit

end Megaparsec
