namespace Megaparsec

structure Pos where
  pos : Nat

structure SourcePos where
  sourceName : String
  sourceLine : Pos
  sourceColumn: Pos

class Stream (S: Type) where
  Token : Type
  Tokens : Type
  ordToken  : Ord Token
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
-- Except for Result and Reply, where the order is S E A.
structure PosState (S: Type) where
  pstateInput : S
  pstateOffset : Nat
  pstateSourcePos : SourcePos
  pstateLinePrefix : String

inductive NonEmptyList (A: Type) where
| nil (x: A)
| cons (x: A) (xs: NonEmptyList A)

inductive ErrorItem (T: Type) where
| tokens (t: NonEmptyList T)
| label (l: NonEmptyList Char)
| eof

inductive ErrorFancy (E: Type) where
| fail (msg: String)
| indent (ord: Ordering) (fromPos: Pos) (uptoPos: Pos)
| custom (e: E)

inductive ParseError (S E: Type) [Stream S] where
| trivial (offset: Nat) (unexpected: (ErrorItem (Stream.Token S))) (expected: List (ErrorItem (Stream.Token S)))
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

end Megaparsec
