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

-- Convention, S is state, E is Error, T is token
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
  statePosState    : (PosState S)
  stateParseErrors : List (ParseError S E)

structure Hints (T: Type) where
  hints : List (ErrorItem T)

inductive Result (S E A: Type) [Stream S] where
| ok (x : A)
| err (e : ParseError S E)

structure Reply (S E A : Type) [Stream S] where
  state : State S E
  consumed : Bool
  result : Result S E A

structure ParsecT (E S: Type) (M: Type -> Type) (A: Type) [Stream S] where
  mk ::
    (unParser :
      (B : Type) -> (State S E) ->
      (A -> State S E -> Hints (Stream.Token S) -> M B) -> -- Consumed-OK
      (ParseError S E -> State S E -> M B) ->              -- Consumed-Error
      (A -> State S E -> Hints (Stream.Token S) -> M B) -> -- Empty-OK
      (ParseError S E -> State S E -> M B) ->              -- Empty-Error
      M B)

def pMap (E S: Type) [Stream S] (M: Type -> Type) (U V: Type) (f: U -> V) (x: ParsecT E S M U) : ParsecT E S M V  :=
  ParsecT.mk (λ (b s cok cerr eok eerr) => (x.unParser b s (cok ∘ f) cerr (eok ∘ f) eerr))

end Megaparsec
