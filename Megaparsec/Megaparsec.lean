import Std.Data.HashSet
import Mathlib.Algebra.Group.Defs -- for Monoid

namespace Megaparsec

/-- Util -/
def option (b : B) (f : A → B) (oa : Option A) : B :=
  match oa with
    | Option.none => b
    | Option.some x => f x

inductive Either (L: Type u) (R: Type v) where
| left (l : L)
| right (r : R)

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

def seqComp {M : Type u → Type v} [Monad M] (ma : M A) (mb : M B) :=
  ma >>= fun _ => mb

/-- Megaparsec datatypes -/

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
| cons (x: A) (xs: List A)
  deriving BEq

def nes (a : A) : NonEmptyList A :=
  NonEmptyList.cons a []

def nonEmptyString (s : String) : Option (NonEmptyList Char) :=
  match s with
    | { data := [] } => Option.none
    | { data := x :: xs} => Option.some $ NonEmptyList.cons x xs

inductive ErrorItem (T: Type) where
| tokens (t: NonEmptyList T)
| label (l: NonEmptyList Char)
| eof

abbrev Hints (T : Type) := List (List (ErrorItem T))

instance ord2beq [Ord T] : BEq T where
  -- beq x y := compare x y == Ordering.eq
  beq x := BEq.beq Ordering.eq ∘ compare x

def ord2compare [Ord T] (x y: T): Bool :=
  compare x y == Ordering.eq

def ord2beq_nel [Ord T] [BEq T] (x y: NonEmptyList T): Bool :=
  match x, y with
  | .cons u x₁, .cons v y₁ => ord2compare u v && List.instBEqList.beq x₁ y₁
  | .nil u, .nil v => ord2compare u v
  | _, _ => false

instance ord2beq_ei [Ord T] [BEq T] : BEq (ErrorItem T) where
  beq (u v: ErrorItem T) :=
    match u, v with
    | .tokens nelᵤ, .tokens nelᵥ => ord2beq_nel nelᵤ nelᵥ
    | .label nelᵤ, .label nelᵥ => ord2beq_nel nelᵤ nelᵥ
    | .eof, .eof => true
    | _, _ => false

def errorItemMax [Ord T] [BEq T] (e₁ : ErrorItem T) (e₂ : ErrorItem T) : ErrorItem T :=
  match ord2beq_ei.beq e₁ e₂ with
    | true => e₂
    | false => e₁

class Stream (S : Type) where
  Token : Type
  ordToken : Ord Token
  -- hashToken : Hashable Token
  -- beqEi : BEq (ErrorItem Token)
  -- hashEi : Hashable (ErrorItem Token)
  Tokens : Type
  ordTokens : Ord Tokens
  tokenToChunk : Token → Tokens
  tokensToChunk : List Token → Tokens
  chunkToTokens : Tokens → List Token
  chunkLength : Tokens → Nat
  take1 : S → Option (Token × S)
  takeN : Nat → S → Option (Tokens × S)
  takeWhile : (Token → Bool) → S → (Tokens × S)

def chunkEmpty [stream : Stream S] (s : stream.Tokens) : Bool :=
  stream.chunkLength s <= 0

-- Convention, S is state, E is Error, T is token, A is return type.
-- Convention for optimising currying is to apply E, S then M, and leave A for the last type argument.
-- Except for Result, Reply and ParseError where the order is S E A.

inductive ErrorFancy (E: Type) where
| fail (msg: String)
| indent (ord: Ordering) (fromPos: Pos) (uptoPos: Pos)
| custom (e: E)

inductive ParseError (E: Type) [stream: Stream S] where
| trivial (offset: Nat)
          (unexpected: Option (ErrorItem (stream.Token)))
          -- TODO: Switch to HashSet
          (expected: List (ErrorItem (stream.Token)))
| fancy (offset: Nat) (expected: List (ErrorFancy E))

def errorOffset [s: Stream S] (e: @ParseError S E s) : ℕ :=
  match e with
    | ParseError.trivial n _ _ => n
    | ParseError.fancy n _     => n

def mergeError [s: Stream S]
               [Ord (Stream.Token S)]
               [BEq (Stream.Token S)]
               (e₁: @ParseError S E s)
               (e₂: @ParseError S E s) : @ParseError S E s :=
  match (compare (@errorOffset S E s e₁) (@errorOffset S E s e₂)) with
    | Ordering.lt => e₂
    | Ordering.eq =>
        match (e₁, e₂) with
          | (ParseError.trivial s₁ u₁ p₁, ParseError.trivial _ u₂ p₂) =>
             match (u₁, u₂) with
               | (Option.none, Option.none) => ParseError.trivial s₁ Option.none (p₁ ++ p₂)
               | (Option.some x, Option.some y) => ParseError.trivial s₁ (Option.some (errorItemMax x y)) (p₁ ++ p₂)
               | (Option.none, Option.some x) => ParseError.trivial s₁ (Option.some x) (p₁ ++ p₂)
               | (Option.some x, Option.none)=> ParseError.trivial s₁ (Option.some x) (p₁ ++ p₂)
          | (ParseError.fancy _ _, ParseError.trivial _ _ _) => e₁
          | (ParseError.trivial _ _ _, ParseError.fancy _ _) => e₂
          | (ParseError.fancy s₁ x₁, ParseError.fancy _ x₂) => ParseError.fancy s₁ (x₁ ++ x₂)
    | Ordering.gt => e₁

def toHints [s : Stream S] (streamPos : ℕ) (e : @ParseError S E s) : Hints s.Token :=
  match e with
    | ParseError.fancy _ _ => []
    | ParseError.trivial errOffset _ ps =>
        if streamPos == errOffset
           then (if List.isEmpty ps then [] else [ps])
           else []

def refreshLastHint (h : Hints T) (m : Option (ErrorItem T)) : Hints T :=
  match (h,m) with
    | ([], _h) => []
    | (_ :: xs, Option.none) => xs
    | (_ :: xs, Option.some y) => [y] :: xs

structure State (S E: Type) [s: Stream S] where
  stateInput       : S
  stateOffset      : Nat
  statePosState    : PosState S
  stateParseErrors : List (@ParseError S E s)

def longestMatch [Stream S] (s₁: State S E) (s₂: State S E):  State S E :=
  match compare s₁.stateOffset s₂.stateOffset with
    | Ordering.lt => s₂
    | Ordering.eq => s₂
    | Ordering.gt => s₁

inductive Result (S E A: Type) [s: Stream S] where
| ok (x : A)
| err (e : @ParseError S E s)

structure Reply (S E A: Type) [Stream S] where
  state    : State S E
  consumed : Bool
  result   : Result S E A

structure ParsecT (E: Type) [stream: Stream S] [m: Monad M] (A: Type) where
  unParser :
    (B : Type) → (State S E) →
    -- Return A with State S E and Hints into M B
    (A → State S E → Hints (stream.Token) → M B) →    -- Consumed-OK
    -- Report errors with State into M B
    (@ParseError S E stream → State S E → M B) →      -- Consumed-Error
    -- Return A with State S E and Hints into M B
    (A → State S E → Hints (stream.Token) → M B) →    -- Empty-OK
    -- Report errors with State into M B
    (@ParseError S E stream → State S E → M B) →      -- Empty-Error
    M B

def runParsecT (E: Type) [s: Stream S] [m: Monad M] (A: Type) (x: @ParsecT S M E s m A) (s₀: State S E): M (Reply S E A) :=
  let run_cok  := fun a s₁ _h => pure ⟨s₁, true,  .ok a⟩
  let run_cerr := fun err s₁  => pure ⟨s₁, true,  .err err⟩
  let run_eok  := fun a s₁ _h => pure ⟨s₁, false, .ok a⟩
  let run_eerr := fun err s₁  => pure ⟨s₁, false, .err err⟩
  x.unParser (Reply S E A) s₀ run_cok run_cerr run_eok run_eerr

def pPure [s: Stream S] [m: Monad M] (x: A): @ParsecT S M E s m A :=
  ParsecT.mk $ fun b s _ _ eok _ => eok x s []

instance [s: Stream S] [m: Monad M]: Pure (@ParsecT S M E s m) where
  pure := pPure

def pMap [s: Stream S] [m: Monad M] (f: U → V) (x: @ParsecT S M E s m U): @ParsecT S M E s m V :=
  ParsecT.mk (fun (b s cok cerr eok eerr) => (x.unParser b s (cok ∘ f) cerr (eok ∘ f) eerr))

instance [s: Stream S] [m: Monad M]: Functor (@ParsecT S M E s m) where
  map := pMap

/-- Monad instance for ParsecT and related utilities -/

-- accHints' hs c results in “OK” continuation that will add given
-- hints @hs@ to third argument of original continuation c
def accHints [Stream S] {M : Type u → Type v}
               -- | Hints to add
             (hs₁ : Hints T)
               -- | An “OK” continuation to alter
             (c : A → State S E → Hints T → M B)
                -- | Altered “OK” continuation
             (x : A) (s : State S E) (hs₂ : Hints T) : M B :=
  c x s (hs₁ ++ hs₂)

-- withHints' hs c makes “error” continuation c use given hints hs.
def withHints [stream : Stream S] {M : Type u → Type v}
                -- | Hints to use
              (ps' : Hints (stream.Token))
                -- | Continuation to influence
              (c : @ParseError S E stream → State S E → M B)
                -- | First argument of resulting continuation
              (e : @ParseError S E stream) : State S E → M B :=
  match e with
    | ParseError.trivial pos us ps => c $ ParseError.trivial pos us (List.join (ps :: ps'))
    | _ => c e


def pBind [s: Stream S] [m: Monad M] (p : @ParsecT S M E s m A) (k : A → @ParsecT S M E s m B) : @ParsecT S M E s m B :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let mcok x s' hs := ParsecT.unParser (k x) B s' cok cerr (accHints hs cok) (withHints hs cerr)
    let meok x s' hs := ParsecT.unParser (k x) B s' cok cerr (accHints hs eok) (withHints hs eerr)
    p.unParser B s mcok cerr meok eerr

instance mprsₜ [s: Stream S] [m: Monad M] : Monad (@ParsecT S M E s m) where
  bind := pBind

/-- Alternative instance for ParsecT -/
def pZero [s: Stream S] [m: Monad M] : @ParsecT S M E s m A :=
  ParsecT.mk $ fun _ s _ _ _ eerr => eerr (ParseError.trivial s.stateOffset Option.none []) s

def pPlus [s: Stream S] [m: Monad M] [Ord (s.Token)] [BEq (Stream.Token S)]
          (p₁: @ParsecT S M E s m A) (p₂: @ParsecT S M E s m A) : @ParsecT S M E s m A :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let meer err ms :=
        let ncerr err' s' := cerr (mergeError err' err) (longestMatch ms s')
        let neok x s' hs := eok x s' (toHints s'.stateOffset err ++ hs)
        let neerr err' s' := eerr (mergeError err' err) (longestMatch ms s')
        p₂.unParser B s cok ncerr neok neerr
    p₁.unParser B s cok cerr eok eerr

instance altpₜ [s: Stream S] [Ord (s.Token)] [BEq (s.Token)] [m: Monad M] : Alternative (@ParsecT S M E s m) where
  failure := pZero
  orElse p₁ p₂ := pPlus p₁ (p₂ Unit.unit)

/-- MonadParsec class and their instances -/

-- | Monads M that implement primitive parsers
class MonadParsec (E S : Type) [Monad M] [Alternative M] [strm : Stream S] where
  -- | Stop parsing wherever we are, and report @err@
  parseError (A: Type) (err: @ParseError S E strm): M A
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
  withRecovery (A: Type) (phi: @ParseError S E strm → M A) (parser: M A): M A
  -- | Observes 'ParseError's as they happen, without backtracking.
  observing (A: Type) (parser: M A): M (@Either (@ParseError S E strm) A)
  -- | The parser at the end of the stream.
  eof: M Unit
  -- | Parser @'token' matcher expected@ accepts tokens for which @matcher@ returns '.just', accumulates '.noithing's into an 'Std.HashSet' for error reporting.
  -- token (A: Type) (matcher: Token → Option A) (acc: @Std.HashSet (ErrorItem strm.Token) strm.beqEi strm.hashEi): M A
  -- TODO: enable the token method as above ^
  token (A: Type) (matcher: strm.Token → Option A) (acc: List (ErrorItem strm.Token)): M A
  -- | Parser @'tokens' matcher chunk@ parses a chunk in a stream by comparing against @matcher@, backtracking on fail. For example: `tokens (==) "xyz"` would parse (Tokens "xyz") out of "xyzzy", leaving "zy" unparsed.
  -- NB! Empty target chunk always succeeds.
  tokens (A: Type) (matcher: strm.Tokens → strm.Tokens → Bool) (chunk: strm.Tokens): M strm.Tokens
  -- | Never fails to parse zero or more individual tokens based on a predicate. `takeWhileP (Just "name") predicate` is equivalent to `many (satisfy predicate <?> "name")`.
  takeWhileP (A: Type) (name: Option String) (predicate: strm.Token → Bool): M strm.Tokens
  -- | takeWhileP variant that fails if there were zero matches
  takeWhile1P (A: Type) (name: Option String) (predicate: strm.Token → Bool): M strm.Tokens
  -- | Backtracks if there aren't enough tokens in a stream to be returned as a chunk. Otherwise, take the amount of tokens and return the chunk
  takeP (A: Type) (name: Option String) (n: Nat): M strm.Tokens
  -- | Return current 'State' of the parser
  getParserState: M (State S E)
  -- | Update parser state with @phi@.
  updateParserState (phi: (State S E → State S E)): M Unit

def msₜ [m: Monad M]: Monad (StateT σ M) :=
  StateT.instMonadStateT
def asₜ [Monad A] [Alternative A]: Alternative (StateT σ A) :=
  StateT.instAlternativeStateT

/-- MonadParsec instance for ParsecT -/

def pLabel [stream : Stream S] (A : Type) (l : String) (p : @ParsecT S M E stream m A) : @ParsecT S M E stream m A :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
      let el := Option.map (@ErrorItem.label stream.Token) (nonEmptyString l)
      let cok' x s' hs :=
        match el with
          | Option.none => cok x s' (refreshLastHint hs Option.none)
          | Option.some _ => cok x s' hs
      let eok' x s' hs := eok x s' (refreshLastHint hs el)
      let eerr' err := eerr $
         match err with
          | ParseError.trivial pos us _ => ParseError.trivial pos us (option [] (fun x => [x]) el)
          | _ => err
      p.unParser B s cok' cerr eok' eerr'

def pNotFollowedBy [stream : Stream S] (A : Type) (p : @ParsecT S M E stream m A) : @ParsecT S M E stream m Unit :=
  ParsecT.mk $ fun B s _ _ eok eerr =>
    let input := s.stateInput
    let o := s.stateOffset
    let what := option ErrorItem.eof (ErrorItem.tokens ∘ nes ∘ fst) (stream.take1 input)
    let unexpect u := @ParseError.trivial S E stream o (Option.some u) []
    let cok' _ _ _ := eerr (unexpect what) s
    let cerr' _ _ := eok Unit.unit s []
    let eok' _ _ _ := eerr (unexpect what) s
    let eerr' _ _ := eok Unit.unit s []
    p.unParser B s cok' cerr' eok' eerr'

def pWithRecovery [stream : Stream S] (A : Type) (r : @ParseError S E stream → @ParsecT S M E stream m A) (p : @ParsecT S M E stream m A) :=
  ParsecT.mk $ fun B s cok cerr eok eerr =>
    let mcerr err ms :=
        let rcok x s' _ := cok x s' []
        let rcerr _ _ := cerr err ms
        let reok x s' _ := eok x s' (toHints s'.stateOffset err)
        let reerr _ _ := cerr err ms
        let p₁ := r err
        p₁.unParser B ms rcok rcerr reok reerr
    let meerr err ms :=
        let rcok x s' _ := cok x s' (toHints s'.stateOffset err)
        let rcerr _ _ := eerr err ms
        let reok x s' _ := eok x s' (toHints s'.stateOffset err)
        let reerr _ _ := eerr err ms
        let p₁ := r err
        p₁.unParser B ms rcok rcerr reok reerr
    p.unParser B s cok mcerr eok meerr

def pEof [stream : Stream S] : @ParsecT S M E stream m Unit :=
  ParsecT.mk $ fun _ s _ _ eok eerr =>
    let input := s.stateInput
    let o := s.stateOffset
    let pst := s.statePosState
    let de := s.stateParseErrors
    match stream.take1 input with
      | Option.none => eok Unit.unit s []
      | Option.some (x,_) =>
          let us := (Option.some ∘ ErrorItem.tokens ∘ nes) x
          let ps := [ ErrorItem.eof ]
          eerr (ParseError.trivial o us ps) (State.mk input o pst de)

instance (E S : Type) [m : Monad M] [stream : Stream S]
         [o : Ord stream.Token] [e : BEq stream.Token] :
         @MonadParsec (@ParsecT S M E stream m) E S (@mprsₜ S M E stream m) (@altpₜ S M E stream o e m) stream where
  parseError _ err := ParsecT.mk $ fun _ s _ _ _ eerr => eerr err s
  label := pLabel
  attempt _ p :=
    ParsecT.mk $ fun B s cok _ eok eerr =>
      let eerr' err _ := eerr err s
      p.unParser B s cok eerr' eok eerr'
  lookAhead _ p :=
    ParsecT.mk $ fun B s _ cerr eok eerr =>
      let eok' a _ _ := eok a s []
      p.unParser B s eok' cerr eok' eerr
  notFollowedBy := pNotFollowedBy
  withRecovery := pWithRecovery
  observing _ p := ParsecT.mk $ fun B s cok _ eok _ =>
    let cerr' err s' := cok (Either.left err) s' []
    let eerr' err s' := eok (Either.left err) s' (toHints s'.stateOffset err)
    p.unParser B s (cok ∘ Either.right) cerr' (eok ∘ Either.right) eerr'
  eof := pEof
  token A matcher ps := ParsecT.mk $ fun B s cok _ _ eerr =>
    let input := s.stateInput
    let o := s.stateOffset
    let pst := s.statePosState
    let de := s.stateParseErrors
    match stream.take1 input with
      | .none => eerr (.trivial o (.some .eof) ps) s
      | .some (c, cs) => match matcher c with
        | .none =>
            let us := (.some ∘ .tokens ∘ nes) c
            eerr (.trivial o us ps) s
        | .some x => cok x (State.mk cs (o + 1) pst de) []
  tokens A matcher chunk := ParsecT.mk $ fun B s₀ cok _ eok eerr =>
    let unexpect pos' u :=
      let us := pure u
      -- let ps := [ (@ErrorItem.tokens stream.Token chunk) ]
      let es := match stream.chunkToTokens chunk with
        | List.cons x xs => [ErrorItem.tokens $ NonEmptyList.cons x xs]
        | [] => [ErrorItem.label $ NonEmptyList.cons ' ' "Empty target chunk.".data]
        -- ^ This should never happen, because an empty target always succeeds by design
      ParseError.trivial pos' us es
    let len := stream.chunkLength chunk
    -- TODO: can we trick type system into using takeN from one `stream` with `stateInput` being another?
    match stream.takeN len s₀.stateInput with
      | .none => eerr (unexpect s₀.stateOffset ErrorItem.eof) s₀
      | .some (consumed, rest) =>
        if matcher chunk consumed then
          let s₁ := State.mk rest (s₀.stateOffset + len) s₀.statePosState s₀.stateParseErrors
          if chunkEmpty chunk then
            eok consumed s₁ []
          else
            cok consumed s₁ []
        else
          let oops := match stream.chunkToTokens consumed with
          | List.cons x xs => ErrorItem.tokens $ NonEmptyList.cons x xs
          | [] => ErrorItem.label $ NonEmptyList.cons ' ' "Nothing consumed.".data
          -- ^ This should never happen, because we handle chunkEmpty earlier on
          eerr (unexpect s₀.stateOffset oops) (State.mk s₀.stateInput s₀.stateOffset s₀.statePosState s₀.stateParseErrors)
  takeWhileP _ ml f :=
    ParsecT.mk $ fun _ s cok _ eok _ =>
      let input := s.stateInput
      let o := s.stateOffset
      let pst := s.statePosState
      let de := s.stateParseErrors
      let (ts, input') := stream.takeWhile f input
      let len := stream.chunkLength ts
      let hs := match ml >>= nonEmptyString with
                  | Option.none => []
                  | Option.some l => [[ErrorItem.label l]]
      if chunkEmpty ts
        then eok ts (State.mk input' (o + len) pst de) hs
        else cok ts (State.mk input' (o + len) pst de) hs
  takeWhile1P _ ml f := ParsecT.mk $ fun _ s cok _ _ eerr =>
      let input := s.stateInput
      let o := s.stateOffset
      let pst := s.statePosState
      let de := s.stateParseErrors
      let (ts, input') := stream.takeWhile f input
      let len := stream.chunkLength ts
      let el := ErrorItem.label <$> (ml >>= nonEmptyString)
      let hs := match el with
                  | Option.none => []
                  | Option.some l => [[l]]
      if chunkEmpty ts
        then
          let us := Option.some $
            match stream.take1 input with
              | Option.none => ErrorItem.eof
              | Option.some (t,_) => ErrorItem.tokens (nes t)
          let ps := option [] (fun x => [x]) el
          eerr (ParseError.trivial o us ps) (State.mk input o pst de)
        else cok ts (State.mk input' (o + len) pst de) hs
  takeP _ ml n := ParsecT.mk $ fun _ s cok _ _ eerr =>
      let input := s.stateInput
      let o := s.stateOffset
      let pst := s.statePosState
      let de := s.stateParseErrors
      -- let len := stream.chunkLength ts
      let el := ErrorItem.label <$> (ml >>= nonEmptyString)
      let ps := option [] (fun x => [x]) el
      match stream.takeN n input with
        | Option.none => eerr (ParseError.trivial o (pure ErrorItem.eof) ps) s
        | Option.some (ts, input') =>
            let len := stream.chunkLength ts
            if not (len == n)
            then eerr (ParseError.trivial (o + len) (pure ErrorItem.eof) ps) (State.mk input o pst de)
            else cok ts (State.mk input' (o + len) pst de) []
  getParserState := ParsecT.mk $ fun _ s _ _ eok _ => eok s s []
  updateParserState f := ParsecT.mk $ fun _ s _ _ eok _ => eok Unit.unit (f s) []

instance (E S : Type) [m: Monad M] [a: Alternative M]
         [s: Stream S] [mₚ: @MonadParsec M E S m a s] :
         @MonadParsec (StateT σ M) E S (@msₜ M σ m) (@asₜ M σ m a) s where
  parseError A err := liftM (mₚ.parseError A err)
  label A f st := (mₚ.label E S (A × σ) f) ∘ st
  attempt A st := mₚ.attempt E S (A × σ) ∘ st
  lookAhead A state x := mₚ.lookAhead E S (A × σ) (state x)
  notFollowedBy A state x := seqComp (mₚ.notFollowedBy E S A (fst <$> state x)) (pure (Unit.unit , x))
  withRecovery A cont state x := mₚ.withRecovery (A × σ) (fun e => (cont e) x) (state x)
  observing A f x := fixs x <$> (mₚ.observing (A × σ) (f x))
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S ms p)
  takeP A l n := liftM (mₚ.takeP E S l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

/-- RWS monad and its transformer and required utilities -/

def void [Monad M] (ma : M A) : M Unit :=
  (fun _ => Unit.unit) <$> ma

def RWST (R W S : Type u) (M : Type u → Type v) (A : Type u) : Type (max u v) :=
  R → S → M (A × S × W)

instance mrwsₜ (R W S : Type) [m : Monoid W] [Monad M] : Monad (RWST R W S M) where
  map f x := fun r s => do {
    let (a, s, w) <- x r s
    pure (f a, s, w)
  }
  pure x := fun _ s => pure (x,s,m.one)
  bind m k := fun r s => do {
    let (a, s', w) <- m r s
    let (b, s'', w') <- (k a) r s
    pure (b, s'', w * w') }

instance arwsₜ [Monoid W] [Monad M] [mₐ : Alternative M] : Alternative (RWST R W S M) where
  failure := fun _ _ => mₐ.failure
  orElse a b := fun r s => mₐ.orElse (a r s) (fun _ => b Unit.unit r s)

instance [Monad M] [m : Monoid W] : MonadLiftT M (RWST R W S M) where
  monadLift ma := fun _ s => do
    let a <- ma
    pure (a, s, m.one)

/-- MonadParsec instance for RWST -/

instance (E S W : Type) [m : Monoid W]
         [monad_inst : Monad M] [a : Alternative M] [s : Stream S]
         [mₚ : @MonadParsec M E S monad_inst a s]
         [MonadLiftT M (RWST R W S M)] : @MonadParsec (RWST R W S M) E S (@mrwsₜ M R W S m monad_inst) (@arwsₜ W M R S m monad_inst a) s where
  parseError A err := liftM (mₚ.parseError A err)
  label A n m := fun r s => mₚ.label E S (A × S × W) n (m r s)
  attempt A st := fun r s => mₚ.attempt E S (A × S × W) (st r s)
  lookAhead A st := fun r s => do
    let (x,_,_) <- mₚ.lookAhead E S (A × S × W) (st r s)
    pure (x,s,m.one)
  notFollowedBy A state := fun r s => do
    mₚ.notFollowedBy E S Unit (void (state r s))
    pure (Unit.unit, s, m.one)
  withRecovery A n m := fun r s => mₚ.withRecovery (A × S × W) (fun e => (n e) r s) (m r s)
  observing A m := fun r s => fixs' s <$> mₚ.observing (A × S × W) (m r s)
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S ms p)
  takeP A l n := liftM (mₚ.takeP E S l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

end Megaparsec
