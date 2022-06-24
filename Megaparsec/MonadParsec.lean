import Megaparsec.Parsec
import Megaparsec.RWST
import Megaparsec.Stream
import Megaparsec.ParserState
import Megaparsec.NEList

namespace MonadParsec

/-- MonadParsec class and their instances -/

-- | Monads M that implement primitive parsers
class MonadParsec (E S : Type) [Monad M] [Alternative M] [strm : Stream.Stream S] where
  -- | Stop parsing wherever we are, and report @err@
  parseError (A : Type) (err : @StreamErrors.ParseError S E strm): M A
  -- | If there's no input consumed by @parser@, labels expected token with name @name_override@
  label (A : Type) (name_override : String) (parser : M A): M A
  -- | Hides expected token error messages when @parser@ fails
  hidden (A : Type) (parser : M A): M A :=
    label A "" parser
  -- | Attempts to parse with @parser@ and backtracks on failure, for arbitrary look ahead. See megaparsec docs for pitfalls:
  -- https://hackage.haskell.org/package/megaparsec-9.2.1/docs/src/Text.Megaparsec.Class.html#try
  attempt (A : Type) (parser : M A): M A
  -- | Uses @parser@ to look ahead without consuming. If @parser@ fails, fail. Combine with 'attempt' if the latter is undesirable.
  lookAhead (A : Type) (parser : M A): M A
  -- | Succeeds if @parser@ fails without consuming or modifying parser state, useful for "longest match" rule implementaiton.
  notFollowedBy (A : Type) (parser : M A): M Unit
  -- | Uses @phi@ to recover from failure in @parser@.
  withRecovery (A : Type) (phi : @StreamErrors.ParseError S E strm → M A) (parser: M A): M A
  -- | Observes 'ParseError's as they happen, without backtracking.
  observing (A : Type) (parser : M A): M (@Util.Either (@StreamErrors.ParseError S E strm) A)
  -- | The parser at the end of the stream.
  eof : M Unit
  -- | Parser @'token' matcher expected@ accepts tokens for which @matcher@ returns '.just', accumulates '.noithing's into an 'Std.HashSet' for error reporting.
  -- token (A: Type) (matcher: Token → Option A) (acc: @Std.HashSet (ErrorItem strm.Token) strm.beqEi strm.hashEi): M A
  -- TODO: enable the token method as above ^
  token (A : Type) (matcher : strm.Token → Option A) (acc : List (Errors.ErrorItem strm.Token)) : M A
  -- | Parser @'tokens' matcher chunk@ parses a chunk in a stream by comparing against @matcher@, backtracking on fail. For example: `tokens (==) "xyz"` would parse (Tokens "xyz") out of "xyzzy", leaving "zy" unparsed.
  -- NB! Empty target chunk always succeeds.
  tokens (A : Type) (matcher : strm.Tokens → strm.Tokens → Bool) (chunk : strm.Tokens) : M strm.Tokens
  -- | Never fails to parse zero or more individual tokens based on a predicate. `takeWhileP (Just "name") predicate` is equivalent to `many (satisfy predicate <?> "name")`.
  takeWhileP (A : Type) (name : Option String) (predicate : strm.Token → Bool) : M strm.Tokens
  -- | takeWhileP variant that fails if there were zero matches
  takeWhile1P (A : Type) (name : Option String) (predicate : strm.Token → Bool) : M strm.Tokens
  -- | Backtracks if there aren't enough tokens in a stream to be returned as a chunk. Otherwise, take the amount of tokens and return the chunk
  takeP (A : Type) (name : Option String) (n : Nat) : M strm.Tokens
  -- | Return current 'State' of the parser
  getParserState: M (ParserState.State S E)
  -- | Update parser state with @phi@.
  updateParserState (phi : (ParserState.State S E → ParserState.State S E)) : M Unit

def msₜ [m : Monad M] : Monad (StateT σ M) :=
  StateT.instMonadStateT
def asₜ [Monad A] [Alternative A] : Alternative (StateT σ A) :=
  StateT.instAlternativeStateT

/-- MonadParsec instance for ParsecT -/

def pLabel [stream : Stream.Stream S] (A : Type) (l : String) (p : @Parsec.ParsecT S M E stream m A) : @Parsec.ParsecT S M E stream m A :=
  Parsec.ParsecT.mk $ fun B s cok cerr eok eerr =>
      let el := Option.map (@Errors.ErrorItem.label stream.Token) (NEList.nonEmptyString l)
      let cok' x s' hs :=
        match el with
          | Option.none => cok x s' (StreamErrors.refreshLastHint hs Option.none)
          | Option.some _ => cok x s' hs
      let eok' x s' hs := eok x s' (StreamErrors.refreshLastHint hs el)
      let eerr' err := eerr $
         match err with
          | StreamErrors.ParseError.trivial pos us _ => StreamErrors.ParseError.trivial pos us (Util.option [] (fun x => [x]) el)
          | _ => err
      p.unParser B s cok' cerr eok' eerr'

def pNotFollowedBy [stream : Stream.Stream S] (A : Type) (p : @Parsec.ParsecT S M E stream m A) : @Parsec.ParsecT S M E stream m Unit :=
  Parsec.ParsecT.mk $ fun B s _ _ eok eerr =>
    let input := s.input
    let o := s.offset
    let what := Util.option Errors.ErrorItem.eof (Errors.ErrorItem.tokens ∘ (NEList.NEList.uno) ∘ Util.fst) (stream.take1 input)
    let unexpect u := @StreamErrors.ParseError.trivial S E stream o (Option.some u) []
    let cok' _ _ _ := eerr (unexpect what) s
    let cerr' _ _ := eok Unit.unit s []
    let eok' _ _ _ := eerr (unexpect what) s
    let eerr' _ _ := eok Unit.unit s []
    p.unParser B s cok' cerr' eok' eerr'

def pWithRecovery [stream : Stream.Stream S] (A : Type)
                  (r : @StreamErrors.ParseError S E stream → @Parsec.ParsecT S M E stream m A)
                  (p : @Parsec.ParsecT S M E stream m A) :=
  Parsec.ParsecT.mk $ fun B s cok cerr eok eerr =>
    let mcerr err ms :=
        let rcok x s' _ := cok x s' []
        let rcerr _ _ := cerr err ms
        let reok x s' _ := eok x s' (StreamErrors.toHints s'.offset err)
        let reerr _ _ := cerr err ms
        let p₁ := r err
        p₁.unParser B ms rcok rcerr reok reerr
    let meerr err ms :=
        let rcok x s' _ := cok x s' (StreamErrors.toHints s'.offset err)
        let rcerr _ _ := eerr err ms
        let reok x s' _ := eok x s' (StreamErrors.toHints s'.offset err)
        let reerr _ _ := eerr err ms
        let p₁ := r err
        p₁.unParser B ms rcok rcerr reok reerr
    p.unParser B s cok mcerr eok meerr

def pEof [stream : Stream.Stream S] : @Parsec.ParsecT S M E stream m Unit :=
  Parsec.ParsecT.mk $ fun _ s _ _ eok eerr =>
    let input := s.input
    let o := s.offset
    let pst := s.posState
    let de := s.parseErrors
    match stream.take1 input with
      | Option.none => eok Unit.unit s []
      | Option.some (x,_) =>
          let us := (Option.some ∘ Errors.ErrorItem.tokens ∘ NEList.NEList.uno) x
          let ps := [ Errors.ErrorItem.eof ]
          eerr (StreamErrors.ParseError.trivial o us ps) (ParserState.State.mk input o pst de)

instance (E S : Type) [m : Monad M] [stream : Stream.Stream S]
         [o : Ord stream.Token] [e : BEq stream.Token] :
         @MonadParsec (@Parsec.ParsecT S M E stream m) E S (@Parsec.mprsₜ S M E stream m) (@Parsec.altpₜ S M E stream o e m) stream where
  parseError _ err := Parsec.ParsecT.mk $ fun _ s _ _ _ eerr => eerr err s
  label := pLabel
  attempt _ p :=
    Parsec.ParsecT.mk $ fun B s cok _ eok eerr =>
      let eerr' err _ := eerr err s
      p.unParser B s cok eerr' eok eerr'
  lookAhead _ p :=
    Parsec.ParsecT.mk $ fun B s _ cerr eok eerr =>
      let eok' a _ _ := eok a s []
      p.unParser B s eok' cerr eok' eerr
  notFollowedBy := pNotFollowedBy
  withRecovery := pWithRecovery
  observing _ p := Parsec.ParsecT.mk $ fun B s cok _ eok _ =>
    let cerr' err s' := cok (Util.Either.left err) s' []
    let eerr' err s' := eok (Util.Either.left err) s' (StreamErrors.toHints s'.offset err)
    p.unParser B s (cok ∘ Util.Either.right) cerr' (eok ∘ Util.Either.right) eerr'
  eof := pEof
  token A matcher ps := Parsec.ParsecT.mk $ fun B s cok _ _ eerr =>
    let input := s.input
    let o := s.offset
    let pst := s.posState
    let de := s.parseErrors
    match stream.take1 input with
      | .none => eerr (.trivial o (.some .eof) ps) s
      | .some (c, cs) => match matcher c with
        | .none =>
            let us := (.some ∘ .tokens ∘ NEList.NEList.uno) c
            eerr (.trivial o us ps) s
        | .some x => cok x (ParserState.State.mk cs (o + 1) pst de) []
  tokens A matcher chunk := Parsec.ParsecT.mk $ fun B s₀ cok _ eok eerr =>
    let unexpect pos' u :=
      let us := pure u
      -- let ps := [ (@ErrorItem.tokens stream.Token chunk) ]
      let es := match stream.chunkToTokens chunk with
        | List.cons x xs => [Errors.ErrorItem.tokens $ NEList.toNEList x xs]
        | [] => [Errors.ErrorItem.label $ NEList.toNEList ' ' "Empty target chunk.".data]
        -- ^ This should never happen, because an empty target always succeeds by design
      StreamErrors.ParseError.trivial pos' us es
    let len := stream.chunkLength chunk
    -- TODO: can we trick type system into using takeN from one `stream` with `input` being another?
    match stream.takeN len s₀.input with
      | .none => eerr (unexpect s₀.offset Errors.ErrorItem.eof) s₀
      | .some (consumed, rest) =>
        if matcher chunk consumed then
          let s₁ := ParserState.State.mk rest (s₀.offset + len) s₀.posState s₀.parseErrors
          if Stream.chunkEmpty chunk then
            eok consumed s₁ []
          else
            cok consumed s₁ []
        else
          let oops := match stream.chunkToTokens consumed with
          | List.cons x xs => Errors.ErrorItem.tokens $ NEList.toNEList x xs
          | [] => Errors.ErrorItem.label $ NEList.toNEList ' ' "Nothing consumed.".data
          -- ^ This should never happen, because we handle chunkEmpty earlier on
          eerr (unexpect s₀.offset oops) (ParserState.State.mk s₀.input s₀.offset s₀.posState s₀.parseErrors)
  takeWhileP _ ml f :=
    Parsec.ParsecT.mk $ fun _ s cok _ eok _ =>
      let input := s.input
      let o := s.offset
      let pst := s.posState
      let de := s.parseErrors
      let (ts, input') := stream.takeWhile f input
      let len := stream.chunkLength ts
      let hs := match ml >>= NEList.nonEmptyString with
                  | Option.none => []
                  | Option.some l => [[Errors.ErrorItem.label l]]
      if Stream.chunkEmpty ts
        then eok ts (ParserState.State.mk input' (o + len) pst de) hs
        else cok ts (ParserState.State.mk input' (o + len) pst de) hs
  takeWhile1P _ ml f := Parsec.ParsecT.mk $ fun _ s cok _ _ eerr =>
      let input := s.input
      let o := s.offset
      let pst := s.posState
      let de := s.parseErrors
      let (ts, input') := stream.takeWhile f input
      let len := stream.chunkLength ts
      let el := Errors.ErrorItem.label <$> (ml >>= NEList.nonEmptyString)
      let hs := match el with
                  | Option.none => []
                  | Option.some l => [[l]]
      if Stream.chunkEmpty ts
        then
          let us := Option.some $
            match stream.take1 input with
              | Option.none => Errors.ErrorItem.eof
              | Option.some (t,_) => Errors.ErrorItem.tokens (NEList.NEList.uno t)
          let ps := Util.option [] (fun x => [x]) el
          eerr (StreamErrors.ParseError.trivial o us ps) (ParserState.State.mk input o pst de)
        else cok ts (ParserState.State.mk input' (o + len) pst de) hs
  takeP _ ml n := Parsec.ParsecT.mk $ fun _ s cok _ _ eerr =>
      let input := s.input
      let o := s.offset
      let pst := s.posState
      let de := s.parseErrors
      let el := Errors.ErrorItem.label <$> (ml >>= NEList.nonEmptyString)
      let ps := Util.option [] (fun x => [x]) el
      match stream.takeN n input with
        | Option.none => eerr (StreamErrors.ParseError.trivial o (pure Errors.ErrorItem.eof) ps) s
        | Option.some (ts, input') =>
            let len := stream.chunkLength ts
            if not (len == n)
            then eerr (StreamErrors.ParseError.trivial (o + len) (pure Errors.ErrorItem.eof) ps) (ParserState.State.mk input o pst de)
            else cok ts (ParserState.State.mk input' (o + len) pst de) []
  getParserState := Parsec.ParsecT.mk $ fun _ s _ _ eok _ => eok s s []
  updateParserState f := Parsec.ParsecT.mk $ fun _ s _ _ eok _ => eok Unit.unit (f s) []

instance (E S : Type) [m: Monad M] [a: Alternative M]
         [s : Stream.Stream S] [mₚ: @MonadParsec M E S m a s] :
         @MonadParsec (StateT σ M) E S (@msₜ M σ m) (@asₜ M σ m a) s where
  parseError A err := liftM (mₚ.parseError A err)
  label A f st := (mₚ.label E S (A × σ) f) ∘ st
  attempt A st := mₚ.attempt E S (A × σ) ∘ st
  lookAhead A state x := mₚ.lookAhead E S (A × σ) (state x)
  notFollowedBy A state x := Util.seqComp (mₚ.notFollowedBy E S A (Util.fst <$> state x)) (pure (Unit.unit , x))
  withRecovery A cont state x := mₚ.withRecovery (A × σ) (fun e => (cont e) x) (state x)
  observing A f x := Util.fixs x <$> (mₚ.observing (A × σ) (f x))
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S ms p)
  takeP A l n := liftM (mₚ.takeP E S l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

/-- MonadParsec instance for RWST -/

instance (E S W : Type) [m : Monoid W]
         [monad_inst : Monad M] [a : Alternative M] [s : Stream.Stream S]
         [mₚ : @MonadParsec M E S monad_inst a s]
         [MonadLiftT M (RWST.RWST R W S M)] : @MonadParsec (RWST.RWST R W S M) E S
         (@RWST.mrwsₜ M R W S m monad_inst) (@RWST.arwsₜ W M R S m monad_inst a) s where
  parseError A err := liftM (mₚ.parseError A err)
  label A n m := fun r s => mₚ.label E S (A × S × W) n (m r s)
  attempt A st := fun r s => mₚ.attempt E S (A × S × W) (st r s)
  lookAhead A st := fun r s => do
    let (x,_,_) <- mₚ.lookAhead E S (A × S × W) (st r s)
    pure (x,s,m.one)
  notFollowedBy A state := fun r s => do
    mₚ.notFollowedBy E S Unit (RWST.void (state r s))
    pure (Unit.unit, s, m.one)
  withRecovery A n m := fun r s => mₚ.withRecovery (A × S × W) (fun e => (n e) r s) (m r s)
  observing A m := fun r s => Util.fixs' s <$> mₚ.observing (A × S × W) (m r s)
  eof := liftM mₚ.eof
  token A test mt := liftM (mₚ.token E A test mt)
  tokens A e ts := liftM (mₚ.tokens E S e ts)
  takeWhileP A ms p := liftM (mₚ.takeWhileP E S ms p)
  takeWhile1P A ms p := liftM (mₚ.takeWhile1P E S ms p)
  takeP A l n := liftM (mₚ.takeP E S l n)
  getParserState := liftM mₚ.getParserState
  updateParserState f := liftM (mₚ.updateParserState f)

end MonadParsec
