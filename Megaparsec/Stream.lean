import Megaparsec.Errors
import Megaparsec.Util

namespace Stream

/-- Stream type class, related definitions, and Stream instances -/

class Stream (S : Type) where
  Token : Type
  ordToken : Ord Token
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

inductive ParseError (E: Type) [stream: Stream S] where
| trivial (offset: Nat)
          (unexpected: Option (Errors.ErrorItem (stream.Token)))
          (expected: List (Errors.ErrorItem (stream.Token)))
| fancy (offset: Nat) (expected: List (Errors.ErrorFancy E))

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
               | (Option.some x, Option.some y) => ParseError.trivial s₁ (Option.some (Errors.errorItemMax x y)) (p₁ ++ p₂)
               | (Option.none, Option.some x) => ParseError.trivial s₁ (Option.some x) (p₁ ++ p₂)
               | (Option.some x, Option.none)=> ParseError.trivial s₁ (Option.some x) (p₁ ++ p₂)
          | (ParseError.fancy _ _, ParseError.trivial _ _ _) => e₁
          | (ParseError.trivial _ _ _, ParseError.fancy _ _) => e₂
          | (ParseError.fancy s₁ x₁, ParseError.fancy _ x₂) => ParseError.fancy s₁ (x₁ ++ x₂)
    | Ordering.gt => e₁

def toHints [s : Stream S] (streamPos : ℕ) (e : @ParseError S E s) : Errors.Hints s.Token :=
  match e with
    | ParseError.fancy _ _ => []
    | ParseError.trivial errOffset _ ps =>
        if streamPos == errOffset
           then (if List.isEmpty ps then [] else [ps])
           else []

def refreshLastHint (h : Errors.Hints T) (m : Option (Errors.ErrorItem T)) : Errors.Hints T :=
  match (h,m) with
    | ([], _h) => []
    | (_ :: xs, Option.none) => xs
    | (_ :: xs, Option.some y) => [y] :: xs


instance str : Stream String where
  Token := Char
  ordToken := instOrdChar
  Tokens := String
  ordTokens := instOrdString
  tokenToChunk ch := String.mk [ch]
  tokensToChunk := String.mk
  chunkToTokens := String.data
  chunkLength := String.length
  take1 str :=
    match str.data with
      | [] => Option.none
      | (x::xs) => Option.some (x, String.mk xs)
  takeN n str :=
    match n with
      | Nat.zero => Option.some (String.mk [], str)
      | n => if String.isEmpty str then Option.none else Util.splitAtString n str
  takeWhile p str :=
    match List.span p str.data with
      | (s₁,s₂) => (String.mk s₁, String.mk s₂)

end Stream