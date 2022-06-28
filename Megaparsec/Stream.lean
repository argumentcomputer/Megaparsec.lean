import Megaparsec.Errors
import YatimaStdLib

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
      | n => if String.isEmpty str 
             then Option.none 
             else Option.some $ String.splitAtString n str
  takeWhile p str :=
    match List.span p str.data with
      | (s₁,s₂) => (String.mk s₁, String.mk s₂)

end Stream
