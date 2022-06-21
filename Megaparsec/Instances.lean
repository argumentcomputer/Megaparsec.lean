import Megaparsec.Megaparsec
import Megaparsec.Common

namespace Instances

def splitAtString (n : ℕ) (str : String) : String × String :=
  match List.splitAt n str.data with
    | (s₁,s₂) => (String.mk s₁, String.mk s₂)

instance str : Megaparsec.Stream String where
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
      | n => if String.isEmpty str then Option.none else splitAtString n str
  takeWhile p str :=
    match List.span p str.data with
      | (s₁,s₂) => (String.mk s₁, String.mk s₂)

end Instances