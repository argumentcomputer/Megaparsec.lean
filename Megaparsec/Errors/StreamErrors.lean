import Megaparsec.Errors
import Megaparsec.Stream

import YatimaStdLib

namespace StreamErrors

inductive ParseError (E: Type) [stream: Stream.Stream S] where
| trivial (offset: Nat)
          (unexpected: Option (Errors.ErrorItem (stream.Token)))
          (expected: List (Errors.ErrorItem (stream.Token)))
| fancy (offset: Nat) (expected: List (Errors.ErrorFancy E))

def errorOffset [s: Stream.Stream S] (e: @ParseError S E s) : ℕ :=
  match e with
    | ParseError.trivial n _ _ => n
    | ParseError.fancy n _     => n

def mergeError [s: Stream.Stream S]
               [Ord (Stream.Stream.Token S)]
               [BEq (Stream.Stream.Token S)]
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

def toHints [s : Stream.Stream S] (streamPos : ℕ) (e : @ParseError S E s) : Errors.Hints s.Token :=
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

end StreamErrors
