import Megaparsec.Errors
import YatimaStdLib
import Straume.Iterator

open Straume.Iterator (Iterable)
open Megaparsec.Errors

namespace Megaparsec.Errors.StreamErrors

universe u

inductive ParseError (β E : Type u) where
| trivial (offset: Nat)
          (unexpected: Option (ErrorItem β))
          (expected: List (ErrorItem β))
| fancy (offset: Nat) (expected: List (ErrorFancy E))

def errorOffset (e: ParseError β E) : Nat :=
  match e with
    | ParseError.trivial n _ _ => n
    | ParseError.fancy n _     => n

def mergeError (e₁: ParseError β E)
               (e₂: ParseError β E) [Ord β] : ParseError β E :=
  match (compare (errorOffset e₁) (errorOffset e₂)) with
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

def toHints (streamPos : Nat) (e : ParseError α E) : Hints α :=
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

end StreamErrors
