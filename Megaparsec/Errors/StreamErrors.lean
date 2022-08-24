import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import YatimaStdLib
import Straume.Iterator
import Megaparsec.Ok
import Megaparsec.Err

open Straume.Iterator (Iterable)
open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.Ok
open Megaparsec.Err

namespace Megaparsec.Errors.StreamErrors

universe u

def errorOffset (e: ParseError β E) : Nat :=
  match e with
    | ParseError.trivial n _ _ => n
    | ParseError.fancy n _     => n

/- Merge errors produced by alternative parsers.
Strategy:

1. If the errors have the same offset, keep fancy.
2. If both are fancy, merge the collections of ErrorFancy in each.
3. If both are trivial carrying some information, pick one based on the optional eiMax funciton.
   The first one is picked by default.
2. Otherwise, discard the error with the lowest offset.
   It doesn't matter, because the alternative choice of parsers is eager.


The error with the state with the longest match is topped with the messages from the "shortest" state.
The error with the "shortest" state is discarded. -/
def mergeErrors (e₁: ParseError β E)
                (e₂: ParseError β E)
                (eiMax : ErrorItem β → ErrorItem β → ErrorItem β := fun x _ => x) : ParseError β E :=
  match (compare (errorOffset e₁) (errorOffset e₂)) with
    | Ordering.lt => e₂
    | Ordering.eq =>
        match (e₁, e₂) with
          | (ParseError.trivial s₁ u₁ p₁, .trivial _ u₂ p₂) =>
             match (u₁, u₂) with
               | (.none, .none) => .trivial s₁ .none (p₁ ++ p₂)
               | (.some x, .some y) => .trivial s₁ (.some (eiMax x y)) (p₁ ++ p₂)
               | (.none, .some x) => .trivial s₁ (.some x) (p₁ ++ p₂)
               | (.some x, .none)=> .trivial s₁ (.some x) (p₁ ++ p₂)
          | (.fancy _ _, .trivial _ _ _) => e₁
          | (.trivial _ _ _, .fancy _ _) => e₂
          | (.fancy s₁ x₁, .fancy _ x₂) => .fancy s₁ (x₁ ++ x₂)
    | Ordering.gt => e₁

def toHints (streamPos : Nat) (e : ParseError α E) : Hints α :=
  match e with
    | ParseError.fancy _ _ => []
    | ParseError.trivial errOffset _ ps =>
        if streamPos == errOffset
           then (if List.isEmpty ps then [] else [ps])
           else []

def refreshLastHint (h : Hints β) (m : Option (ErrorItem β)) : Hints β :=
  match (h, m) with
    | ([], _h) => []
    | (_ :: xs, .none) => xs
    | (_ :: xs, .some y) => [y] :: xs
