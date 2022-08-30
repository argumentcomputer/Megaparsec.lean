import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Errors.ParseError
import Megaparsec.Errors
import Megaparsec.ParserState
import Megaparsec.Common

open Megaparsec.Parsec
open MonadParsec
open Megaparsec.Errors.ParseError
open Megaparsec.Errors
open Megaparsec.ParserState
open Megaparsec.Common

namespace Megaparsec.String

variable (℘ : Type) [MonadParsec (Parsec Char ℘ Unit) ℘ String Unit Char]

-- def StrFancyT m E  := ParsecT m Char ℘T E
-- def StrT m := ParsecT m Char ℘T Unit

-- def StrFancy E := Parsec Char ℘ E
-- def Str := Parsec Char ℘ Unit

def swap (a : Char) (b : Char) (xs : String) : String :=
  xs.map (fun x => if x == a then b else x)

def unwords : List String → String :=
  String.intercalate " "

namespace Megaparsec.String.Simple

-- TODO: metaprogramming?!
structure StringSimple where
  parseError : ParseError Char Unit → Parsec Char ℘ Unit γ := MonadParsec.parseError ℘ String
  label : String → Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.label ℘ String Unit Char
  hidden : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.hidden ℘ String Unit Char
  attempt : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.attempt ℘ String Unit Char
  lookAhead : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.lookAhead ℘ String Unit Char
  notFollowedBy : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit PUnit := MonadParsec.notFollowedBy ℘ String Unit Char
  withRecovery : (ParseError Char Unit → Parsec Char ℘ Unit γ) → Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.withRecovery ℘ String
  observing : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit (Either (ParseError Char Unit) γ) := MonadParsec.observing ℘ String
  eof : Parsec Char ℘ Unit PUnit := MonadParsec.eof ℘ String Unit Char
  token : (Char → Option γ) → List (ErrorItem Char) → Parsec Char ℘ Unit γ := MonadParsec.token ℘ String Unit
  tokens : (String → String → Bool) → String → Parsec Char ℘ Unit String := MonadParsec.tokens ℘ Unit Char
  takeWhileP : Option String → (Char → Bool) → Parsec Char ℘ Unit String := MonadParsec.takeWhileP ℘ Unit
  takeWhile1P : Option String → (Char → Bool) → Parsec Char ℘ Unit String := MonadParsec.takeWhile1P ℘ Unit
  takeP : Option String → Nat → Parsec Char ℘ Unit String := MonadParsec.takeP ℘ Unit Char
  getParserState : Parsec Char ℘ Unit (State Char ℘ Unit) := MonadParsec.getParserState String
  updateParserState : (State Char ℘ Unit → State Char ℘ Unit) → Parsec Char ℘ Unit PUnit := MonadParsec.updateParserState String
  stringP (x : String) : Parsec Char ℘ Unit String := MonadParsec.tokens ℘ Unit Char (BEq.beq) x

end Megaparsec.String.Simple
