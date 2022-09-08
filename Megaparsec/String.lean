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

variable (m : Type → Type v) (℘ E : Type) [MonadParsec m ℘ String E Char]

def swap (a : Char) (b : Char) (xs : String) : String :=
  xs.map (fun x => if x == a then b else x)

def unwords : List String → String :=
  String.intercalate " "

-- TODO: metaprogramming?!
structure StringSimple where
  parseError : ParseError Char E → m γ := MonadParsec.parseError ℘ String
  label : String → m γ → m γ := MonadParsec.label ℘ String E Char
  hidden : m γ → m γ := MonadParsec.hidden ℘ String E Char
  attempt : m γ → m γ := MonadParsec.attempt ℘ String E Char
  lookAhead : m γ → m γ := MonadParsec.lookAhead ℘ String E Char
  notFollowedBy : m γ → m PUnit := MonadParsec.notFollowedBy ℘ String E Char
  withRecovery : (ParseError Char E → m γ) → m γ → m γ := MonadParsec.withRecovery ℘ String
  observing : m γ → m (Either (ParseError Char E) γ) := MonadParsec.observing ℘ String
  eof : m PUnit := MonadParsec.eof ℘ String E Char
  token : (Char → Option γ) → List (ErrorItem Char) → m γ := MonadParsec.token ℘ String E
  tokens : (String → String → Bool) → String → m String := MonadParsec.tokens ℘ E Char
  takeWhileP : Option String → (Char → Bool) → m String := MonadParsec.takeWhileP ℘ E
  takeWhile1P : Option String → (Char → Bool) → m String := MonadParsec.takeWhile1P ℘ E
  takeP : Option String → Nat → m String := MonadParsec.takeP ℘ E Char
  getParserState : m (State Char ℘ E) := MonadParsec.getParserState String
  updateParserState : (State Char ℘ E → State Char ℘ E) → m PUnit := MonadParsec.updateParserState String
  stringP (x : String) : m String := MonadParsec.tokens ℘ E Char (BEq.beq) x

def string_simple (℘x : Type) [MonadParsec (Parsec Char ℘x Unit) ℘x String Unit Char] : StringSimple (Parsec Char ℘x Unit) ℘x Unit := {}
def string_simple_pure : StringSimple (Parsec Char String Unit) String Unit := {}

def string_parsecT (mx : Type → Type v) (℘x : Type)
                   [MonadParsec (ParsecT mx Char ℘x Unit) ℘x String Unit Char]
                   : StringSimple (ParsecT mx Char ℘x Unit) ℘x Unit := {}
