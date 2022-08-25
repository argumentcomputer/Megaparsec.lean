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

variable (℘T : Type) [MonadParsec (ParsecT m Char ℘ E) ℘ String E Char]
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
def parseError : ParseError Char Unit → Parsec Char ℘ Unit γ := MonadParsec.parseError ℘ String
def label : String → Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.label ℘ String Unit Char
def hidden : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.hidden ℘ String Unit Char
def attempt : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.attempt ℘ String Unit Char
def lookAhead : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.lookAhead ℘ String Unit Char
def notFollowedBy : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit PUnit := MonadParsec.notFollowedBy ℘ String Unit Char
def withRecovery : (ParseError Char Unit → Parsec Char ℘ Unit γ) → Parsec Char ℘ Unit γ → Parsec Char ℘ Unit γ := MonadParsec.withRecovery ℘ String
def observing : Parsec Char ℘ Unit γ → Parsec Char ℘ Unit (Either (ParseError Char Unit) γ) := MonadParsec.observing ℘ String
def eof : Parsec Char ℘ Unit PUnit := MonadParsec.eof ℘ String Unit Char
def token : (Char → Option γ) → List (ErrorItem Char) → Parsec Char ℘ Unit γ := MonadParsec.token ℘ String Unit
def tokens : (String → String → Bool) → String → Parsec Char ℘ Unit String := MonadParsec.tokens ℘ Unit Char
def takeWhileP : Option String → (Char → Bool) → Parsec Char ℘ Unit String := MonadParsec.takeWhileP ℘ Unit
def takeWhile1P : Option String → (Char → Bool) → Parsec Char ℘ Unit String := MonadParsec.takeWhile1P ℘ Unit
def takeP : Option String → Nat → Parsec Char ℘ Unit String := MonadParsec.takeP ℘ Unit Char
def getParserState : Parsec Char ℘ Unit (State Char ℘ Unit) := MonadParsec.getParserState String
def updateParserState : (State Char ℘ Unit → State Char ℘ Unit) → Parsec Char ℘ Unit PUnit := MonadParsec.updateParserState String
def stringP (x : String) : Parsec Char ℘ Unit String := tokens ℘ (BEq.beq) x

end Megaparsec.String.Simple
