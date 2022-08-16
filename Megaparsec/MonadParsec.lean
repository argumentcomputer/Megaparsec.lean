import Megaparsec.Errors
import Megaparsec.Errors.ParseError
import Megaparsec.ParserState

import YatimaStdLib

open Megaparsec.Errors
open Megaparsec.Errors.ParseError
open Megaparsec.ParserState

namespace MonadParsec

/-- MonadParsec class and their instances -/

/- Monads m that implement primitive parsers.
Thus, you see `m γ`, read it "parser m-gamma".  -/
class MonadParsec (m : Type u → Type v) (α β ℘ E : outParam (Type u)) where
  /- Stop parsing wherever we are, and report ParseError. -/
  parseError : ParseError β E → m γ
  /- If `m γ` consumed no input, replace the names of expected tokens with `nameOverride`. -/
  label (nameOverride : String) : m γ → m γ
  /- Hides expected token error messages when `m γ` fails. -/
  hidden : m γ → m γ
  /- Attempts to parse with `m γ` and backtrack on failure.
  Used for arbitrary look-ahead.
  Consult megaparsec docs for pitfalls:
  https://hackage.haskell.org/package/megaparsec-9.2.1/docs/src/Text.Megaparsec.Class.html#try -/
  attempt : m γ → m γ
  /- Parse with `m γ` without consuming.
  Fail on fail.
  Combine with `attempt` if you need to recover.
  -/
  lookAhead : m γ → m γ
  /- Succeeds if `m γ` fails. Doesn't consume, nor modify state.
  Useful for "longest match" rule implementation. -/
  notFollowedBy : m γ → m PUnit
  /- Use recovery function `φ` to recover from failure in `m γ`. -/
  withRecovery : (φ : ParseError β E → m γ) → m γ → m γ
  /- Observes errors as they happen, without backtracking. -/
  observing : m γ → m (Either (ParseError β E) γ)
  /- The parser at the end of the stream. -/
  eof : m PUnit
  /- If `φ` is `.some`, parse the token.
  Otherwise, accumulate `.none`s into `acc` for error reporting. -/
  token : (φ : β → Option γ) → (acc : List (ErrorItem β)) → m γ
  /- Parse `y` tokens from the beginning of the stream, such that y = |x| > 0, if `φ x y`.
  Succed if |x| = 0.
  Backtrack on fail.
  -/
  tokens : (φ : α → α → Bool) → (x : α) → m γ
  /- Never fail to parse zero or more tokens with `φ`.

  Optional `String` is a way to name the expected token.
  For example:

  `takeWhileP (.just "symbol of Korean alphabet") f` = `many (satisfy f <?> "symbol of Korean alphabet")`

  `takeWhileP .none` f = `many (satisfy f)`.
  -/
  takeWhileP : Option String → (β → Bool) → m α
  /- Like `takeWhileP`, but fail if there are zero matches.

  Optional `String` is a way to name the expected token.

  For example:

  `takeWhile1P (.just "symbol of Korean alphabet")` f = `many (satisfy f <?> "symbol of Korean alphabet")`

  `takeWhile1P .none` f = `many (satisfy f)`.
  -/
  takeWhile1P : Option String → (β → Bool) → m α
  /- Parses `n` tokens at the beginning of the stream.
  Backtracks if there are not enough tokens.

  NB! This is not a best-effort take, like we have it in Straume!
  It has to guarantee that if it succeds, the requested amount of tokens is returned!

  Optional `String` is a way to name the expected group of tokens.

  For example:

  `takeP (.some "protobuf message") n` = `count n (anySingle <?> "protobuf message")`

  `takeP .none n` = `count n anySingle`.
  -/
  takeP : Option String → n → m α
  /- Ditto. -/
  getParserState : m (State β ℘ E)
  /- Ditto. -/
  updateParserState : (State β ℘ E → State β ℘ E) → m PUnit
