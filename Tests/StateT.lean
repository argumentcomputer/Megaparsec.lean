import LSpec

import Megaparsec
import Megaparsec.Common
import Megaparsec.Parsec

open LSpec

open MonadParsec
open Megaparsec.Common
open Megaparsec.Parsec


abbrev SP := StateT Nat (Parsec Char String Unit)

def stateTest : TestSeq :=
  let sample := "“'if at first you don't succeed, try, try, try again!' -- William E. Hickson” -- Day[9]"

  let ptSO : StateT Nat (Parsec Char String Unit) String := do
    let x0 ← MonadStateOf.get
    let fail ← string (i := statetInstance) "fail me"
    MonadStateOf.set $ x0 + 41
    pure fail

  let ptST : StateT Nat (Parsec Char String Unit) String := do
    MonadStateOf.set $ 1
    let x0 ← StateT.get
    let parsed ← string (i := statetInstance) "fail me" <|> pure ""
    MonadStateOf.set $ x0 + 41
    pure parsed

  withExceptError "StateT with failing parser: fails"
    (parse (StateT.run ptSO 1) sample)
    (fun _ => .done) ++

  withExceptOk "StateT parsing successful"
    (parse (StateT.run ptST 1) sample)
    (fun (s, x) =>
      test "state is 42" (x = 42) $
      test "empty string parsed out" (s = "")
    )

def main := lspecIO $
  stateTest
