import LSpec
import Megaparsec.Common
import Megaparsec.Parsec
import YatimaStdLib

open LSpec
open Megaparsec.Parsec


open Megaparsec.Common in
def testString (x : String) (y : String) : IO (Either Unit String) := parseTest (string x) y

def stringUX : TestSeq :=
  test "string has good invocation UX" $
    testString "yatima" "yatimaa~"

def main := lspecIO $
  stringUX
