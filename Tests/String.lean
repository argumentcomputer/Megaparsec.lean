import LSpec
import Megaparsec.Common

open LSpec

import Megaparsec.Parsec

open Megaparsec.Common in
def testString x y := Parsec.parseTest (string x) y

def stringUX : TestSeq :=
  test "string has good invocation UX" $
    testString "yatima" "yatimaa~"

def main := lspecIO $
  stringUX
