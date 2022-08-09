import LSpec
open LSpec

-- import Megaparsec.Parsec
-- import Megaparsec.Common
-- import Megaparsec.Errors
-- import Megaparsec.Stream

-- def unimpl : LSpec :=
--   it "is unimplemented" true $ shouldBe false

-- instance s2s : ToString String where
--   toString := id

-- def main :=
--   lspec "todo: inspect the state" unimpl

-- def main : IO Unit := do
--   -- Prove that we can at least parse something.
--   let specM := lspec "todo: inspect the state" unimpl
--   pure ()

-- def main : IO Unit := do
--   -- Prove that we can at least parse something.
--   let _x <- lspec "todo: inspect the state" unimpl
--     -- it "prints something" (IO Unit) (shouldBe $ Parsec.parseTest (Common.string "yatima") "yatimaa~")
--   -- TODO: Make an abbreviated String version for parseTest lol
--   -- @Parsec.parseTest String (Stream.str) (Errors.ErrorFancy String) String s2s (Common.string "yatima") "yatimaa~"
--   -- Parsec.parseTest (Common.string "yatima") "yatimaa~"
--   @Parsec.parseTest String Stream.str String String s2s (@Common.string Option String String Option.instMona "yatima")

def failMe : TestSeq :=
  test "Tests can't fail" false

def main := lspecIO $
  failMe
