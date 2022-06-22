import LSpec

def twoTests : LSpec :=
  it "knows equality" 42 (shouldBe 42) $
  it "knows lists" [42].length (shouldBe 1)

def main :=
  lspec "some description" twoTests
