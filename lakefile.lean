import Lake

open Lake DSL

package Megaparsec {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "6895646674b04c0d7bcd085b4da3f7bb354ceaa9"
  }, {
    name := "LSpec",
    src := Source.git "https://github.com/yatima-inc/LSpec.git" "f71c4dd98c5735599664100acfaaa5f6238d13a3"
  }],
  defaultFacet := PackageFacet.oleans -- no executable is generated
}
