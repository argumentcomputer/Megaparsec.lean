import Lake

open Lake DSL

package Megaparsec {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "6895646674b04c0d7bcd085b4da3f7bb354ceaa9"
  }],
  defaultFacet := PackageFacet.oleans -- no executable is generated
}
