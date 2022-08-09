import Lake
open Lake DSL

package Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "77fc51697abeff937ffd20d2050723dc0fa1c8c0"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}