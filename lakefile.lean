import Lake
open Lake DSL

package Megaparsec

@[defaultTarget]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "c63610bb23451c7aa2faae17c71e8d162c6c616e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "54177756e0f3488979b05153872d1832bc5ba625"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "c1d72a24ae3a8a8e0bd7928001b55958e4b9113c"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
