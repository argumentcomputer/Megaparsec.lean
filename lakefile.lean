import Lake
open Lake DSL

package Megaparsec

@[defaultTarget]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "7e2d41644519e8c437fbe7461544eaa855738f73"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "9c362443e0d89eb96683b52a1caaf762049697c4"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "c1d72a24ae3a8a8e0bd7928001b55958e4b9113c"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
