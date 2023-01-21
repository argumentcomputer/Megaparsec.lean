import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "0b0e2b07e2f8eabcf392140bfc289080e03aa9b5"

require Straume from git
  "https://github.com/yatima-inc/straume" @ "9597873f0b18a9e97b7315fb84968c55d09a6112"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
