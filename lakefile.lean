import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "7af015ddd688052cd14f7dedea6856b943ed25ed"

require Straume from git
  "https://github.com/lurk-lab/straume" @ "568d412316c412433029046f899033d5839f7304"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
