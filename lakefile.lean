import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "main"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "pull/98/head"

require Straume from git
  "https://github.com/lurk-lab/straume" @ "main"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
