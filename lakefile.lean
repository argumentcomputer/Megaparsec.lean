import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "3388be5a1d1390594a74ec469fd54a5d84ff6114"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "3037f0c14128751b95510c2723f067ec7a494f08"

require Straume from git
  "https://github.com/lurk-lab/straume" @ "ad2aa666b7e4148df450ecf74aedb477f1535534"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
