import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "818538aced05fe563ef95bb3dcdf5ed755896139"

require Straume from git
  "https://github.com/yatima-inc/straume" @ "df81444aa996010835a6a5f63ea651b02ec035e8"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
