import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "515b7eff7765dcf55ce275ac41fa13a30a59f1d0"

require Straume from git
  "https://github.com/yatima-inc/straume" @ "10fffb9ddcb015b7d1251e2495e20cdbaebc79b1"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
