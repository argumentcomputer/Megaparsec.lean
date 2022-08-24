import Lake
open Lake DSL

package Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "77fc51697abeff937ffd20d2050723dc0fa1c8c0"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "a2bbc9a48db7efd5d761a5b27f2cc6c1863b9622"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "1f007dd57e8e0da6fe966f052be1f3724bd1281a"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
