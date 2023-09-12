import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "3b6023654b917c8641ec5e626724a43380cff8f0"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "5b64c5150e371fb280728cbb5b7c225b9c96b348"

require Straume from git
  "https://github.com/lurk-lab/straume" @ "053d9feccbface9a0b2c1a72447914376aac74ea"

@[default_target]
lean_exe megaparsec {
  root := "Main"
}

lean_exe Tests.Parsec
lean_exe Tests.IO
lean_exe Tests.StateT
lean_exe Tests.Lisp
