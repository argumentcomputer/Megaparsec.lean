import Lake
open Lake DSL

package Megaparsec

@[default_target]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "2b914196a8c67838e63c1c1e44eaf339b8a50eb7"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "2c8c0ecb0afa5bb5e9dbd039fe48064f40edd6aa"

@[default_target]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
