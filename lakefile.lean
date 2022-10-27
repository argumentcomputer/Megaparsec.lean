import Lake
open Lake DSL

package Megaparsec

@[defaultTarget]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "9270cda461d9b76a5ae5004ccb4f02428622d390"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "9429ac391b9ef4fb8df648d8873439bc7e30c3a0"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
