import Lake
open Lake DSL

package Megaparsec

@[defaultTarget]
lean_lib Megaparsec

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "9c9f3cc9f3148c1b2d6071a35e54e4c5392373b7"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "876d29cb6f8011119a74712de7cb86280e408e3b"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "fa32bbbc9942c2339e5d363ef5af1e5af081470b"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
