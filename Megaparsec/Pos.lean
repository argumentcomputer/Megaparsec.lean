namespace Megaparsec.Pos

structure Pos where
  pos : Nat
  deriving Repr, DecidableEq, Ord

instance : ToString Pos where
  toString x := s!"{x.pos}"

export Pos (pos)

instance : Add Pos where
  add | ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

def pos1 : Pos := Pos.mk 1

partial def expandTab (tw : Nat) (str : String) : String :=
  let strl := str.data
  let rec go : Nat → List Char → List Char
    | 0, [] => []
    | 0, ('\t' :: xs) => go tw xs
    | 0, (x :: xs) => x :: go 0 xs
    | n, xs => ' ' :: go (n - 1) xs
  String.mk $ go 0 strl
