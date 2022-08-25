namespace Megaparsec.Pos

structure Pos where
  pos : Nat

instance : ToString Pos where
  toString x := s!"{x.pos}"

export Pos (pos)
