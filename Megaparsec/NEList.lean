import Megaparsec.Util

/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains definitions for `NEList`, an inductive type meant to
represent non-empty lists.
-/

namespace NEList

inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

/-- Builds an `NEList α` from a term of `α` and a term of `List α` -/
def toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
def toList : NEList α → List α
  | .uno  a   => [a]
  | .cons a b => a :: toList b

def ord2beq_nel [Ord T] [BEq T] (x y : NEList T) : Bool :=
  match x, y with
  | .cons u x₁, .cons v y₁ => Util.ord2compare u v && ord2beq_nel x₁ y₁
  | .uno u, .uno v => Util.ord2compare u v
  | _, _ => false

def nonEmpty (l : List A) : Option (NEList A) :=
  match l with
  | [] => Option.none
  | (x :: xs) => NEList.cons x <$> nonEmpty xs

def nonEmptyString (s : String) : Option (NEList Char) :=
  match s with
    | { data := str } => nonEmpty str

end NEList