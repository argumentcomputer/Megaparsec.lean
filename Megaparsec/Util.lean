import Mathlib.Algebra.Group.Defs

namespace Util

def option (b : B) (f : A → B) (oa : Option A) : B :=
  match oa with
    | Option.none => b
    | Option.some x => f x

inductive Either (L: Type u) (R: Type v) where
| left (l : L)
| right (r : R)

def fixs {A B C : Type} (c : C) : Either A (B × C) → (Either A B) × C
  | .left a => ⟨ .left a, c ⟩
  | .right ⟨ a, b ⟩ => ⟨ .right a, c ⟩

def fixs' {A B C W : Type} [m : Monoid W] (c : C) : Either A (B × C × W) → (Either A B) × C × W
  | .left a => ⟨ .left a, c, m.one ⟩
  | .right ⟨ a, b, w ⟩ => ⟨ .right a, c, w ⟩

def updatePair {A B C : Type} (c : C) : A × B → A × C
  | ⟨ a, _ ⟩ => ⟨ a, c ⟩

def fst {A B : Type} : A × B → A
  | ⟨ a, _⟩ => a

def seqComp {M : Type u → Type v} [Monad M] (ma : M A) (mb : M B) :=
  ma >>= fun _ => mb

instance ord2beq [Ord T] : BEq T where
  -- beq x y := compare x y == Ordering.eq
  beq x := BEq.beq Ordering.eq ∘ compare x

def ord2compare [Ord T] (x y : T) : Bool :=
  compare x y == Ordering.eq

def splitAtString (n : ℕ) (str : String) : String × String :=
  match List.splitAt n str.data with
    | (s₁,s₂) => (String.mk s₁, String.mk s₂)
end Util
