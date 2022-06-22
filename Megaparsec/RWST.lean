import Mathlib.Algebra.Group.Defs

namespace RWST

/-- RWS monad and its transformer and required utilities -/

def void [Monad M] (ma : M A) : M Unit :=
  (fun _ => Unit.unit) <$> ma

def RWST (R W S : Type u) (M : Type u → Type v) (A : Type u) : Type (max u v) :=
  R → S → M (A × S × W)

instance mrwsₜ (R W S : Type) [m : Monoid W] [Monad M] : Monad (RWST R W S M) where
  map f x := fun r s => do {
    let (a, s, w) <- x r s
    pure (f a, s, w)
  }
  pure x := fun _ s => pure (x,s,m.one)
  bind m k := fun r s => do {
    let (a, s', w) <- m r s
    let (b, s'', w') <- (k a) r s
    pure (b, s'', w * w') }

instance arwsₜ [Monoid W] [Monad M] [mₐ : Alternative M] : Alternative (RWST R W S M) where
  failure := fun _ _ => mₐ.failure
  orElse a b := fun r s => mₐ.orElse (a r s) (fun _ => b Unit.unit r s)

instance [Monad M] [m : Monoid W] : MonadLiftT M (RWST R W S M) where
  monadLift ma := fun _ s => do
    let a <- ma
    pure (a, s, m.one)

end RWST