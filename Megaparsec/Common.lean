import Megaparsec.MonadParsec
import Straume.Iterator
import Straume.Coco
import Straume

import YatimaStdLib

open MonadParsec
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection
open Straume.Coco
open Straume

/-!
# Common token combinators

Simple combinators that are agnostic to the stream they're applied to.
-/

namespace Megaparsec.Common

-- TODO: case-insensitive version
def string (m : Type u → Type v) (℘ : Type u) {E : Type u} {α β : Type u} (x : α) [MonadParsec m ℘ α β E] [BEq α] : m α :=
  MonadParsec.tokens ℘ (BEq.beq) x

-- TODO: Move to YatimaStdLib
def between [SeqLeft φ] [SeqRight φ] (f h g : φ α) : φ α := f *> h <* g

end Common
