import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Straume.Iterator
import Straume.Coco
import Straume
import Megaparsec.Errors

import YatimaStdLib

open MonadParsec
open Megaparsec.Parsec
open Straume.Iterator (Iterable)
open Straume.Iterator renaming Bijection → Iterable.Bijection
open Straume.Coco
open Straume
open Megaparsec.Errors

/-!
# Common token combinators

Simple combinators that are agnostic to the stream they're applied to.
-/

namespace Megaparsec.Common

universe u

def single (m : Type u → Type v) (℘ E α : Type u) (x : β) [MonadParsec m ℘ α E β] [BEq β] : m β :=
  MonadParsec.token ℘ α E (fun y => if x == y then .some x else .none) [ErrorItem.tokens $ NEList.uno x]

-- TODO: case-insensitive version
def string (m : Type u → Type v) (℘ E β : Type u) {α : Type u} (x : α) [MonadParsec m ℘ α E β] [BEq α] : m α :=
  MonadParsec.tokens ℘ E β (BEq.beq) x

-- TODO: Move to YatimaStdLib or even to Lean 4
def between [SeqLeft φ] [SeqRight φ] (f : φ α) (h : φ β) (g : φ γ) : φ β :=
  f *> h <* g

def liftSeq2 [Seq φ] [Functor φ] (f2 : α → β → γ) (x : φ α) : (Unit → φ β) → φ γ :=
  Seq.seq (Functor.map f2 x)

def void [Functor φ] (fx : φ a) : φ Unit :=
  (fun _ => ()) <$> fx


-- TODO: A lot of thunks here. Support monadic versions of these combinators.
mutual
  partial def some [Alternative φ] [Inhabited (φ (List α))] (p : φ α) : φ (List α) :=
    liftSeq2 List.cons p $ fun () => many p
  partial def many [Alternative φ] [Inhabited (φ (List α))] (p : φ α) : φ (List α) :=
    some p <|> pure []
end
partial def many1 [Alternative φ] [Inhabited (φ (List α))] : φ α → φ (List α) := some

partial def sepBy1 [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
  liftSeq2 List.cons p fun () => (many $ sep *> p)
partial def sepBy [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
  sepBy1 p sep <|> pure []

mutual
  partial def sepEndBy1 [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
    liftSeq2 List.cons p fun () => (sep *> sepEndBy p sep)
  partial def sepEndBy [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
    sepEndBy1 p sep <|> pure []
end

-- -- TODO: Our foldable is not foldable: https://zulip.yatima.io/#narrow/stream/24-yatima-tools/topic/.5BYatimaStdLib.2Elean.5D.20chat/near/19242
-- def asum {f : Type u → Type v} {t : Type v → Type v} [Foldable t] [Alternative f] (fas : t (f α)) : f α :=
--   Foldable.foldr (fun a b => a <|> b) Alternative.failure fas

def choice {m : Type → Type v} {β σ E γ : Type} (ps : List (ParsecT m β σ E γ)) : ParsecT m β σ E γ :=
  List.foldr (fun a b => a <|> b) Alternative.failure ps

/- m-polymorphic choice -/
def choiceP {m : Type → Type v} (σ α E β : Type) {γ : Type} (ps : List (m γ)) [MonadParsec m σ α E β] [Alternative m] : m γ :=
  List.foldr (fun a b => a <|> b) Alternative.failure ps
