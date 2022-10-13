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

def single {m : Type u → Type v} {℘ α E β: Type u} [MonadParsec m ℘ α E β] [BEq β] (x : β): m β :=
  MonadParsec.token ℘ α E (fun y => if x == y then .some x else .none) [ErrorItem.tokens $ NEList.uno x]

-- TODO: case-insensitive version
def string {m : Type u → Type v} {℘ α E β: Type u} [MonadParsec m ℘ α E β] [BEq α] (x : α): m α :=
  MonadParsec.tokens ℘ E β (BEq.beq) x

mutual
  partial def some' {℘ β x: Type u} (p : Parsec β ℘ PUnit x) : Parsec β ℘ PUnit (List x) := do
    let y ← p
    let ys ← many' p
    pure $ List.cons y ys
  partial def many' {℘ β x: Type u} (p : Parsec β ℘ PUnit x) : Parsec β ℘ PUnit (List x) := do
    some' p <|> pure []
end
partial def many1' {℘ β x : Type u} (p : Parsec β ℘ PUnit x) : Parsec β ℘ PUnit (List x) := some' p

mutual
  partial def some {m : Type u → Type v} {σ α β E : Type u} {γ : Type u}
                   [pi: MonadParsec m σ α E β] [mi: Monad m] [ai: Alternative m]
                   (p : m γ)
                   : m (List γ) := do
    let y ← p
    let ys ← @many m σ α β E γ pi mi ai p
    pure $ List.cons y ys
  partial def many {m : Type u → Type v} {σ α β E : Type u} {γ : Type u}
                   [pi: MonadParsec m σ α E β] [mi: Monad m] [ai: Alternative m]
                   (p : m γ)
                   : m (List γ) :=
    @some m σ α β E γ pi mi ai p <|> pure []
end

partial def many1 {m : Type u → Type v} {σ α β E : Type u} {γ : Type u}
                  [pi: MonadParsec m σ α E β] [mi: Monad m] [ai: Alternative m]
                  (p : m γ)
                  : m (List γ) :=
    @some m σ α β E γ pi mi ai p

-- mutual
--   partial def sepEndBy1 [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
--     Seq.liftSeq2 List.cons p fun () => ((sep *> sepEndBy p sep) <|> pure [])
--   partial def sepEndBy [Alternative φ] [Inhabited (φ (List α))] (p : φ α) (sep : φ β) : φ (List α) :=
--     sepEndBy1 p sep <|> pure []
-- end

mutual
  partial def sepEndBy {m : Type u → Type v} {σ α β E : Type u} {γ : Type u}
                       [pi: MonadParsec m σ α E β] [mi: Monad m] [ai: Alternative m]
                       (p : m γ) (sep : m γ)
                       : m (List γ) :=
    @sepEndBy1 m σ α β E γ pi mi ai p sep <|> pure []

  partial def sepEndBy1 {m : Type u → Type v} {σ α β E : Type u} {γ : Type u}
                       [pi: MonadParsec m σ α E β] [mi: Monad m] [ai: Alternative m]
                       (p : m γ) (sep : m γ)
                       : m (List γ) := do
    let y ← p
    let ys ← ((sep *> @sepEndBy m σ α β E γ pi mi ai p sep) <|> pure [])
    pure $ List.cons y ys
end

mutual
  partial def sepEndBy' {℘ β x: Type u} (p : Parsec β ℘ PUnit x) (sep : Parsec β ℘ PUnit s) : Parsec β ℘ PUnit (List x) :=
    sepEndBy1' p sep <|> pure []

  partial def sepEndBy1' {℘ β x : Type u} (p : Parsec β ℘ PUnit x) (sep : Parsec β ℘ PUnit s) : Parsec β ℘ PUnit (List x) := do
    let y ← p
    let ys ← ((sep *> sepEndBy' p sep) <|> pure [])
    pure $ List.cons y ys
end

-- -- TODO: Our foldable is not foldable: https://zulip.yatima.io/#narrow/stream/24-yatima-tools/topic/.5BYatimaStdLib.2Elean.5D.20chat/near/19242
-- def asum {f : Type u → Type v} {t : Type v → Type v} [Foldable t] [Alternative f] (fas : t (f α)) : f α :=
--   Foldable.foldr (fun a b => a <|> b) Alternative.failure fas

-- TODO: Can we resort to finite Foldables and use Iterable in the combinators where we would otherwise use Foldable?
-- That would be way better than Lists.

-- TODO: I absolutely hate the fact that we're not properly universe-polymorphic. I think it's a ripple effect of buggy Foldable.
-- And the fact that we're not doing universe-lifting for primitive types.

def choice' {m : Type → Type v} {β σ E γ : Type} (ps : List (ParsecT m β σ E γ))
  : ParsecT m β σ E γ :=
  List.foldr (fun a b => a <|> b) Alternative.failure ps

/- m-polymorphic choice -/
def choice {m : Type → Type v} {σ α E β : Type} {γ : Type} [MonadParsec m σ α E β] [Alternative m]
  (ps : List (m γ))
  : m γ :=
  List.foldr (fun a b => a <|> b) Alternative.failure ps

/- m-polymorphic noneOf -/
-- def noneOf {m : Type → Type v} [MonadParsec m σ α E β]

def satisfy {m : Type u → Type v} {σ α E β : Type u} [MonadParsec m σ α E β] (f : β → Bool) : m β :=
  MonadParsec.token σ α E (fun x => if f x then .some x else .none) []

def anySingle {m : Type u → Type v} {σ α E β : Type u} [i: MonadParsec m σ α E β] : m β :=
  @satisfy m σ α E β i (fun _ => true)

def noneOf {m : Type u → Type v} {σ α E β : Type u} [BEq β] [i: MonadParsec m σ α E β] (cs : List β): m β :=
  @satisfy m σ α E β i $ fun c => (cs.indexOf? c).isNone

def oneOf {m : Type u → Type v} {σ α E β: Type u} [BEq β] [i: MonadParsec m σ α E β] (cs : List β): m β :=
  @satisfy m σ α E β i $ fun c => (cs.indexOf? c).isSome

/- Even if the parser `p` fails, `option'` succeds without consuming input.
Otherwise, it succeeds with consuming input. -/
def option' {m : Type u → Type v} {℘ β x : Type u}
            (p : ParsecT m β ℘ PUnit x) : ParsecT m β ℘ PUnit (Option x) :=
  (p >>= fun y => pure $ .some y) <|> pure none

/- Even if the parser `p` fails, `option'` succeds without consuming input.
Otherwise, it succeeds with consuming input. -/
def option'' {℘ β x : Type u} (p : Parsec β ℘ PUnit x) : Parsec β ℘ PUnit (Option x) :=
  @option' Id ℘ β x p

/- m-polymorphic option -/
def option {m : Type → Type v} {σ α E β : Type} {γ : Type}
           [MonadParsec m σ α E β] [Alternative m] [Monad m]
           (p : m γ)
           : m (Option γ) :=
  (p >>= fun y => pure $ .some y) <|> pure none
