import Megaparsec.ParserState
import Megaparsec.Pos

import Straume.Coco
import Straume.Iterator
import Straume.Zeptoparsec

open Megaparsec.ParserState
open Megaparsec.Pos

open Straume.Coco
open Straume.Iterator
open Zeptoparsec

namespace Megaparsec.Streamable

class Streamable (℘ : Type u) where
/-
  Given an offset `o` and initial `PosState`, adjust the state in such
  a way that it starts at the offset.

  Return two values (in order):

      * `Option String` representing the line on which the given offset
        `o` is located. It can be omitted (i.e. `.none`); in that case
        error reporting functions will not show offending lines. If
        returned, the line should satisfy a number of conditions that are
        described below.
      * The updated `PosState` which can be in turn used to locate
        another offset `o'` given that `o' >= o`.

  The `String` representing the offending line in input stream should
  satisfy the following:

      * It should adequately represent location of token at the offset of
        interest, that is, character at `column` of the returned
        `SourcePos` should correspond to the token at the offset @o@.
      * It should not include the newline at the end.
      * It should not be empty, if the line happens to be empty, it
        should be replaced with the string `"<empty line>"`.
      * Tab characters should be replaced by appropriate number of
        spaces, which is determined by the `tabWidth` field of
        `PosState`.
-/
  reachOffset (o : Nat) (pst : PosState ℘) : (Option String × PosState ℘)

  -- A version of `reachOffset` that may be faster because it doesn't need
  -- to fetch the line at which the given offset in located.
  --
  -- It's currently not possible to use `reachOffsetNoLine` as a minimal
  -- definition; unlike Haskell, Lean4 doesn't(?) allow mutually
  -- recursive class defs.
  reachOffsetNoLine (o : Nat) (pst : PosState ℘) : PosState ℘
    := (reachOffset o pst).2

export Streamable (reachOffset reachOffsetNoLine)

---===========================================================--
---========================= HELPERS =========================--
---===========================================================--

-- A helper definition to facilitate defining `reachOffset` for various
-- stream types.
def reachOffset'
  (fsplit : Nat → ℘ → (℘ × ℘)) -- How to split input stream at given offset
  (ffold : ∀φ, (φ → β → φ) → φ → ℘ → φ) [Iterable ℘ β] [DecidableEq β] -- How to fold over input stream;
  -- How to convert chunk of input stream into a `String`.
  -- We only need it to handle adding `linePrefix`.
  (fstr : ℘ → String)
  (nlt : β) (tabt : β) -- Newline token and tab token
  (o : Nat) -- Offset to reach
  (pst : PosState ℘) -- Initial `PosState` to use
  [DecidableEq ℘] [Inhabited ℘] -- for Zeptoparsec
  : (Option String × PosState ℘) -- Line at which `SourcePos` is located, updated `PosState`
  := let prepend c (str : ℘) := fromList $ c :: (toList str)
  let go | (apos, g), ch => if ch = nlt then
      ({ apos with line := apos.line + pos1, column := pos1 }, id)
    else if ch = tabt then
      let c' := apos.column.pos
      ({ apos with column :=
        Pos.mk $ c' + pst.tabWidth - ((c' - 1) % pst.tabWidth)}
      , (g ∘ prepend ch))
    else ({ apos with column := apos.column + pos1}, (g ∘ prepend ch))
  let (pre, post) := fsplit (o - pst.offset) pst.input
  let (spos, f) :=
    ffold (SourcePos × (℘ → ℘)) go (pst.sourcePos, id) pre
  let isSameLine := spos.line = pst.sourcePos.line
  let addPrefix xs := if isSameLine then pst.linePrefix ++ xs else xs

  let taken? := (Zeptoparsec.run (manyChars (satisfy (fun c => c != nlt))) post).toOption
  let location :=
    match (expandTab pst.tabWidth ∘ addPrefix ∘ fstr ∘ f) <$> taken? with
    | .none    => .none
    | .some "" => .some "<empty line>"
    | .some xs => .some xs
  (location,
  { input := post, offset := max pst.offset o, sourcePos := spos
  , tabWidth := pst.tabWidth
  , linePrefix :=
      if isSameLine
      then pst.linePrefix ++ fstr (f default)
      else fstr $ f default
  })

def reachOffsetNoLine'
  (fsplit : Nat → ℘ → (℘ × ℘)) -- How to split input stream at given offset
  (ffold : ∀φ, (φ → β → φ) → φ → ℘ → φ) [Iterable ℘ β] [DecidableEq β] -- How to fold over input stream;
  -- How to convert chunk of input stream into a `String`.
  -- We only need it to handle adding `linePrefix`.
  (nlt : β) (tabt : β) -- Newline token and tab token
  (o : Nat) -- Offset to reach
  (pst : PosState ℘) -- Initial `PosState` to use
  [DecidableEq ℘] [Inhabited ℘] -- for Zeptoparsec
  : PosState ℘ := -- Updated `PosState`
  let go | apos, ch => if ch = nlt
    then { apos with line := apos.line + pos1, column := pos1 }
    else if ch = tabt then
      let c' := apos.column.pos
      { apos with column :=
        Pos.mk $ c' + pst.tabWidth - ((c' - 1) % pst.tabWidth) }
    else { apos with column := apos.column + pos1 }
  let (pre, post) := fsplit (o - pst.offset) pst.input
  let spos := ffold SourcePos go pst.sourcePos pre

  { pst with input := post, offset := max pst.offset o, sourcePos := spos }

---===========================================================--
---================== STREAMABLE INSTANCES ===================--
---===========================================================--

private def splitAt (n : Nat) (str : String) := (str.take n, str.drop n)

instance : Streamable String where
  reachOffset o pst := reachOffset' splitAt @String.foldl id '\n' '\t' o pst
  reachOffsetNoLine o pst :=
    reachOffsetNoLine' splitAt @String.foldl '\n' '\t' o pst

instance [Streamable ℘] [Coco ℘ (℘ × η)] : Streamable (℘ × η) where
  reachOffset o pst :=
    let inner : ℘ := Coco.coco pst.input
    let (ol, npst) := reachOffset o $ { pst with input := inner }
    (ol, { npst with input := Coco.replace pst.input npst.input })
