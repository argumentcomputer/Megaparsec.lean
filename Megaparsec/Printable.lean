import YatimaStdLib
import Straume.Iterator

open Straume.Iterator

namespace Megaparsec.Printable

class Printable (β : Type u) where
  -- Pretty-print non-empty list of tokens. This function is also used
  -- to print single tokens (represented as singleton lists).
  showTokens : NEList β → String

  -- Return the number of characters that a non-empty list of tokens
  -- spans. The default implementation is sufficient if every token spans
  -- exactly 1 character.
  tokensLength : NEList β → Nat := fun xs => xs.toList.length

export Printable (showTokens tokensLength)

--===========================================================--
--========================= HELPERS =========================--
--===========================================================--

-- TODO: why are almost all escape sequences unrecognised by Lean?
private def charPretty' : Char → Option String
  -- | '\NUL' => .some "null"
  -- | '\SOH' => .some "start of heading"
  -- | '\STX' => .some "start of text"
  -- | '\ETX' => .some "end of text"
  -- | '\EOT' => .some "end of transmission"
  -- | '\ENQ' => .some "enquiry"
  -- | '\ACK' => .some "acknowledge"
  -- | '\BEL' => .some "bell"
  -- | '\BS' => .some "backspace"
  | '\t' => .some "tab"
  | '\n' => .some "newline"
  -- | '\v' => .some "vertical tab"
  -- | '\f' => .some "form feed"
  | '\r' => .some "carriage return"
  -- | '\SO' => .some "shift out"
  -- | '\SI' => .some "shift in"
  -- | '\DLE' => .some "data link escape"
  -- | '\DC1' => .some "device control one"
  -- | '\DC2' => .some "device control two"
  -- | '\DC3' => .some "device control three"
  -- | '\DC4' => .some "device control four"
  -- | '\NAK' => .some "negative acknowledge"
  -- | '\SYN' => .some "synchronous idle"
  -- | '\ETB' => .some "end of transmission block"
  -- | '\CAN' => .some "cancel"
  -- | '\EM' => .some "end of medium"
  -- | '\SUB' => .some "substitute"
  -- | '\ESC' => .some "escape"
  -- | '\FS' => .some "file separator"
  -- | '\GS' => .some "group separator"
  -- | '\RS' => .some "record separator"
  -- | '\US' => .some "unit separator"
  -- | '\DEL' => .some "delete"
  -- | '\160' => .some "non-breaking space"
  | _ => .none

private def charPretty : Char → String
  | ' ' => "space"
  | ch  => (charPretty' ch).getD $ s!"'{ch}'"

private def stringPretty : NEList Char → String
  | ⟦x⟧ => charPretty x
  | ⟦'\r','\n'⟧ => "crlf newline"
  | xs =>
    let f c := match charPretty' c with
      | .none => s!"{c}"
      | .some pretty => s!"<{pretty}>"
    s!"\"{String.join $ f <$> xs.toList}\""

--===========================================================--
--=================== PRINTABLE INSTANCES ===================--
--===========================================================--

instance : Printable Char where
  showTokens := stringPretty

-- This isn't in the original MP, but we want to keep instances as
-- simple as possible; consequently, we allow empty string be in the
-- non-empty string list, but we don't represent it unless the whole
-- list consists of a single empty string.
instance : Printable String where
  showTokens nl :=
    let showStr str := (stringPretty <$> NEList.nonEmptyString str).getD ""
    let rec go xs := match xs with
      | ⟦x⟧ => [showStr x]
      | "" :| xs => go xs
      | x  :| xs => showStr x :: go xs
    match String.join $ go nl with
    | "" => "empty string"
    | joined => s!"\"{joined}\""

instance : Printable UInt8 where
  showTokens := stringPretty ∘ Functor.map (fun i => Char.ofNat $ i.toNat)

open ByteArray in
instance : Printable Bit where
  showTokens
    | ⟦b⟧ => s!"'{b}'"
    | nl => let rec go xs := match xs with
      | ⟦b⟧ => [toString b]
      | b :| bs => toString b :: go bs
      s!"\"{String.join $ go nl}\""
