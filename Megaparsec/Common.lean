import Megaparsec.MonadParsec

import YatimaStdLib

/-!
# Common token combinators

Simple combinators that are agnostic to the stream they're applied to.
-/

namespace Megaparsec.Common

-- def string [m : Monad M] [a : Alternative M]
--            [strm : Stream.Stream S] [mₚ : @MonadParsec.MonadParsec M E S m a strm]:
--            strm.Tokens → M (strm.Tokens) :=
--   fun expected =>
--     mₚ.tokens E S (fun x y => @BEq.beq (strm.Tokens) (@NEList.BEqOfOrd strm.Tokens strm.ordTokens) x y) expected

-- TODO: Case-insensitive string

end Common
