import Megaparsec.Megaparsec
/-!
# Common token combinators

Simple combinators that are agnostic to the stream they're applied to.
-/

namespace Common

#check Megaparsec.MonadParsec.tokens
#check (fun x y => x == y)

def string [m : Monad M] [a : Alternative M]
           [strm : Megaparsec.Stream S] [mₚ : @Megaparsec.MonadParsec M E S m a strm]:
           strm.Tokens → M (strm.Tokens) :=
  fun expected =>
    mₚ.tokens E S (fun x y => @BEq.beq (strm.Tokens) (@Megaparsec.ord2beq strm.Tokens strm.ordTokens) x y) expected

-- TODO: Case-insensitive string

end Common
