import Megaparsec.Stream
import Megaparsec.Errors.StreamErrors

namespace Result

inductive Result (S E A : Type) [s : Stream.Stream S] where
| ok (x : A)
| err (e : @StreamErrors.ParseError S E s)

end Result
