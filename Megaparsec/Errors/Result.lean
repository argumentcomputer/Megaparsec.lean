import Megaparsec.Errors.ParseError
import Straume.Iterator

namespace Megaparsec.Errors.Result

open Megaparsec.Errors.ParseError
inductive Result (β : Type u) (γ : Type v) (E : Type u) where
| ok (x : γ)
| err (e : ParseError β E)

export Result (ok err)

end Result
