import Megaparsec.Errors.StreamErrors
import Straume.Iterator

namespace Megaparsec.Errors.Result

inductive Result (β : Type u) (γ : Type v) (E : Type u) where
| ok (x : γ)
| err (e : StreamErrors.ParseError β E)

export Result (ok err)

end Result
