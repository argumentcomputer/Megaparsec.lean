import Megaparsec.Errors.StreamErrors

namespace Megaparsec.Errors.Result

inductive Result (α E : Type u) where
| ok (x : α)
| err (e : StreamErrors.ParseError α E)

export Result (ok err)

end Result
