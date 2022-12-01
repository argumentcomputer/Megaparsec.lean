import Megaparsec

/-!
# A Megaparsec tutorial

In this tutorial we will cover a simple (yet not trivial) use case for Megaparsec.
We will stick to basic tools of Megaparsec, but keep in mind that there are more
high level combinators available that would be covered in another tutorial.

Let's parse the source code of a simplified and non-structured Lisp-like language.
We want our parser to accept atomic symbols, numbers or parenthesized sequences of those.
For example, the following would be valid sources for our language:

* `f`, `10`, `()`, `(add 1 3)`, `(mul 2 (sub 1 9) 5)`

So first let's define the datatype to represent our grammar.
-/

inductive Grammar
  | nil
  | sym  (name  : String)
  | num  (value : Nat)
  | cons (head tail : Grammar)
  deriving Repr

instance : ToString Grammar where
  toString x := toString $ repr x

open Megaparsec Parsec Common

/-- We define `P` as a parsec over strings, whose tokens are chars -/
abbrev P := Parsec Char String Unit

/-- We start by parsing numbers, a sequence of at least some digit -/
def numP : P Grammar := do
  let x : List Char ← some' (satisfy Char.isDigit)
  let str : String := String.mk x
  return .num $ String.toNat! str

/-- A symbol must start with a letter, followed by any other alphanumeric character -/
def symP : P Grammar := do
  let c : Char ← satisfy Char.isAlpha
  let cs : List Char ← many' (satisfy Char.isAlphanum)
  return .sym $ ⟨c :: cs⟩

/--
Let's call numbers and symbols "atoms".
First we try to parse a number and if it fails we try to parse a symbol -/
def atomP : P Grammar :=
  numP <|> symP

#eval discard $ parseTestP atomP "101" -- Grammar.num 101
#eval discard $ parseTestP atomP "ab0" -- Grammar.sym ab0

/- This is how Megaparsec shows parsing errors: -/
#eval discard $ parseTestP numP "abc"
-- 1:1:
--   |
-- 1 | abc
--   | ^
-- unexpected  'a'

/-- For lists, we will need a way to ignore blank characters -/
def blanksP : P Unit := do
  discard $ many' (satisfy fun c => [' ', '\n', '\t'].contains c)

mutual

/--
As we've said in the beginning, an element of our grammar is either an atom or a list of atoms.
However, that description isn't precise enough because we also want to accept nested lists.
So we can define the parser for the grammar as follows:

* An element of our grammar is either an atom or a list
* A list is a sequence of elements of the grammar

We also consume blank characters before and
-/
partial def grammarP : P Grammar := do
  blanksP -- discard blank characters before anything
  let x : Grammar ← atomP <|> listP
  return x

/--
Lists must start and end with parentheses, with any number of grammar elements
in between.

This function could be implemented with `between` and `sebEndBy`, but, again,
let's try to stick to the simplest tools in this tutorial.
-/
partial def listP : P Grammar := do
  discard $ single '('
  blanksP -- this is necessary for empty lists, otherwise `grammarP` would crash
          -- at ')'
  let xs : List Grammar ← many' grammarP
  discard $ single ')'
  return xs.foldr (init := .nil) fun x acc => .cons x acc

end

#eval discard $ parseTestP grammarP "(  )" -- Grammar.nil

#eval discard $ parseTestP grammarP " (add (inv  \t  2) \n 3)\n "
-- Grammar.cons
--   (Grammar.sym "add")
--   (Grammar.cons
--     (Grammar.cons (Grammar.sym "inv") (Grammar.cons (Grammar.num 2) (Grammar.nil)))
--     (Grammar.cons (Grammar.num 3) (Grammar.nil)))

/-- Now we can write the final function for parsing source code -/
def parseGrammar (code : String) : Except String Grammar :=
  Except.mapError toString $ parse grammarP code

#eval parseGrammar "(add 0 3)"
-- Except.ok
--  (Grammar.cons (Grammar.sym "add") (Grammar.cons (Grammar.num 0)
--    (Grammar.cons (Grammar.num 3) (Grammar.nil))))
