# Megaparsec

This is a port of the Haskell package [megaparsec](https://hackage.haskell.org/package/megaparsec) to Lean 4.

# How to use it?

## Make your parser

Let's write a parser that bites a digit off a string, but only if it's padded to the right with a space or a pipe symbol at the end of line or input:

```lean
def s := string_simple_pure
def c := char_simple_pure

def laLexer : Parsec Char String Unit String :=
  s.lookAhead ((s.stringP "|" <* (void c.eol <|> c.eof)) <|> s.stringP " ")

def numP : Parsec Char String Unit Nat :=
  (c.oneOf "0123456789".data) >>= fun x => pure $ x.val.toNat - '0'.val.toNat

def takeOneDigitP : Parsec Char String Unit (List Nat) :=
  many' (numP <* laLexer)
```

To check for the padding we used `lookAhead` primitive parser because it parses without consuming.

To check for the `|` terminator, we used "alternative parsing" between `c.eof`, which parses only the literal end of stream and `c.eol`.
Due to `(<|>)` signature (or an imperfect `Alternative` implementation?!), we can't simply write `c.eol <|> c.eof`.
It's because `c.eof` returns `Unit`, whereas `c.eol` returns either `"\n"` or `"\r\n"`.
To work around it we used a `Common` combinator `void`, which voids anything, that's at least a `Functor`.

Note that you could have used the same trick, but via `Seq` to substitute the return type of any parser too.
For example, you could have just as well written `(c.eol <|> c.eof *> pure "FIN")`.
We wouldn't care, since the parsed value gets discarded anyway due to `<*` (left sparrow) operator between `stringP` and the sub-parser in question.

## Exercise for the reader

Check out stuff that `MonadParsec` exports, look around `char_simple` and `string_simple` APIs in `Megaparsec/Char.lean` and `Megaparsec/String.lean` respectively, and patch the example code so that it would _tolerate, but not require_ padding with spaces and the "end-of-line bar" while parsing a digit out of the input.

Send your snippets to @cognivore in Yatima Inc's Zulip!

# Idea

The big idea of Megaparsec goes like this:

`MonadParsec` is a typeclass.
If a type is `MonadParsec`, it means that there are:

1.  Basic parsers defined on it.
2.  Basic parser combinators defined on it.
3.  Ways to retrieve and update parser state.
4.  Track errors with ParseError.
5.  Thread the values through a particular monad.

`ParsecT` is a structure designed to be a `MonadParsec` and a trasformer that adds its capabilities to the underlying monad.

`ParsecT`, and any other thing that implements `MonadParsec` should be `Monad` and `Alternative`.
We're not prioritising applicative parsers at the moment, but you can use `Seq` to swap types in our parsers as well as use the usual `between` combinator.

For example, suppose we have a `Char` parser `newline := char '\n'` and we have a `String` parser `crlf := s.stringP "\r\n"`.
To combine both without losing information, we need to transform the first parser into a `String` parser.
Instead of writing a new parser, we write `(newline *> pure "\n") <|> crlf`.

So far, this is the main use of `Seq` in this library.

# Polymorphism

There is a generic polymorphic machinery, `MonadParsec`.
There is also a concrete default implementation of monad parsec, which is a monad transformer called `ParsecT`.
As the user of Megaparsec, you'll likely be using `ParsecT` or even just `Parsec`, which is `ParsecT` over `Id`.

## ParsecT

## MonadParsec

# Usability

# Hacking

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in `reference/megaparsec`.
To download it, include `--recursive` when cloning this repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

I tried both nix and GHCup, both seem to be currently broken, so I disabled HLS VSCode extension for the time being.

## Lean is strict and terms don't have a single type in Lean

You can't port Haskell code to Lean one to one!
