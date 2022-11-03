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

`Parsec` has several type arguments: `β ℘ E γ : Type u`.

- `β` is the atomic type. In our example, it's `Char`. That's the type of tokens parsed out of source `℘`.
- `℘` is the source type. In our example, it's `String`. Tokens can be read out of the source via `Straume` facilities. `Straume` allows for transparently reading from files. If you want to read from a file, this type would be `(String × IO.FS.Handle)`. It would mean that finite chunks of type `String` are emitted from a, perhaps-larger-than-RAM file handled with somethign of type `IO.FS.Handle`. See `Main.lean` for a usage example! It's really simple!
- `E` is the custom error type. For quick and dirty parsers, it's `Unit`, but if you want to get fancy, you can create custom errors and construct those based on your parser's fails.
- `γ` is the type of the thing we're parsing out of the source. In this case, we're parsing a `String` (out of a `String`).

You may wonder where did the type `α` go? In `Straume`, we use letter alpha to denote the _composite_ type. Composite types are finite counterparts of streams. Every stream `℘` has a composite buffer, consisting of atomic tokens.

Now let's see how our parser works.

To check for the padding we used `lookAhead` primitive parser because it parses without consuming.

To check for the `|` terminator, we used "alternative parsing" between `c.eof`, which parses only the literal end of stream and `c.eol`.
Due to `(<|>)` signature (or an imperfect `Alternative` implementation?!), we can't simply write `c.eol <|> c.eof`.
It's because `c.eof` returns `Unit`, whereas `c.eol` returns either `"\n"` or `"\r\n"`.
To work around it we used a `Common` combinator `void`, which voids anything, that's at least a `Functor`.

Note that you could have used the same trick, but via `Seq` to substitute the return type of any parser too.
For example, you could have just as well written `(c.eol <|> c.eof *> pure "FIN")`.
We wouldn't care, since the parsed value gets discarded anyway due to `<*` (left sparrow) operator between `stringP` and the sub-parser in question.

There are also some examples in the [Exambles](Examples) folder.

## Running the parser

To simply manually test the parser you wrote, you can use `runParseTestP`:

```lean
def testMyP : IO Unit := do
  -- Succeeds
  IO.println "Successful parsers."
  let (true1, three) ← parseTestP myP "3 2 1"
  let (true2, five) ← parseTestP myP "5|"
  -- Fails
  IO.println "Failing parsers."
  let (false1, _notFive) ← parseTestP myP "5"
  let (false2, _notFiftyFive) ← parseTestP myP "55|"

  pure $ Unit.unit
```

It will also print some errors and results on the screen.

Analogous function to simply run the parser and get the result of a parse is `parseP`.

Just give it a parser, the stream (file) name from which you're parsing and a source which can either be a pure `String` or a `String` buffer (most likely, you want it to be empty) plus a file handle.

A concrete example of parsing straight from a file is:

```lean
  let sIO := string_parsecT IO (String × IO.FS.Handle)
  let cIO := char_parsecT IO (String × IO.FS.Handle)

  let file := System.mkFilePath ["./Tests", "abcd.txt"]
  let h ← IO.FS.Handle.mk file IO.FS.Mode.read false
  let buffed := ("", h)
  let res ← parseTP
    (sIO.stringP "ab" *> sIO.stringP "cd" <* cIO.eol <* cIO.eof)
    "abcd.txt"
    buffed
```

The `parseTP` function shall return either `ParseErrorBundle` or the parse result, which in this case is `String`.

Also, file-based parsing allows you to parse from files that are larger-than-RAM thanks to Straume library.
(We didn't test this extensively yet!)

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

TODO: Matej et al. made a significant UX improvement facilitating `@[defaultIntance]`, and some day we'll describe it here with code samples, but since I don't understand it completely, I can't quite write about it.

# Hacking

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in `reference/megaparsec`.
To download it, include `--recursive` when cloning this repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

I tried both nix and GHCup, both seem to be currently broken, so I disabled HLS VSCode extension for the time being.

## Lean is strict and terms don't have a single type in Lean

You can't port Haskell code to Lean one to one!
