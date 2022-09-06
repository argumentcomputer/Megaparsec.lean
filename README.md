# Megaparsec

This is a port of the Haskell package [megaparsec](https://hackage.haskell.org/package/megaparsec) to Lean 4.

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

##

# Hacking

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in `reference/megaparsec`.
To download it, include `--recursive` when cloning this repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

I tried both nix and GHCup, both seem to be currently broken, so I disabled HLS VSCode extension for the time being.

## Lean is strict and terms don't have a single type in Lean

You can't port Haskell code to Lean one to one!
