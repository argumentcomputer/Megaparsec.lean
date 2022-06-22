# Megaparsec

This is a port of the Haskell package [megaparsec](https://hackage.haskell.org/package/megaparsec) to Lean 4.

# Idea

The big idea of Megaparsec goes like this:

`MonadParsec` is a typeclass.
If a type is `MonadParsec`, it means that there are:
 1. Basic parsers defined on it.
 2. Basic parser combinators defined on it.
 3. Ways to retrieve and update parser state.
 4. Track errors with ParseError.
 5. Thread the values through a particular monad.

`ParsecT` is a structure designed to be a `MonadParsec` and a trasformer that adds its capabilities to the underlying monad.

# Hacking

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in `reference/megaparsec`.
To download it, include `--recursive` when cloning this repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

I tried both nix and GHCup, both seem to be currently broken, so I disabled HLS VSCode extension for the time being.
