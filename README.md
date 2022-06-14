# Megaparsec

This is a port of the Haskell package
[megaparsec](https://hackage.haskell.org/package/megaparsec) to Lean 4.

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in
`reference/megaparsec`. To download it, include `--recursive` when cloning this
repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

I tried both nix and GHCup, both seem to be currently broken, so I disabled HLS VSCode extension for the time being.
