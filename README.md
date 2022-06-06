# Megaparsec

This is a port of the Haskell package
[megaparsec](https://hackage.haskell.org/package/megaparsec) to Lean 4.

## Reference implementation as a submodule

The original `megaparsec` repository is included as a reference in
`reference/megaparsec`. To download it, include `--recursive` when cloning this
repository.

If you have this repository cloned already, but need to fetch the reference implementation, please run `git submodule update --init --recursive`

### Haskell language server in VSCode

The latest version of the extension uses GHCup (whatever it is).
If you want to keep using Nix, you'll have to add the following two options to your `settings.json`:

```
  "haskell.manageHLS": "PATH",
  "haskell.serverExecutablePath": "/nix/store/2xrgxzjcxww2z2xh05x06yf4xwcn103a-haskell-language-server-1.4.0.0/bin/haskell-language-server",
```

Where the second line is the output of running `which haskell-language-server`.
At the time of writing, I don't know of a better way to make HLS work aside from this.
