This is a simple introduction to model checking, written in literate Haskell.
See src/ModelChecking*.lhs.

The `build.sh` script runs `cabal build` to compile the code, and builds
documentation using `pandoc`.

You can use `nix develop` to enter a shell with all dependencies required to
run `build.sh`. Or use:

```console
$ nix build
$ firefox result-doc/share/doc/model-checking-0.1.0.0/html/src/ModelChecking{1,2}.html
```
