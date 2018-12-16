# `path`: a lambda calculus to explore type-directed program synthesis

## Overview

`path` was initially based on the calculus described in _[A tutorial implementation of a dependently typed lambda calculus][]_. It has been extended with the quantitative type theory described in _[Syntax and Semantics of Quantitative Type Theory][]_.

[A tutorial implementation of a dependently typed lambda calculus]: https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
[Syntax and Semantics of Quantitative Type Theory]: https://bentnib.org/quantitative-type-theory.pdf


## Getting started

Development of `path` typically uses `cabal new-build`:

```
cabal new-build # build the library and pathc
cabal new-repl  # load the library in GHCI
```

Path’s REPL can be run from GHCI:

```haskell
λ import Path.REPL
λ repl (packageSources basePackage)
λ: …
```

or from the CLI:

```
cabal new-run pathc -- -i src/Base/*.path
```
