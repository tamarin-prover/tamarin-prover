# tree-sitter-spthy

Spthy grammar for [tree-sitter](https://github.com/tree-sitter/tree-sitter).

The generated parser is committed so consumers do not need Node.js or the
tree-sitter CLI at build time.

Regenerate it after editing the grammar with `npm run generate`. This command
uses ABI 14 for compatibility with the supported language bindings.

## Go

```sh
go get github.com/tamarin-prover/tamarin-prover/tree-sitter/tree-sitter-spthy@develop
```

Import the language binding as:

```go
import tree_sitter_spthy "github.com/tamarin-prover/tamarin-prover/tree-sitter/tree-sitter-spthy/bindings/go"
```

## Rust

```toml
[dependencies]
tree-sitter = "0.23"
tree-sitter-spthy = { git = "https://github.com/tamarin-prover/tamarin-prover.git", branch = "develop" }
```

## Python

```sh
python -m pip install \
  "tree-sitter-spthy[core] @ git+https://github.com/tamarin-prover/tamarin-prover.git@develop#subdirectory=tree-sitter/tree-sitter-spthy"
```

For reproducible builds, replace `develop` with a release tag or commit hash.
