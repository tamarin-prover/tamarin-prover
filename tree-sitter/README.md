# Independent spthy parser

This directory contains an independent parser for Tamarin's spthy language.
The parser is auto-generated from a tree-sitter grammar.

## Dependencies

- Node.js and npm

## Usage

Generate or update the parser with the pinned tree-sitter CLI version:

``` shell
$ make generate
```

This installs the dependencies pinned in `package-lock.json` before running the
generator.
