# Independent spthy parser

This directory contains an indepdendent parser for Tamarin's spthy and splib language.
The parser is auto-generated from a tree-sitter grammar.

## Dependencies

- `nodejs`
- `cargo`

## Usage

Install `tree-sitter-cli`:

``` shell
$ make install
```

Generate/update parser library:

``` shell
$ make generate_spthy
$ make generate_splib
```
