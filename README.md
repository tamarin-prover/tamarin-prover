# Tamarin Manual README

This is the manual for
[Tamarin](https://github.com/tamarin-prover/tamarin-prover). It is written in
Pandoc markdown, from which both an HTML website can be generated as well as a
PDF book.

The source files can be found in the `src` directory.


## Prerequisites

To compile the manual, you need [pandoc](http://pandoc.org) and pandoc-citeproc.
We recommend to use [stack](www.haskellstack.org/) to install these dependencies.

    stack install pandoc pandoc-citeproc

To create the PDF, [xelatex](http://xetex.sourceforge.net/) is required,
which is part of the texlive packages. On Ubuntu/Debian systems it can
usually be installed directly.

    sudo apt-get install texlive-xetex

The build process additionally depends on the `make` toolchain.


## Compiling the manual

### HTML

Building the online (HTML) documentation can be done by invoking the `Makefile`
without arguments, i.e.:

    make

In this case, the starting page would be `index.html` which would link directly
to `book/001_introduction.html`.

### PDF

The PDF-based (printable) book documentation can be build by invoking the
`Makefile` with the `pdf` argument:

    make pdf

The result should end up in `tex/tamarin-manual.pdf`.


## Problems

The navigation on the left is hardcoded in templates/template.html. In
particular, the navigations directly refers to the names of the files in `src`.
This means one has to take care when renaming or adding sections.

