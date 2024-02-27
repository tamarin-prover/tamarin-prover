# Tamarin Manual README

This is the manual for
[Tamarin](https://github.com/tamarin-prover/tamarin-prover). It is written in
Pandoc markdown, from which both an HTML website can be generated as well as a
PDF book.

The source files can be found in the `src` directory.

[![Build Status](https://travis-ci.org/tamarin-prover/manual.svg?branch=master)](https://travis-ci.org/tamarin-prover/manual) Travis monitors the master branch of this repository. Commits to master trigger a new Travis build, which will commit the updated manual to the gh-pages branch of this repository. This is served by Github Pages at https://tamarin-prover.github.io/manual.

## Prerequisites

To compile the manual, you need [pandoc](http://pandoc.org) and pandoc-citeproc.
We recommend to use [stack](https://www.haskellstack.org/) to install these dependencies.

    stack install pandoc pandoc-citeproc

(If you get any errors while running this, make sure you're running the latest version of Stack: 
`stack update && stack upgrade` then try again.)

To create the PDF, [xelatex](http://xetex.sourceforge.net/) is required,
which is part of the texlive packages. On Ubuntu/Debian systems it can
usually be installed directly.

    sudo apt-get install texlive-xetex texlive-latex-extra texlive-fonts-recommended latex-xcolor lmodern

The build process additionally depends on the `make` toolchain.


## Contributing

There are two main branches: `/master` and `/develop`. The intent is that they are 
synchronised with Tamarin's corresponding [source code](https://github.com/tamarin-prover/tamarin-prover) branches.

To suggest improvements/extensions for the [current manual](https://tamarin-prover.github.io/manual), 
create a pull request for the `/master` branch.

To add documentation for new features that have been accepted into the `/develop` 
branch of Tamarin's source repository, create a pull request for the `/develop` 
branch.


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

