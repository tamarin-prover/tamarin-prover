The Tamarin prover repository
=============================
![master branch build-status](https://travis-ci.org/tamarin-prover/tamarin-prover.svg?branch=develop)

This README describes the organization of the repository of the Tamarin prover
for security protocol verification. Its intended audience are interested
users and future developers of the Tamarin prover. For installation
and usage instructions of the Tamarin prover see chapter 2 of the manual:
https://tamarin-prover.github.io/manual/book/002_installation.html


Developing and contributing
---------------------------

See [contributing instructions](CONTRIBUTING.md).


Version Numbering Policy
-----------------------

We use version numbers with four components.

 - The first component is the major version number. It indicates complete
   rewrites of the codebase.
 - The second component is the minor version number. We use odd minor version
   numbers to denote development releases intended for early adopters. We use
   even minor version numbers to denote public releases, which are also
   published.
 - The third component indicates bugfix releases.
 - The fourth component indicates documentation and meta-data changes.

We ensure that the external interface of a version of the Tamarin prover is backwards
compatible with the external interface of all versions that agree on the major
and minor version number.

We announce all releases of the Tamarin prover on:
http://tamarin-prover.github.io


Manual
------

The manual is available as PDF or HTML at https://tamarin-prover.github.io/manual/index.html

Experimental improved graph output
----------------------------------

You can use our experimental improved graph output which may be
helpful for very large graphs that can be created for complicated
protocols. To enable this feature read the instructions about
[improved graphs](/misc/cleandot/README.md).

Spthy code editors
------------------

The project contains support for spthy syntax highlighting and support
in the [etc](/etc/) directory. This includes support for [Sublime Text](/etc/SUBLIME_TEXT.md), [VIM](/etc/spthy.vim) and [Notepad++](/etc/notepad_plus_plus_spthy.xml).


Example Protocol Models
-----------------------

All example protocol models are found in the directory

    ./examples/

All models that we consider stable
are part of every installation of the Tamarin prover. See
`tamarin-prover.cabal` for the list of installed protocols. We use the
following sub-directories to organize the models.

~~~~
csf12/         the AKE case studies from our CSF'12 paper.
classic/       classic security protocols like the ones from
               [SPORE](http://www.lsv.ens-cachan.fr/Software/spore/table.html)
loops/         experiments for testing loop-invariants and protocols with
               non-monotonic state
related_work/  examples from related work on protocols with loops or
               non-monotonic state
experiments/   all other experiments
ake/           more AKE examples including ID-based and tripartite group KE
               protocols based on bilinear pairing
features/      (small) models that demonstrate a given feature
ccs15/	       the observational equivalence case studies from our CCS'15 paper
~~~~

Feel free to add more sub-directories and describe them here.

In general, we try use descriptive names for files containing the models. We
also document all our findings as comments in the protocol model.  Moreover,
we use the following header in all files to make their context more explicit.

~~~~
/*
   Protocol:    Example
   Modeler:     Simon Meier, Benedikt Schmidt
   Date:        January 2012

   Status:      working

   Description of protocol.

*/
~~~~
