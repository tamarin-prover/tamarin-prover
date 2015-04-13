The Tamarin prover repository
=============================
![master branch build-status](https://travis-ci.org/tamarin-prover/tamarin-prover.svg?branch=develop)

This README describes the organization of the repository of the Tamarin prover
for security protocol verification. Its intended audience are interested
users and future developers of the Tamarin prover. For installation
and usage instructions of the Tamarin prover see:
http://www.infsec.ethz.ch/research/software/tamarin.

TODO: @cas, installation, usage, and examples (see #147)


Developing
----------

We use Linux and Mac OS X during the development of Tamarin. Windows can be
used for development, but the directory layout simplification introduced via
symbolic links will not work.

As of October 1st, 2012, we started organizing our branches according to
http://nvie.com/posts/a-successful-git-branching-model/.
We moreover use the Haskell coding style from
https://github.com/tibbe/haskell-style-guide/blob/master/haskell-style.md.

We manage the Haskell dependencies using 'cabal sandbox'es with all transitive
dependencies pinned in the 'cabal.config' file. To bootstrap development, you
should run a successful sandboxed installation by calling 'make install' in
the repositories root directory. This will build the tamarin-prover executable
at

  cabal-sandbox/bin/tamarin-prover

This file is relocatable and you can copy it anywhere you'd like. Also to
other systems with the same 'libc' and 'libgmp' libraries.

To enter the GHCi repl, type

  cabal repl

in the root directory of this repository. If you are working on one of the
tamarin-prover-XXX libraries, you can use GHCi to load them by typing 'cabal
repl' in their respective root directory.

The static web assets are embedded into the built binary in the file
'src/Web/Dispatch.hs'. See the note on 'staticFile' on how to enable dynamic
reloading in case you are working on the web assets.

The variants of the intruder rules for Diffi-Hellman exponentiation and
Bilinear-Pairing are embedded statically in 'src/Main/TheoryLoader.hs'. If you
change them, then this file needs to be recompiled for the changes to come
into effect.

Note that we welcome all contributions, e.g., further protocol models. Just
send us a pull request.


Version Numbering Policy
-----------------------

We use version numbers with four components.

 - The first component is the major version number. It indicates complete
   rewrites of the codebase.
 - The second component is the minor version number. We use odd minor version
   numbers to denote development releases intended for early adopters. We use
   even minor version numbers to denote public releases, which are also
   published on [Hackage](http://hackage.haskell.org/package/tamarin-prover).
 - The third component indicates bugfix releases.
 - The fourth component indicates documentation and meta-data changes.

We ensure that the external interface of a version of the Tamarin prover is backwards
compatible with the external interface of all versions that agree on the major
and minor version number.

We announce all releases of the Tamarin prover on:
http://www.infsec.ethz.ch/research/software/tamarin.


Manual
------

The manual is `data/doc/MANUAL`. It is part of every installation of the
Tamarin prover.


Example Protocol Models
-----------------------

All example protocol models are found in the directory

    ./data/examples/

, which is also symlinked as `./examples`. All models that we consider stable
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
