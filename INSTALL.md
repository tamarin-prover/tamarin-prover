Installing tamarin-prover
-------------------------

Pre-requisites
--------------

Maude, available at http://maude.cs.illinois.edu/
(version 2.6 and 2.7 work).

GraphViz, available at http://www.graphviz.org/


Tamarin-prover
--------------

You can download the binaries appropriate for your system from
https://github.com/tamarin-prover/bin-dists

You can also compile tamarin-prover from source.  We manage the
Haskell dependencies automatically, using 'stack'. First install
'stack' according to
https://github.com/commercialhaskell/stack/wiki/Downloads

After cloning the tamarin-prover repository run 'make default', which
will install an appropriate GHC for your system, including all
dependencies, and the tamarin-prover executable will be copied to

  ~/.local/bin/tamarin-prover


Limitations on Windows
----------------------

To the best of our knowledge, there is no current GraphViz version
available for Windows, so only the command-line parts of the tool are
functional there.
