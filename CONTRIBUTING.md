Developing and contributing to tamarin-prover
---------------------------------------------

We use Linux during the development of Tamarin. Mac OS X can be used
just as well. Windows is not recommended as no testing is possible
(due to GraphViz and Maude) and additionally the directory layout
simplification introduced via symbolic links will not work.

As of October 1st, 2012, we started organizing our branches according to
http://nvie.com/posts/a-successful-git-branching-model/.
We moreover use the Haskell coding style from
https://github.com/tibbe/haskell-style-guide/blob/master/haskell-style.md.

We manage the Haskell dependencies automatically, using
'stack'. Install 'stack' according to
https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

After cloning this repository run 'make default', which will install an
appropriate GHC for your system, including all dependencies, and the
tamarin-prover executable will be copied to

  ~/.local/bin/tamarin-prover

This file is relocatable and you can copy it anywhere you'd like. Also to
other systems with the same 'libc' and 'libgmp' libraries.

The static web assets are embedded into the built binary in the file
'src/Web/Dispatch.hs'. See the note on 'staticFile' on how to enable dynamic
reloading in case you are working on the web assets.

The variants of the intruder rules for Diffie-Hellman exponentiation and
Bilinear-Pairing are embedded statically in 'src/Main/TheoryLoader.hs'. If you
change them, then this file needs to be recompiled for the changes to come
into effect.

Note that we welcome all contributions, e.g., further protocol models. Just
send us a pull request.


Branches
--------

There is only the 'develop' branch to which we are happy to accept your pull requests.

In general, we do ask developers to use their own, external, branches
and send pull requests to include. There are some historical branches
that we will keep around, but that are definitely stale and will
bitrot:

feature-user-defined-sorts
feature-ac-rewrite-rules

Regression testing for pull requests
------------------------------------

Before submitting a pull request, please double check that your changes do not break any of the existing proofs by running the regression test suite. To do this run the following commands in your clone of tamarin-prover:

rm -rf case-studies

make case-studies

diff -r case-studies case-studies-regression

This first removes any existing case-study runs you may have, then runs all the case studies, and finally compares the resulting output to the stored expected output. It is expected that the runtime of the analyses changes every time (but on the order of 1% or so, possibly more depending on the machine you run it on). If that is the only change, everything is fine. If some proof steps get reordered, but the number of steps stays constant that is ok, but should be noted. If that number changes or runtimes change significantly that must be discussed in a pull request.

If you are running the regression on a server you can run multiple case studies in parallel by adding the "-j #" parameter where # is the number of parallel runs. Note that your machine should have 16GB of memory per run, and each run uses 3 threads already. For example:

make -j 6 case-studies

to run 6 case studies in parallel.
