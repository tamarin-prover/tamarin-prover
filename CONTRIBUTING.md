Developing and contributing to tamarin-prover
---------------------------------------------

We use Linux during the development of Tamarin. Mac OS X can be used
just as well. Windows can be used for development also, but the
directory layout simplification introduced via symbolic links will not
work.

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
