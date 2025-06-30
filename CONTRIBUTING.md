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


Making new releases
-------------------

The Tamarin Prover is distributed through a number of channels: source and binaries through Github, and packages through Homebrew, Arch and NixOS. A new release should be made whenever a major new feature has been added, some significant bug(s) have been fixed, a new version of GHC should be used (possibly necessary due to MacOS auto-update), or whenever the maintainers deem it desirable. When a new release is cut, here's how to prepare the release first and then update the various distribution channels.

1. Make the new release on Github. @rsasse or @jdreier usually does this.

   1. run `python3 regressionTests.py -s` and check for any error

   2. run `tamarin-prover test`

   3. call `tamarin-prover` and copy CSF'12 automatic command and
      check whether verification succeeds, i.e., run
      `tamarin-prover --prove *.spthy`
      in the examples/csf12 folder.

   4. generate `intruder_variants_{dh,bp}.spthy` and diff with versions
      in data/ so:
      `tamarin-prover variants > tmp.txt`
      `diff tmp.txt data/intruder_variants_both_bp_dh_for_diff.txt`
      which should be empty.

   5. call `tamarin-prover` and copy CSF'12 interactive command and
      execute the following steps in the GUI after running
      `tamarin-prover interactive .`
      in the examples/csf12 folder.

        (a) open one of the presented theories
        (b) try shortcuts (J,K,j,k,1,2,..,a)
        (c) try different graph/sequent options
        (d) try Download
        (e) try 'Loading a new theory' from the start page

   6. Bump version number to even minor version in cabal files and code,
      commit version bump, by running the `version-change.sh` script as
      described in its comments. Then merge from 'develop' into 'master'
      and use "Release" functionality to prepare the release.


2. Update the Homebrew tap at tamarin-prover/homebrew-tap:
   1. Update the [formula](https://github.com/tamarin-prover/homebrew-tap/blob/master/Formula/tamarin-prover.rb) to point to the new source tarball.
   2. [Build bottles](https://github.com/tamarin-prover/homebrew-tap#building-bottles) for Mac and Windows, and add them to the Homebrew formula as well.
3. Update the NixOS repo: @thoughtpolice usually does this ([example](https://github.com/NixOS/nixpkgs/commit/04002e2b7186c166af87c20da7a7ceb8c0edb021))
4. Update the Arch repo: @felixonmars usually does this


Branches
--------

There is only the 'develop' branch to which we are happy to accept your pull requests.

In general, we do ask developers to use their own, external, branches
and send pull requests to include. There are some historical branches
that we will keep around, but that are definitely stale and will
bitrot:

  - `feature-user-defined-sorts`
  - `feature-ac-rewrite-rules`

Regression testing for pull requests
------------------------------------

Before submitting a pull request, please double check that your changes do not break any of the existing proofs by running the regression test suite. To do this run the following commands in your clone of tamarin-prover:

```
rm -rf case-studies
python3 regressionTests.py
```

If you have changes that pertain to SAPIC+, run

```
rm -rf case-studies
python3 regressionTests.py -s
```

This first removes any existing case-study runs you may have, then runs all the case studies, and finally compares the resulting output to the stored expected output. The script shows any differences between the outputs, and also compares the runtimes. It is expected that the runtime of the analyses changes every time (but on the order of 1% or so, possibly more depending on the machine you run it on), hence the times are shown using a color code: green for small changes, yellow for bigger changes, and red for significant changes. If small runtime changes are only differences, everything is fine. If some proof steps get reordered, but the number of steps stays constant that is ok, but should be noted. If that number changes or runtimes change significantly that must be discussed in a pull request.

If you are running the regression on a server you can run multiple case studies in parallel by adding the "-j #" parameter where # is the number of parallel runs. Note that your machine should have 16GB of memory per run, and each run uses 3 threads already. For example:

```
python3 regressionTests.py -j 6
```

For more details about `regressionTests.py`, have a look at `doc/READMEregressionTests.md`


Editor support
--------------

The directory `etc` holds files for editor support. For the `vim` editor, it is
desirable to have a separate repository for these files, hence we include this
directory as a git-subtree. [Here is
a tutorial](https://www.atlassian.com/git/tutorials/git-subtree). In summary:

1. To merge changes from the outside  repository into `etc` here, run the
   following command, where $branch is the branch you are in now, which is
   almost always `develop`.
```
 git subtree pull --prefix etc https://github.com/tamarin-prover/editors $branch --squash
```

2. To contribute changes in `etc` back to that outside repository, run the
   following, where `$github_user` is your github user name, because you need
   to fork that directory, too.
```
git subtree push --prefix etc https://github.com/$github_user/editors $branch
```

3. FYI: if we ever want to add another subtree, we use:
```
git subtree add --prefix $local_dir $remote_url $remote_branch --squash
```

Debugging
---------

We provide a module tailored to debugging the codebase in the REPL.
The module is provided in `src/Main/ScratchPad.hs` and you can load it by running `stack ghci` in the top-level directory of this repository.
It is important that you run this command in the top-level directory.
If not, there will be an error.

After you entered GHCI, you must load the scratch pad module using the command `:m *Main.ScratchPad`. If you then run the function `debug`, the debugging starts!

The `ScratchPad` module is designed such that you can explore the proof tree using the functions `paths` and `methodsAt` and debug by modifying `debugInput` and `debugM`.
You can find more documentation in the `Main.ScratchPad` module.

Here is a complete example of how debugging could work:
```
stack ghci
ghci> :m *Main.ScratchPad
ghci> debug
[Theory NAXOS_eCK] Theory loaded
[Theory NAXOS_eCK] Theory translated
[Theory NAXOS_eCK] Derivation checks started
[Theory NAXOS_eCK] Derivation checks ended
[Theory NAXOS_eCK] Theory closed
--- starting constraint solving ---
[Saturating Sources] Step 1 (Max 5)
[Saturating Sources] Done
The constraint system contains the following annotated nodes
#i2
```
