Installation {#sec:installation}
============


We explain how to install Tamarin for each operating system. Refer to
the Linux instructions in Section on [Linux](#sec:linux), the Mac OS X
instructions in the section on [Mac OS X](#sec:macosx), and the Windows instructions
in the section on [Windows](#sec:windows).

Linux {#sec:linux}
-----

For Tamarin to run on Linux\index{Linux}, a number of dependencies
must be installed, namely GraphViz and Maude 2.7. You can install
GraphViz through your regular package manager, or from
<http://www.graphviz.org/>. Similarly you can install Maude using your
package manager, but if that installs Maude 2.6 you need to go to
<http://maude.cs.illinois.edu/> to install version 2.7, [Core Maude
2.7](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation#Core_Maude_2.7),
and make sure that the install path is in your path variable, so that
calling `maude` starts version 2.7. Note that even though the maude
executable is movable, the `prelude.maude` file must be in the same
folder you start Maude from.

With these dependencies available, you can then either compile
Tamarin from source, or download the binaries of the latest master
version. Development versions require compilation from source.

### Compiling from source ###

To help compile Tamarin from source we manage Haskell dependencies
automatically, using the tool `stack`. First you must install
`stack` according to
[Stack's install page](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md)

After running `git clone` of the Tamarin
repository you have the current development version ready for
compilation. If you rather want to use the master version just run
`git checkout master`. In either case, you can then run `make
default', which will install an appropriate GHC for your system,
including all dependencies, and the `tamarin-prover` executable
will be copied to
`~/.local/bin/tamarin-prover`
Note that this process will take between 30 and 60 minutes, as all
dependencies (roughly 120) are compiled from scratch. If you later pull a newer
version of Tamarin (or switch to/from the `master` branch), then only
the tool itself needs to be recompiled, which takes a few minutes at
most.

