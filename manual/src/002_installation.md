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
default`, which will install an appropriate GHC for your system,
including all dependencies, and the `tamarin-prover` executable
will be copied to
`~/.local/bin/tamarin-prover`
Note that this process will take between 30 and 60 minutes, as all
dependencies (roughly 120) are compiled from scratch. If you later pull a newer
version of Tamarin (or switch to/from the `master` branch), then only
the tool itself needs to be recompiled, which takes a few minutes at
most.

Continue with Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.

### Using binaries ###

You can download the binaries appropriate for your system from
<https://github.com/tamarin-prover/bin-dists>

Only the current master is available as binary, while the sources
contain both the master and the current development state.

Similarly to installing from source, now starting
Tamarin without arguments will output its help
message, including the paths to the installed example protocol models
and all case studies from published papers. We recommend opening the
`Tutorial.spthy` example file in a text editor and start exploring from
there, or to continue reading this document.

Continue with Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.


Mac OS X {#sec:macosx}
--------

MacOS X instructions \index{MacOS X}



Windows {#sec:windows}
-------

Windows is not supported at the moment. 




Running Tamarin {#sec:running-tamarin}
---------------

Starting ```tamarin-prover``` without arguments will output its
help message, including the paths to the installed example protocol
models and all case studies from published papers. We recommend
opening the Tutorial.spthy example file in a text editor and start
exploring from there, or to continue reading this document.

Running ```tamarin-prover test``` will check the Maude and GraphViz
versions and run some tests, its output should be:

```
$ tamarin-prover test
Self-testing the tamarin-prover installation.

*** Testing the availability of the required tools ***
maude tool: 'maude'
 checking version: 2.7. OK.
 checking installation: OK.

GraphViz tool: 'dot'
 checking version: dot - graphviz version 2.39.20150613.2112 
                   (20150613.2112). OK.

*** Testing the unification infrastructure ***
Cases: 55  Tried: 55  Errors: 0  Failures: 0

*** TEST SUMMARY ***
All tests successful.
The tamarin-prover should work as intended.

           :-) happy proving (-:
```

You are now ready to use the \tamarin for verification of cryptographic protocols.

Running Tamarin on remote machine
---------------------------------

If you have access to a faster desktop or server, but prefer using
Tamarin on your laptop, you can do that. The cpu/memory intensive
reasoning part of the tool will run on the bigger machine, while you
only run the GUI, i.e., the web browser of your choice, locally. To do
this, you can forward your port 3001 to the port 3001 of your server
(replace ```SERVERNAME``` appropriately) with the following
command:

```
ssh -L 3001:localhost:3001 SERVERNAME
```

If you do this, we recommend that you run your Tamarin instance on
the server inside a ```screen``` instance, which will continue
running even if the network drops your connection as you can later
reconnect to it. Otherwise, any network failure may require you to
restart Tamarin and start over on the proof.
