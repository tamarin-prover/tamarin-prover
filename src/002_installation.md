Installation {#sec:installation}
============


We explain below how to install Tamarin on different operating systems:
[Linux](#sec:linux),  [Mac
OS X](#sec:macosx), and [Microsoft Windows](#sec:windows). 

Linux {#sec:linux}
-----

For Tamarin to run on Linux\index{Linux}, a number of dependencies
must be installed, namely GraphViz and Maude 2.7. You can install
GraphViz using your standard package manager or directly from
<http://www.graphviz.org/>. You can also
install Maude using your
package manager.  However, if your package manager installs Maude 2.6,
then you must install version 2.7, [Core Maude
2.7](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation#Core_Maude_2.7),
directly from <http://maude.cs.illinois.edu/>.
In this case, you should ensure 
that your *PATH* includes the install path, so that
calling `maude` starts version 2.7. Note that even though the Maude
executable is movable, the `prelude.maude` file must be in the same
folder that you start Maude from.

Once these dependencies have been installed, you can then either compile
Tamarin from source, or download the binaries of the latest master
version. Development versions require compilation from source.

### Compiling from source ###

To help compile Tamarin from source, we manage Haskell dependencies
automatically using the tool `stack`. You must first install
`stack`, following the instructions given at
[Stack's install page](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md).

After running `git clone` of the Tamarin
repository you have the current development version ready for
compilation. If you would prefer to use the master version, just run
`git checkout master`. In either case, you can then run `make
default`, which will install an appropriate GHC (the Glasgow Haskell Compiler)
for your system,
including all dependencies, and the `tamarin-prover` executable
will be copied to `~/.local/bin/tamarin-prover`.
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

### Installing the pre-built Tamarin binary {#sec:MacOSBinInstall}

To run Tamarin on Mac OS X you need to have Maude 2.7 and GraphViz. 

1.  Download and install Maude 2.7 from
  <http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation>

2.  Download and install GraphViz from 
<http://www.graphviz.org/Download.php>

3.  Download the Tamarin binary `tamarin-prover-1.x.y-macosx` from 
<https://github.com/tamarin-prover/bin-dists>

**Note:** 

  * Only the current master is available as binary, while the sources
contain both the master and the current development state.

  * The Tamarin source archive 
<https://github.com/tamarin-prover/tamarin-prover/archive/develop.zip>
contains numerous protocol examples and the `Tutorial.spthy` file that this manual refers to. 

Continue with Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.

### Installing Tamarin from sources ###

1. To compile Tamarin you need the Haskell tool [stack](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#manual-download-1)
and to run Tamarin you need to have [Maude 2.7](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation) and [GraphViz](http://www.graphviz.org/Download.php). 
You can download these tools from their respective sites *or* use one of the package managers 'MacPorts' or 'Homebrew'. 

  *  For 'MacPorts':
```
  sudo port install maude graphviz
```

The Haskell tool `stack` is not in the MacPorts repository and must be installed by following the instructions at 
  <https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md>

  *   For 'Homebrew':
```
  brew install homebrew/science/maude graphviz haskell-stack
```


2. Clone the `tamarin-prover` repository by typing
```
  git clone https://github.com/tamarin-prover/tamarin-prover.git
```
or download the source files from 
  <https://github.com/tamarin-prover/tamarin-prover/archive/develop.zip>


3. Build Tamarin by changing to the `tamarin-prover` directory and 
   typing
```
  make default
```

   The installation process lets you know where the `tamarin-prover`
   executable will be installed in, e.g., in `~/.local/bin/`. Move the
   binary to a directory in your executables path or add
   `~/.local/bin/` to your path.

Continue with Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.


Windows {#sec:windows}
-------

Windows is not supported at the moment. 

To the best of our knowledge, there is no current GraphViz version
available for Windows and there is no Maude binary for Windows 10. 
Therefore only the command-line parts of the tool are
functional for Windows systems prior to Windows 10.


Running Tamarin {#sec:running-tamarin}
---------------

Starting `tamarin-prover` without arguments will output its
help message, including the paths to the installed example protocol
models and all case studies from published papers. We recommend
opening the [Tutorial.spthy](https://github.com/tamarin-prover/tamarin-prover/tree/develop/examples/Tutorial.spthy) example file in a text editor and start
exploring from there, or to continue reading this document.
**Note:** The `Tutorial.spthy` file can be found in the `examples` directory of the Tamarin source.

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

Running Tamarin on a remote machine
---------------------------------

If you have access to a faster desktop or server, but prefer using
Tamarin on your laptop, you can do that. The cpu/memory intensive
reasoning part of the tool will run on the faster machine, while you
only run the GUI, i.e., the web browser of your choice, locally. To do
this, you forward your port 3001 to the port 3001 of your server
with the following command, replacing ```SERVERNAME``` appropriately.

```
ssh -L 3001:localhost:3001 SERVERNAME
```

If you do this, we recommend that you run your Tamarin instance on
the server in a [screen](https://www.gnu.org/software/screen/manual/screen.html) environment, which will continue
running even if the network drops your connection as you can later
reconnect to it. Otherwise, any network failure may require you to
restart Tamarin and start over on the proof.
