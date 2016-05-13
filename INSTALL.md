Installing tamarin-prover
-------------------------

Pre-requisites
--------------

Maude, available at http://maude.cs.illinois.edu/
(version 2.6 and 2.7 work).

GraphViz, available at http://www.graphviz.org/ or through your system's package manager.


Tamarin-prover
--------------

You can download the binaries appropriate for your system from
https://github.com/tamarin-prover/bin-dists

You can also compile tamarin-prover from source.  We manage the
Haskell dependencies automatically, using 'stack'. First install
'stack' according to
https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

After cloning the tamarin-prover repository run 'make default', which
will install an appropriate GHC for your system, including all
dependencies, and the tamarin-prover executable will be copied to

```
  ~/.local/bin/tamarin-prover
```

Limitations on Windows
----------------------

To the best of our knowledge, there is no current GraphViz version
available for Windows, so only the command-line parts of the tool are
functional there.


Detailed instructions for Linux - from source
---------------------------------------------

1. Use your package manager to install maude and graphviz:

   ```
     sudo apt-get install maude graphviz
   ```

2. Install the Haskell tool `stack` by following the instructions at 
   https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

3. Clone the `tamarin-prover` repository

   ```
     git clone https://github.com/tamarin-prover/tamarin-prover.git
   ```

4. Build the tamarin-prover

   ```
     make default
   ```
   
   The `tamarin-prover` executable will be installed in `~/.local/bin/tamarin-prover`.

   Starting 'tamarin-prover' without arguments will output its help message,
   including the paths to the installed example protocol models and the
   case studies from our papers. We recommend opening the `Tutorial.spthy`
   example file in a text editor and start exploring from there. 

   Happy proving :-)


Detailed instructions for MacOS X - from source
---------------------------------------------

1. Use your package manager (MacPorts or Homebrew) to install maude and graphviz. For MacPorts:

   ```
     sudo port install maude graphviz
   ```

  For Homebrew:

   ```
     brew install maude graphviz
   ```

  Alternatively, download and install both by following the instructions at their respective websites.

  For Maude you can download core Maude 2.7 from:
  http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation

  For GraphViz you can download it from:
  http://www.graphviz.org/Download.php

2. Install the Haskell tool `stack` by following the instructions at 
   https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

3. Clone the `tamarin-prover` repository

   ```
     git clone https://github.com/tamarin-prover/tamarin-prover.git
   ```

4. Build the tamarin-prover

   ```
     make default
   ```

   The installation process lets you know where the `tamarin-prover` executable will be installed in.
   
   Starting 'tamarin-prover' without arguments will output its help message,
   including the paths to the installed example protocol models and the
   case studies from our papers. We recommend opening the `Tutorial.spthy`
   example file in a text editor and start exploring from there. 

   Happy proving :-)
