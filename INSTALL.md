Installing tamarin-prover
===

Table of Contents
---

* [Pre-requisites](#pre-requisites)
* [Tamarin Prover](#tamarin-prover)
* [Limitations on Windows](#limitations-on-Windows)
* [Installation](#installation)
  + [Linux](#linux)
  + [MacOS X](#macos-x)


Pre-requisites
---

Maude, available at http://maude.cs.illinois.edu/
(version 2.6 and 2.7 work).

GraphViz, available at http://www.graphviz.org/ or through your system's package manager.


Tamarin-prover
---

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
---

To the best of our knowledge, there is no current GraphViz version
available for Windows, so only the command-line parts of the tool are
functional there.


Installation
---

### Linux


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

5. Test the install by running the following in your terminal

  ```
    ~/.local/bin/tamarin-prover test
  ```

The `tamarin-prover` executable will be installed in `~/.local/bin/tamarin-prover`.

Starting 'tamarin-prover' without arguments will output its help message,
including the paths to the installed example protocol models and the
case studies from our papers. We recommend opening the [Tutorial.spthy]
example file in a text editor and start exploring from there.

Happy proving :smile:


### MacOS X

1. Install Command Line tools if you have not already. Open a terminal and enter
   the following: `xcode-select --install`. From the popup press the "Install"
   button and wait for it to install.

2. Use your package manager ([MacPorts] or [Homebrew]) to install maude and graphviz. For [MacPorts]:

   ```
     sudo port install maude graphviz
   ```

  *Please follow instructions to also install Haskell 'stack' tool, if using MacPorts.*

  For [Homebrew]:

   ```
     brew install homebrew/science/maude graphviz haskell-stack
   ```

  Alternatively, download and install both by following the instructions at their respective websites.

  For Maude you can download core Maude 2.7 from:
  http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation

  For GraphViz you can download it from:
  http://www.graphviz.org/Download.php

  For Haskell tool 'stack' can download it from:
  https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#manual-download-1

3. Clone the `tamarin-prover` repository

   ```
     git clone https://github.com/tamarin-prover/tamarin-prover.git
   ```

4. Build the tamarin-prover

   ```
     make default
   ```

   The installation process lets you know where the `tamarin-prover` executable will be installed in.

5. Test the install by running the following in your terminal

  ```
    ~/.local/bin/tamarin-prover test
  ```

Starting `tamarin-prover` without arguments will output its help message,
including the paths to the installed example protocol models and the
case studies from our papers. We recommend opening the [Tutorial.spthy]
example file in a text editor and start exploring from there.

Happy proving :smile:


[MacPorts]: https://www.macports.org/
[Homebrew]: http://brew.sh/
[Tutorial.spthy]: examples/Tutorial.spthy