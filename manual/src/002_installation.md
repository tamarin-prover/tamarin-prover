
Installation {#sec:installation}
============


We explain below how to install Tamarin on different operating systems:
[Linux](#sec:linux),  [Mac
OS X](#sec:macosx), and [Microsoft Windows](#sec:windows).

Linux {#sec:linux}
-----

### Compiling from source {#sec:LinuxSrcInstall}

To run Tamarin on Linux\index{Linux}, a number of dependencies
must be installed, namely GraphViz and Maude 2.7. You can install
GraphViz using your standard package manager or directly from
<http://www.graphviz.org/>. You can also
install Maude using your
package manager.  However, if your package manager installs Maude 2.6,
then you must install version 2.7.1, [Core Maude
2.7.1](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation#Core_Maude_2.7.1),
directly from <http://maude.cs.illinois.edu/>.
In this case, you should ensure
that your `PATH` includes the install path, so that
calling `maude` starts version 2.7.1. Note that even though the Maude
executable is movable, the `prelude.maude` file must be in the same
folder that you start Maude from.

Once these dependencies have been installed, you can then compile
Tamarin from source, using either the stable master or current development version.

To help compile Tamarin from source, we manage Haskell dependencies
automatically using the tool `stack`. You must first install
`stack`, following the instructions given at
[Stack's install page](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md). In case you are installing `stack` with your package manager (particularly on Ubuntu), you must run `stack upgrade` afterwards, as that version of stack is usually out-of-date.

After running `git clone` on the Tamarin
repository, you have the current development version ready for
compilation. If you would prefer to use the master version, just run
`git checkout master`. In either case, you can then run `make
default`, which will install an appropriate GHC (the Glasgow Haskell Compiler)
for your system,
including all dependencies, and the `tamarin-prover` executable
will be copied to `~/.local/bin/tamarin-prover`.
Note that this process will take between 30 and 60 minutes, as all
dependencies (roughly 120) are compiled from scratch. If you later pull a newer
version of Tamarin (or switch to/from the `master` branch), then only
the tool itself needs to be recompiled, which takes a few minutes, at most.

Continue as described in Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.


### Automatic Installation of Tamarin {#sec:LinuxBinInstall}

The fastest way to install Tamarin on Linux is to use [Linuxbrew](http://linuxbrew.sh/). Linuxbrew is a fork of Homebrew, the Mac OS package manager,
for Linux.

To install Linuxbrew follow the [Installation Instructions](https://github.com/Linuxbrew/brew#install-linuxbrew-tldr).

If you already have this installed, it is as simple as running the following two commands in your terminal:

  * `brew update`
  * `brew install homebrew/science/tamarin-prover`

You can now run Tamarin from the command line by typing `tamarin-prover`.
Continue as described in Section [Running Tamarin](#sec:running-tamarin) to
run Tamarin for the first time.


### Automatic Installation for Arch Linux {#sec:ArchLinuxBinInstall}

There is a package in the official repositories. To install it, simply type:

  * `pacman -S tamarin-prover`

### Automatic Installation for Nix/NixOS {#sec:NixBinInstall}

There is a package in the official Nixpkgs repository. To install it, simply type:

  * `nix-env -i tamarin-prover`

This installs a per-user copy of Tamarin. If you're on NixOS, just add `tamarin-prover` to your
`environment.systemPackages` for system-wide installation.

Mac OS X {#sec:macosx}
--------

### Automatic Installation of Tamarin {#sec:MacOSBinInstall}

The fastest way to install Tamarin on Mac OS X is to use [Homebrew](http://brew.sh/).

If you already have this installed, it is as simple as running the following two commands in your terminal:

  * `brew update`
  * `brew tap brewsci/science`
  * `brew install tamarin-prover`

You can now run Tamarin from the command line by typing `tamarin-prover`.
Continue as described in Section [Running Tamarin](#sec:running-tamarin) to
run Tamarin for the first time.

Please note, if you previously used homebrew to install Tamarin from homebrew-science, you will have to
uninstall and untap:

  * `brew uninstall tamarin-prover`
  * `brew untap homebrew/science`

Once complete run the above instructions.

#### Installing Homebrew
If you don't have Homebrew installed:

1. Install [Homebrew](http://brew.sh/), by following the instructions on their
website (this is a one-line copy paste install). Update everything with: `brew update`.
Any issues, run `brew doctor` for more information.

2. Install Tamarin: `brew install homebrew/science/tamarin-prover`
    * This should just work. If for any reason this doesn't work, you might have to 'tap' (add) Homebrew
    [Science](https://github.com/Homebrew/homebrew-science/blob/master/README.md) manually. 
    This is currently achieved by `brew tap homebrew/science`, but could change. 
    Check [the website](https://github.com/Homebrew/homebrew-science/blob/master/README.md) 
    for the latest instructions.
    * Tamarin's dependencies Maude and GraphViz are automatically installed
    and added to your path.

3. You can now run Tamarin from the terminal by typing `tamarin-prover`

That's it! Homebrew will automatically update Tamarin when new versions are
released, if you `brew update && brew upgrade` on a semi-regular basis.

For reference, Homebrew will place a symlink to the binary in
`/usr/local/bin/tamarin-prover`, but you should never need to touch this.
To uninstall, just `brew remove tamarin-prover`, and if you want, also
remove `maude` and `graphviz`, two dependencies which are automatically
installed with Tamarin.

If you want to install Tamarin from source (through Homebrew), simply use: 
`brew install --build-from-source homebrew/science/tamarin-prover`.


### Installing Tamarin from sources ###

1. To compile Tamarin, you need the Haskell tool [stack](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md#manual-download-1).
To run Tamarin you need [Maude 2.7](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation) and [GraphViz](http://www.graphviz.org/Download.php).
You can download these tools from their respective sites.
Alternatively, you can use either the
[MacPorts](https://www.macports.org) or
[Homebrew](http://brew.sh)
package managers.

  *  For MacPorts:
```
  sudo port install maude graphviz
```

The Haskell tool `stack` is not in the MacPorts repository and must be installed by following the instructions at
  <https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md>.

  *   For Homebrew:
```
  brew install homebrew/science/maude graphviz haskell-stack
```


2. Clone the `tamarin-prover` repository by typing
```
  git clone https://github.com/tamarin-prover/tamarin-prover.git
```
or download the source files from
  <https://github.com/tamarin-prover/tamarin-prover/archive/develop.zip>.


3. Build Tamarin by changing into the `tamarin-prover` directory and
   typing
```
  make default
```

   The installation process informs you where the `tamarin-prover`
   executable will be installed, for example, in `~/.local/bin/`. Move the
   binary to a directory in your executables path or add
   `~/.local/bin/` to your path.

Continue as described in Section [Running Tamarin](#sec:running-tamarin) to run Tamarin for the first time.


Windows {#sec:windows}
-------

Windows is not currently supported.
To the best of our knowledge, there is not a current GraphViz version
available for Windows and there is no Maude binary for Windows 10.
Therefore only the command-line parts of the tool are
functional for Windows systems prior to Windows 10.


Running Tamarin {#sec:running-tamarin}
---------------

Starting `tamarin-prover` without arguments will output its help
message, including the paths to the installed example protocol models
and all case studies from published papers. We recommend opening the
[Tutorial.spthy](https://raw.githubusercontent.com/tamarin-prover/tamarin-prover/develop/examples/Tutorial.spthy)
example file in a text editor and start exploring from there, or to
continue reading this document.  Note that the `Tutorial.spthy` file
can be found in the `examples` directory of the Tamarin source.

Running ```tamarin-prover test``` will check the Maude and GraphViz
versions and run some tests. Its output should be:

```
$ tamarin-prover test
Self-testing the tamarin-prover installation.

*** Testing the availability of the required tools ***
maude tool: 'maude'
 checking version: 2.7.1. OK.
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

You are now ready to use Tamarin to verify cryptographic protocols.

Running Tamarin on a remote machine
---------------------------------

If you have access to a faster desktop or server, but prefer using
Tamarin on your laptop, you can do that. The cpu/memory intensive
reasoning part of the tool will then run on the faster machine, while you
just run the GUI locally, i.e., the web browser of your choice. To do
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

Tamarin Code Editors
--------------------

Under the [etc](https://github.com/tamarin-prover/tamarin-prover/tree/develop/etc) folder contained in the Tamarin Prover project, plug-ins are available for VIM, Sublime Text 3 and Notepad++. Below we details the steps required to install your preferred plug-in.

### VIM ###

1. Create `~/.vim/` directory if not already existing, which is the typical location for `$VIMRUNTIME`
2. Change directory to `~/.vim/`
3. Place the [filetype.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/filetype.vim) file
4. Create another directory `syntax` within `~/.vim/` directory and change directory to it.
5. Place the [spthy.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/spthy.vim) and [sapic.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/sapic.vim) files in `~/.vim/syntax`

### Sublime Text 3 ###

[TamarinAssist](http://jwhitefield.co.uk/TamarinAssist/) is a plug-in developed for the Sublime Text 3 editor. The plug-in has the following functionality:
- Basic Syntaxes
- Run Tamarin within Sublime
- Snippets for Theory, Rule, Axiom and Lemma

TamarinAssist can be install in two ways:

The first and preferred method is with [PackageControl.io](https://packagecontrol.io/). TamarinAssist can now be installed via the sublime package manager. See the [install](https://packagecontrol.io/installation) and [usage](https://packagecontrol.io/docs/usage) documentation, then search and install TamarinAssist.

Alternatively it can be installed from source. For Linux / OS X this process can be followed. We assume you have
the `git` tool installed.

1. Change Directory to Sublime Text packages directory:
    + Mac OS X: `cd ~/Library/Application\ Support/Sublime\ Text\ 3/Packages/`
    + Linux: `~/.Sublime\ Text\ 3/Packages/`

2. Pull directory into Packages folder.
    + SSH: `git pull git@github.com:lordqwerty/TamarinAssist.git`
    + HTTPS: `https://github.com/lordqwerty/TamarinAssist.git`

3. Open Sublime and bottom right syntaxes 'Tamarin' should be in the list.

*Please be aware that TamarinAssist is still under active development and as such, several of the features are still implemented in a prototypical manner. If you experience any problems or have any questions on running any parts of the plug-in please [visit the project GitHub page](https://github.com/lordqwerty/TamarinAssist/).*

### Notepad++ ###

Follow steps from the [Notepad++ Wiki](http://docs.notepad-plus-plus.org/index.php/User_Defined_Language_Files#How_to_install_user_defined_language_files) using the [notepad_plus_plus_spthy.xml](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/notepad_plus_plus_spthy.xml) file.
