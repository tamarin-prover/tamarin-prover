
Installation {#sec:installation}
============

The easiest way to install Tamarin on Mac or Linux is to use
[Homebrew](http://brew.sh/)/[Linuxbrew](https://github.com/Linuxbrew/brew#install-linuxbrew):

  * `brew install tamarin-prover/tap/tamarin-prover`

It's separately packaged for

  - Arch Linux: `pacman -S tamarin-prover`
  - Nixpkgs: `nix-env -i tamarin-prover`
  - NixOS: add `tamarin-prover` to your `environment.systemPackages`.

You can also [download binaries directly from GitHub](https://github.com/tamarin-prover/tamarin-prover/releases)
and manually install dependencies yourself (see below).
  
## Compiling from source {#sec:LinuxSrcInstall}

You don't need to compile Tamarin from source unless you are developing a new feature for it or you
want to use an unreleased feature. However, if you do want to install it from source:

### Manually install dependencies

Tamarin requires Haskell Stack to build and GraphViz and Maude 2.7 to run. The easiest way to
install these is

```
brew install tamarin-prover/tap/maude graphviz haskell-stack
```

Alternatively, you can install them yourself:

  - **Haskell Stack** Follow the instructions given at [Stack's install
    page](https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md). If you
    are installing `stack` with your package manager (particularly on Ubuntu), you must run `stack
    upgrade` afterwards, as that version of stack is usually out-of-date.

  - **Graphviz** Graphviz should be available using your standard package manager, or directly from
    <http://www.graphviz.org/>

  - **Maude** You can install Maude using your package manager. However, if your package manager
    installs Maude 2.6, then you must install version 2.7.1, [Core Maude
    2.7.1](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation#Core_Maude_2.7.1),
    directly from <http://maude.cs.illinois.edu/>.  In this case, you should ensure that your `PATH`
    includes the install path, so that calling `maude` starts version 2.7.1. Note that even though
    the Maude executable is movable, the `prelude.maude` file must be in the same folder that you
    start Maude from.

### Compile

Check out the source code with

```
git clone https://github.com/tamarin-prover/tamarin-prover.git
```

and you have the current development version ready for compilation. If you would prefer to use the
master version, just run `git checkout master`.

In either case, you can then run `make default` in the new directory, which will install an
appropriate GHC (the Glasgow Haskell Compiler) for your system, including all dependencies. The
`tamarin-prover` executable will be copied to `~/.local/bin/tamarin-prover`. Note that this process
will take between 30 and 60 minutes, as all dependencies (roughly 120) are compiled from scratch. If
you later pull a newer version of Tamarin (or switch to/from the `master` branch), then only the
tool itself needs to be recompiled, which takes a few minutes, at most.

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

Under the [etc](https://github.com/tamarin-prover/tamarin-prover/tree/develop/etc) folder contained
in the Tamarin Prover project, plug-ins are available for VIM, Sublime Text 3, Emacs and
Notepad++. Below we details the steps required to install your preferred plug-in.

#### VIM

1. Create `~/.vim/` directory if not already existing, which is the typical location for `$VIMRUNTIME`
2. Change directory to `~/.vim/`
3. Place the [filetype.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/filetype.vim) file
4. Create another directory `syntax` within `~/.vim/` directory and change directory to it.
5. Place the [spthy.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/spthy.vim) and [sapic.vim](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/sapic.vim) files in `~/.vim/syntax`

#### Sublime Text 3

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

#### Notepad++

Follow steps from the [Notepad++ Wiki](http://docs.notepad-plus-plus.org/index.php/User_Defined_Language_Files#How_to_install_user_defined_language_files) using the [notepad_plus_plus_spthy.xml](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/notepad_plus_plus_spthy.xml) file.

#### Emacs

The [spthy.el](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/spthy.el)
implements a SPTHY major mode. You can load it with `M-x load-file`, or add it to your `.emacs` in
your favourite way.

FAQ
---

#### Why is Windows not supported?

To the best of our knowledge, there is not a current GraphViz version available for Windows and
there is no Maude binary for Windows 10. Therefore only the command-line parts of the tool are
functional anyway for Windows systems prior to Windows 10. Moreover, few users actually run Tamarin
on Windows.

#### How do I uninstall Tamarin using Homebrew?

To uninstall (and "untap" the Tamarin homebrew tap):

  * `brew uninstall tamarin-prover`
  * `brew untap tamarin-prover/tap`

#### What's with this `homebrew-science` tap?

Tamarin was previously distributed in the now-closed `homebrew-science` tap. If you have already
installed it through Homebrew, you may have to uninstall and untap that version first:

  * `brew uninstall tamarin-prover`
  * `brew untap homebrew/science`

