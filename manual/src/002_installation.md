
Installation {#sec:installation}
============

## Installation on macOS or Linux {#sec:maclinux}

The easiest way to install Tamarin on macOS or Linux is to use
[Homebrew](http://brew.sh/):

  * `brew install tamarin-prover/tap/tamarin-prover`

It's separately packaged for

  - Arch Linux: `pacman -S tamarin-prover`
  - Nixpkgs: `nix-env -i tamarin-prover`
  - NixOS: add `tamarin-prover` to your `environment.systemPackages`.

You can also [download binaries directly from GitHub](https://github.com/tamarin-prover/tamarin-prover/releases)
and [manually install dependencies yourself](#sec:dependencies), or [compile from source](#sec:LinuxSrcInstall).

## Installation on Windows 10 {#sec:windows}

You can install Tamarin (with GUI) under Windows 10 using the [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/windows/wsl/install-win10).
For performance and compatibility reasons, we recommend using WSL2 with Ubuntu.
Once you have WSL and Ubuntu installed, start the Ubuntu app and install Tamarin following the [installation instructions for Linux](#sec:maclinux) above.
You can then run Tamarin inside the the Ubuntu app using the usual command.
To use the interactive mode, start Tamarin inside the app and connect your usual Windows-run browser to [http://127.0.0.1:3001](http://127.0.0.1:3001).
Your Windows files are accessible inside the Ubuntu app via, e.g., `/mnt/c` for files on drive `C:`.

## Compiling from source {#sec:LinuxSrcInstall}

You don't need to compile Tamarin from source unless you are developing a new feature for it or you
want to use an unreleased feature. However, if you do want to install it from source:

### Manually install dependencies {#sec:dependencies}

Tamarin requires Haskell Stack to build and GraphViz and Maude 2.7.1 (or newer) to run. The easiest way to
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

##### Using Vim plugin managers

This example will use [Vundle](https://github.com/VundleVim/Vundle.vim) to install the plugin directly
from this repository. The instructions below should be translatable to other plugin managers.

1. Make sure you installed Vundle (or your favorite plugin manager)
2. Put the below, or equivalent instructions, into your `.vimrc`:

```vimrc
Plugin 'tamarin-prover/editors'
```
3. Restart Vim or reload the configuration
4. Run the Vim command `:PluginInstall` (or equivalent)

You can install updates through `:PluginUpdate`.

##### Manual installation (not recommended)

If you install the Vim support files using this method, you will need to keep the files up-to-date yourself.

1. Create `~/.vim/` directory if not already existing, which is the typical location for `$VIMRUNTIME`
2. Copy the contents of `etc/vim` to `~/.vim/`, including the folders.

#### Sublime Text 3

[editor-sublime](https://github.com/tamarin-prover/editor-sublime) is a plug-in developed for the Sublime Text 3 editor. The plug-in has the following functionality:
- Basic Syntaxes
- Snippets for Theories, Rules, Restrictions and Lemmas

editor-sublime can be install in two ways:

The first and preferred method is with [PackageControl.io](https://packagecontrol.io/). editor-sublime can now be installed via the sublime package manager. See the [install](https://packagecontrol.io/installation) and [usage](https://packagecontrol.io/docs/usage) documentation, then search and install Tamarin​Prover.

Alternatively it can be installed from source. For Linux / macOS this process can be followed. We assume you have
the `git` tool installed.

1. Change Directory to Sublime Text packages directory:
    + macOS: `cd ~/Library/Application\ Support/Sublime\ Text\ 3/Packages/`
    + Linux: `cd ~/.config/sublime-text-3/Packages/`

2. Clone the directory into the Packages folder.
    + SSH: `git clone git@github.com:tamarin-prover/editor-sublime.git`
    + HTTPS: `git clone https://github.com/tamarin-prover/editor-sublime.git`

3. Close and re-open Sublime, and in the bottom right list of syntaxes 'Tamarin' should now be in the list.

*Please be aware that this plugin is under active development and as such, several of the features are still implemented in a prototypical manner. If you experience any problems or have any questions on running any parts of the plug-in please [visit the project GitHub page](https://github.com/tamarin-prover/editor-sublime).*

#### Notepad++

Follow steps from the [Notepad++ Wiki](http://docs.notepad-plus-plus.org/index.php/User_Defined_Language_Files#How_to_install_user_defined_language_files) using the [notepad_plus_plus_spthy.xml](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/notepad_plus_plus_spthy.xml) file.

#### Emacs

The [spthy.el](https://github.com/tamarin-prover/tamarin-prover/blob/develop/etc/spthy-mode.el)
implements a SPTHY major mode. You can load it with `M-x load-file`, or add it to your `.emacs` in
your favourite way.

#### Atom

The [language-tamarin](https://atom.io/packages/language-tamarin) package provides Tamarin syntax
highlighting for Atom. To install it, run `apm install language-tamarin`.

FAQ
---

#### How do I uninstall Tamarin using Homebrew?

To uninstall (and "untap" the Tamarin homebrew tap):

  * `brew uninstall tamarin-prover`
  * `brew untap tamarin-prover/tap`

#### What's with this `homebrew-science` tap?

Tamarin was previously distributed in the now-closed `homebrew-science` tap. If you have already
installed it through Homebrew, you may have to uninstall and untap that version first:

  * `brew uninstall tamarin-prover`
  * `brew untap homebrew/science`

#### After an update/pull/release Tamarin does not compile any more.

Try running `stack upgrade` and `stack update`. An out-of-date stack version can cause spurious
compilation errors.
