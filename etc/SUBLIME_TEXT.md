TamarinAssist for Sublime Text 3
===

*Please be aware that TamarinAssist is still under active development and as such, several of the features are still implemented in a prototypical manner.*
*If you experience any problems or have any questions on running any parts of the plug-in please [visit the project GitHub page](https://github.com/lordqwerty/TamarinAssist/).

Introduction
---

This is a [Sublime Text 3](https://www.sublimetext.com/3) plug-in which adds
support for [Tamarin] Security Protocol Theories (`spthy`):

+ Syntax Highlighting
+ Autocompletion (Snippets)
+ Run Tamarin functions within Sublime

Tamarin function commands are accessed via `CTRL + SHIFT + P` then
type "*Tamarin*" to see the options available.

Features
---

- [X] Basic Syntaxes
- [X] Run Tamarin within Sublime
- [X] Snippets for Theory, Rule, Axiom and Lemma
- [X] Add package to [PackageControl.io]

See the [screenshots](https://github.com/lordqwerty/TamarinAssist/blob/master/docs/SCREENSHOTS.md) demonstrating the plugins ability.

Install via Package Control
---

[PackageControl.io: TamarinAssist](https://packagecontrol.io/packages/TamarinAssist) can now be installed via the sublime package manager. See the
[install](https://packagecontrol.io/installation) and [usage](https://packagecontrol.io/docs/usage) documentation, then search and install TamarinAssist.

Manual Install
---

For Linux / OS X this process can be followed. We assume you have
the `git` tool installed.

1. Change Directory to Sublime Text packages directory:
    + Mac OS X: `cd ~/Library/Application\ Support/Sublime\ Text\ 3/Packages/`
    + Linux: `~/.Sublime\ Text\ 3/Packages/`

2. Pull directory into Packages folder.
    + SSH: `git pull git@github.com:lordqwerty/TamarinAssist.git`
    + HTTPS: `https://github.com/lordqwerty/TamarinAssist.git`

3. Open Sublime and bottom right syntaxes Tamarin should be in the list.

Please check back to see what changes have been made so you can perform a
`git pull`.



[Tamarin]:http://www.infsec.ethz.ch/research/software/tamarin.html
[PackageControl.io]:https://packagecontrol.io/