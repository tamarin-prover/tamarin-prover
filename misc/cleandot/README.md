Improving Tamarin's graph output
================================

The purpose of this program is to improve the readability of Tamarin's
graph output, similar to the way this is handled in recent versions of
the Scyther compromising adversaries version.

`tamarin-cleandot.py` 

Dependencies
------------

* `python`
* `pydot`
* `pyparsing`

In Ubuntu, the following should be sufficient to get things up and
running:

	sudo apt-get install python-pyparsing python-pydot

Installation
------------

Currently, we are installing this program by effectively locally
replacing `dot`. (There should be some discussion on how to handle this
in the official releases, because the additional dependencies introduced
are not so nice.)

 1. Make a softlink called `dot` to `tamarin-cleandot.py` in a local
    directory.
    For example, 
    `ln -s tamarin-cleandot.py ~/bin/dot`

 2. Add the local directory to your path in a shell. E.g.,
    `export PATH="$HOME/bin:$PATH"`

 3. Invoke Tamarin from the same shell, e.g.,
    `tamarin-prover interactive .`






