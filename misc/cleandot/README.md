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

Usage
-----

Currently, we are connecting this program to Tamarin by effectively
replacing `dot`, by using Tamarin's `--with-dot` option.

For example,

    tamarin-prover interactive \
    --with-dot=/home/cas/src/tamarin-prover/misc/cleandot/tamarin-cleandot.py \
    ~/src/tamarin-prover/data/examples/csf12/

Note that the `tamarin-cleandot.py` must be in your executable path.
If `tamarin-prover` and `tamarin-cleandot.py` are in your executable
paths, the following wrapper script can be used:

    tamarin-prover-cleandot PROTOCOL_DIRECTORY

