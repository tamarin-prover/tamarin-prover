#! /bin/bash
#
# Run GHCi with the cabal-dev package configuration. The actual package.conf
# directory in ./cabal-dev will have the compiler version suffixed. The
# command below therefore refers to a symlink that you have to create.

# ghci -no-user-package-conf -package-conf cabal-dev/packages.conf/ $*
ghci -no-user-package-conf -package-conf cabal-dev/packages.conf/ $*
