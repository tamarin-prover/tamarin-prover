#!/bin/bash

# to replace 1.3.0 by 1.2.3 execute with:
# ./version-change.sh "1\.3\.0" "1\.2\.3"

sed -i "s/$1/$2/g" \
Makefile \
tamarin-prover.cabal \
lib/term/tamarin-prover-term.cabal \
lib/theory/tamarin-prover-theory.cabal \
lib/utils/tamarin-prover-utils.cabal \
lib/sapic/tamarin-prover-sapic.cabal \
