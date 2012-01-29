CABAL_OPTS=

# NOTE that the dependency solver of cabal-install-0.10.2 has sometimes
# trouble coping with complicated install plans. In these cases, the
# development version version of 'cabal-install' available from
#
#   darcs get http://darcs.haskell.org/cabal-install/
#
# allows you to use a better solver which is activated using the following
# flag.
#
# CABAL_OPTS=--solver=modular
#

# This is the only target that an end-user will use
install:
	cabal install $(CABAL_OPTS) lib/utils lib/term ./

# In case some dependencies cannot be resolved and should be forced use this
# target. NOTE that this may break other libraries installed on your system.
force-install:
	cabal install $(CABAL_OPTS) --force-reinstalls lib/utils lib/term ./
#
#
# ###########################################################################
# NOTE the remainder makefile is FOR DEVELOPERS ONLY.
# It is by no means official in any form and should be IGNORED :-)
# ###########################################################################
#
#
#



# requires the cabal-dev tool. Install it using the 'cabal-dev'
dev-install:
	cabal-dev configure && cabal-dev build
	
dev-run:
	./dist/build/tamarin-prover/tamarin-prover interactive examples/TPM

# TODO: Implement 'dev-clean' target

cabal-dev:
	cabal-dev add-source lib/utils
	cabal-dev add-source lib/term
	# force install with 'native' flag of blaze-textual
	cabal-dev install blaze-textual -fnative --reinstall

###############################################################################
## Developer specific targets (some out of date)
###############################################################################


JKL1=data/examples/JKL_TS1_2004.spthy data/examples/JKL_TS1_2008.spthy data/examples/JKL_TS1_2008-KIFS.spthy
JKL2=data/examples/JKL_TS2_2004.spthy data/examples/JKL_TS2_2008.spthy data/examples/JKL_TS2_2004-KIFS.spthy data/examples/JKL_TS2_2008-KIFS.spthy

KEA=data/examples/KEA_plus.spthy data/examples/KEA_plus_KCI.spthy data/examples/KEA_plus_wPFS.spthy data/examples/KEA_plus_KCI_wPFS.spthy

NAXOS=data/examples/NAXOS_broken_eCK_variant.spthy data/examples/NAXOS_eCK_PFS.spthy data/examples/NAXOS_eCK.spthy 
NAXOS_SIMPLIFIED=data/examples/NAXOS_PFS_initiator_simplified.spthy 

UM=data/examples/UM_eCK_noKCI.spthy data/examples/UM_eCK.spthy data/examples/UM_wPFS.spthy

SDH=data/examples/SignedDH.spthy data/examples/SignedDH_eCK.spthy

STS=data/examples/STS.spthy data/examples/STS-mod.spthy


CASE_STUDIES=$(JKL1) $(JKL2) $(KEA) $(NAXOS) $(UM) $(NAXOS_SIMPLIFIED) $(STS) $(SDH)

# case studies
case-studies:	$(CASE_STUDIES)
	mkdir -p case-studies
	tamarin-prover $(CASE_STUDIES) --prove --stop-on-attack=dfs -Ocase-studies | tee casestudies.txt


# outdated targets

all: unit mult psearch

web:
	ghc --make Main -c -isrc -Wall -iinteractive-only-src
	runghc -isrc -Wall -iinteractive-only-src Main interactive examples --autosave --loadstate --debug

webc: comp
	./tamarin-prover interactive --autosave --loadstate --debug --datadir=data/ examples/

comp:
	ghc --make Main -isrc -iinteractive-only-src/ -o tamarin-prover

opt:
	ghc -fforce-recomp -isrc -main-is Narrow.main --make -O2 -Wall -o narrow src/Narrow.hs

assert:
	ghc -fforce-recomp -isrc -main-is Narrow.main --make -Wall -o narrow src/Narrow.hs

mult: assert
	time ./narrow variants "x1*x2"


scyther:
	cabal install --flags="-build-library -build-tests build-scyther"

unit:
	cabal install --flags="-build-library build-tests -build-scyther"
	-rm scyther-ac-unit-tests.tix
	scyther-ac-unit-tests

coverage:
	ghc -fhpc -fforce-recomp -main-is Term.UnitTests.main --make -Wall -o unit -ilib/term/src Term.UnitTests
	-rm unit.tix
	./unit
	hpc markup unit --destdir coverage
	open coverage/hpc_index.html
	hpc report unit

prof:
	ghc -fforce-recomp -main-is Narrow.main --make -prof -auto-all -Wall -o narrow -isrc src/Narrow.hs

proofa:
	ghc -fforce-recomp -main-is ProofAssistant.main --make -Wall -o proofa -isrc src/ProofAssistant.hs

haddock:
	cabal haddock --executables

depgraph:
	find . -name \*hs | grep -v Old | xargs graphmod -q | tred | dot -odepGraph.svg -Tsvg

ctags:
	ghc -e :ctags src/Main.hs

.PHONY: unit opt all mult coverage proofa haddock case-studies
