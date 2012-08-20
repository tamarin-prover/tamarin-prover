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

force-install-ghc-7.0.4:
	cabal install -wghc-7.0.4 $(CABAL_OPTS) --force-reinstalls lib/utils lib/term ./

force-install-ghc-7.4.1:
	cabal install -wghc-7.4.1 $(CABAL_OPTS) --force-reinstalls lib/utils lib/term ./

#
#
# ###########################################################################
# NOTE the remainder makefile is FOR DEVELOPERS ONLY.
# It is by no means official in any form and should be IGNORED :-)
# ###########################################################################
#
#
#
VERSION=0.9.0.0

source-dists:
	cd lib/utils; cabal sdist
	cd lib/term; cabal sdist
	cabal sdist

source-dists-tests: source-dists
	mkdir -p /tmp/dist-test-$(VERSION)/
	cp lib/utils/dist/tamarin-prover-utils-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
	cp lib/term/dist/tamarin-prover-term-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
	cp dist/tamarin-prover-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
	cd /tmp/dist-test-$(VERSION)/; cabal install *.tar.gz

# For profiling, we use the cabal-dev tool and do not build the GUI. This
# simplifies installing all required libraries with profiling support enabled.
# The locally installed executable can then be called as follows
#
#   ./cabal-dev/bin/tamarin-prover +RTS -p -RTS
#
# to generate the profiling report
#
#   tamarin-prover.prof
#
# in the working directory.
profiling-install:
	cabal-dev install -fno-gui --force-reinstalls --enable-library-profiling --enable-executable-profiling ./lib/term ./lib/utils ./

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

cabal-clean:
	cd lib/utils; cabal clean
	cd lib/term; cabal clean
	cabal clean


###############################################################################
## Case Studies
###############################################################################


## CSF'12
#########

# These case studies are located in data/examples/ or examples/
DH2=DH2_original.spthy

KAS=KAS1.spthy KAS2_eCK.spthy KAS2_original.spthy

KEA=KEA_plus_KI_KCI.spthy KEA_plus_KI_KCI_wPFS.spthy

NAXOS=NAXOS_eCK_PFS.spthy NAXOS_eCK.spthy

SDH=SignedDH_PFS.spthy SignedDH_eCK.spthy

STS=STS_MAC.spthy STS_MAC_fix1.spthy STS_MAC_fix2.spthy

JKL1=JKL_TS1_2004_KI.spthy JKL_TS1_2008_KI.spthy
JKL2=JKL_TS2_2004_KI_wPFS.spthy JKL_TS2_2008_KI_wPFS.spthy
JKL3=JKL_TS3_2004_KI_wPFS.spthy JKL_TS3_2008_KI_wPFS.spthy

UM=UM_wPFS.spthy UM_PFS.spthy


TMPRES=case-studies/temp-analysis.spthy
TMPOUT=case-studies/temp-output.spthy

CSF12_CASE_STUDIES=$(JKL1) $(JKL2) $(KEA) $(NAXOS) $(UM) $(STS) $(SDH) $(KAS) $(DH2)
CSF12_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/csf12/,$(CSF12_CASE_STUDIES)))

# CSF'12 case studies
csf12-case-studies:	$(CSF12_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/csf12/*.spthy

# individual case studies
case-studies/%_analyzed.spthy:	data/examples/%.spthy
	mkdir -p case-studies/csf12
	mkdir -p case-studies/classic
	mkdir -p case-studies/loops
	mkdir -p case-studies/related_work/AIF_Moedersheim_CCS10
	mkdir -p case-studies/related_work/StatVerif_ARR_CSF11
	mkdir -p case-studies/related_work/TPM_DKRS_CSF11
	tamarin-prover $< --prove --stop-on-trace=dfs +RTS -N -RTS -o$(TMPRES) >$(TMPOUT)
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	echo "\n/* Output" >>$(TMPRES)
	cat $(TMPOUT) >>$(TMPRES)
	echo "*/" >>$(TMPRES)
	mv $(TMPRES) $@
	\rm -f $(TMPOUT)


## Inductive Strengthening
##########################

TPM=related_work/TPM_DKRS_CSF11/RunningExample.spthy
# Envelope.spthy (not yet working automatically)
STATVERIF=related_work/StatVerif_ARR_CSF11/StatVerif_Example1.spthy
# GM_Contract.spthy (not finished)
AIF=related_work/AIF_Moedersheim_CCS10/Keyserver.spthy
LOOPS=loops/TESLA_Scheme1.spthy loops/Minimal_KeyRenegotiation.spthy loops/Minimal_Create_Use_Destroy.spthy loops/RFID_Simple.spthy loops/Minimal_Create_Use_Destroy.spthy loops/Minimal_Crypto_API.spthy loops/Minimal_Loop_Example.spthy loops/JCS12_Typing_Example.spthy loops/Minimal_Typing_Example.spthy loops/Typing_and_Destructors.spthy
# TESLA_Scheme2.spthy (not finished)

IND_CASE_STUDIES=$(TPM) $(AIF) $(LOOPS) $(STATVERIF)
IND_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/,$(IND_CASE_STUDIES)))

# case studies
induction-case-studies:	$(IND_CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies/related_work/ case-studies/loops/


## Classical Protocols
######################


CLASSIC_CASE_STUDIES=TLS_Handshake.spthy NSLPK3.spthy NSLPK3_untagged.spthy

CLASSIC_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/classic/,$(CLASSIC_CASE_STUDIES)))

# case studies
classic-case-studies:	$(CLASSIC_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/classic/*.spthy


## All case studies
###################


CS_TARGETS=case-studies/Tutorial_analyzed.spthy $(CSF12_CS_TARGETS) $(CLASSIC_CS_TARGETS) $(IND_CS_TARGETS)

case-studies: 	$(CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies/
	-grep -iR "warning\|error" case-studies/

###############################################################################
## Developer specific targets (some out of date)
###############################################################################

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

haddock:
	cabal haddock --executables

depgraph:
	find . -name \*hs | grep -v Old | xargs graphmod -q | tred | dot -odepGraph.svg -Tsvg

ctags:
	ghc -e :ctags src/Main.hs

.PHONY: unit opt all mult coverage haddock case-studies
