# Please make sure that you have 'stack' installed. 
# https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

TAMARIN=~/.local/bin/tamarin-prover

# Default installation via stack
default: 
	stack setup
	stack install

clean:
	stack clean

# ###########################################################################
# NOTE the remainder makefile is FOR DEVELOPERS ONLY.
# It is by no means official in any form and should be IGNORED :-)
# ###########################################################################

VERSION=1.1.0

#source-dists:
#	cd lib/utils; cabal sdist
#	cd lib/term; cabal sdist
#	cd lib/theory; cabal sdist
#	cabal sdist

#source-dists-tests: source-dists
#	mkdir -p /tmp/dist-test-$(VERSION)/
#	cp lib/utils/dist/tamarin-prover-utils-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
#	cp lib/term/dist/tamarin-prover-term-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
#	cp lib/theory/dist/tamarin-prover-theory-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
#	cp dist/tamarin-prover-$(VERSION).tar.gz /tmp/dist-test-$(VERSION)/
#	cd /tmp/dist-test-$(VERSION)/; cabal install *.tar.gz --force-reinstalls



###############################################################################
## Case Studies
###############################################################################


## CSF'12
#########

# These case studies are located in examples/
DH2=DH2_original.spthy

KAS=KAS1.spthy KAS2_eCK.spthy KAS2_original.spthy

KEA=KEA_plus_KI_KCI.spthy KEA_plus_KI_KCI_wPFS.spthy

NAXOS=NAXOS_eCK_PFS.spthy NAXOS_eCK.spthy

SDH=SignedDH_PFS.spthy #SignedDH_eCK.spthy
# The "SignedDH_eCK.spthy" case study has not been working for a long time, 
# probably some change in the heuristics somewhere made it run indefinitely.

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
case-studies/%_analyzed.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies/csf12
	mkdir -p case-studies/classic
	mkdir -p case-studies/loops
	mkdir -p case-studies/ake/bilinear
	mkdir -p case-studies/ake/dh
	mkdir -p case-studies/features/private_function_symbols
	mkdir -p case-studies/features/multiset
	mkdir -p case-studies/cav13
	mkdir -p case-studies/related_work/AIF_Moedersheim_CCS10
	mkdir -p case-studies/related_work/StatVerif_ARR_CSF11
	mkdir -p case-studies/related_work/YubiSecure_KS_STM12
	mkdir -p case-studies/related_work/TPM_DKRS_CSF11
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$(TMPRES) >$(TMPOUT)
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	echo "\n/* Output" >>$(TMPRES)
	cat $(TMPOUT) >>$(TMPRES)
	echo "*/" >>$(TMPRES)
	mv $(TMPRES) $@
	\rm -f $(TMPOUT)

## Observational Equivalence
############################

# individual diff-based case studies
case-studies/%_analyzed-diff.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies/ccs15
	mkdir -p case-studies/features/equivalence
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$(TMPRES) >$(TMPOUT)
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	echo "\n/* Output" >>$(TMPRES)
	cat $(TMPOUT) >>$(TMPRES)
	echo "*/" >>$(TMPRES)
	mv $(TMPRES) $@
	\rm -f $(TMPOUT)

# individual diff-based precomputed (no --prove) case studies
case-studies/%_analyzed-diff-noprove.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies/ccs15
	mkdir -p case-studies/features/equivalence
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$(TMPRES) >$(TMPOUT)
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	echo "\n/* Output" >>$(TMPRES)
	cat $(TMPOUT) >>$(TMPRES)
	echo "*/" >>$(TMPRES)
	mv $(TMPRES) $@
	\rm -f $(TMPOUT)

CCS15_CASE_STUDIES=DDH.spthy  probEnc.spthy  rfid-feldhofer.spthy
CCS15_CS_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/ccs15/,$(CCS15_CASE_STUDIES)))

CCS15_PRECOMPUTED_CASE_STUDIES=Attack_TPM_Envelope.spthy
CCS15_PCS_TARGETS=$(subst .spthy,_analyzed-diff-noprove.spthy,$(addprefix case-studies/ccs15/,$(CCS15_PRECOMPUTED_CASE_STUDIES)))

CCS15_TARGETS= $(CCS15_CS_TARGETS) $(CCS15_PCS_TARGETS)

# CCS15 case studies
ccs15-case-studies:	$(CCS15_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ccs15/*.spthy

TESTOBSEQ_CASE_STUDIES=AxiomDiffTest1.spthy AxiomDiffTest2.spthy AxiomDiffTest3.spthy N5N6DiffTest.spthy
TESTOBSEQ_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/features/equivalence/,$(TESTOBSEQ_CASE_STUDIES)))

OBSEQ_TARGETS= $(CCS15_TARGETS) $(TESTOBSEQ_TARGETS)

#Observational equivalence test case studies:
obseq-test-case-studies:	$(TESTOBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/features/equivalence/*.spthy

#Observational equivalence case studies with CCS15
obseq-case-studies:	$(OBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ccs15/*.spthy case-studies/features/equivalence/*.spthy

## Inductive Strengthening
##########################

TPM=related_work/TPM_DKRS_CSF11/TPM_Exclusive_Secrets.spthy related_work/TPM_DKRS_CSF11/Envelope.spthy

STATVERIF=related_work/StatVerif_ARR_CSF11/StatVerif_Security_Device.spthy related_work/StatVerif_ARR_CSF11/StatVerif_GM_Contract_Signing.spthy

AIF=related_work/AIF_Moedersheim_CCS10/Keyserver.spthy

YUBIKEY=related_work/YubiSecure_KS_STM12/Yubikey.spthy related_work/YubiSecure_KS_STM12/Yubikey_and_YubiHSM.spthy related_work/YubiSecure_KS_STM12/Yubikey_multiset.spthy related_work/YubiSecure_KS_STM12/Yubikey_and_YubiHSM_multiset.spthy

LOOPS=loops/TESLA_Scheme1.spthy loops/Minimal_KeyRenegotiation.spthy loops/Minimal_Create_Use_Destroy.spthy loops/RFID_Simple.spthy loops/Minimal_Create_Use_Destroy.spthy loops/Minimal_Crypto_API.spthy loops/Minimal_Loop_Example.spthy loops/JCS12_Typing_Example.spthy loops/Minimal_Typing_Example.spthy loops/Typing_and_Destructors.spthy
# TESLA_Scheme2.spthy (not finished)

IND_CASE_STUDIES=$(TPM) $(AIF) $(LOOPS) $(STATVERIF) $(YUBIKEY)
IND_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/,$(IND_CASE_STUDIES)))

# case studies
induction-case-studies:	$(IND_CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies/related_work/ case-studies/loops/


## Classical Protocols
######################


CLASSIC_CASE_STUDIES=TLS_Handshake.spthy NSPK3.spthy NSLPK3.spthy NSLPK3_untagged.spthy

CLASSIC_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/classic/,$(CLASSIC_CASE_STUDIES)))

# case studies
classic-case-studies:	$(CLASSIC_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/classic/*.spthy


## AKE Diffie-Hellman
####################

AKE_DH_CASE_STUDIES=DHKEA_NAXOS_C_eCK_PFS_keyreg_partially_matching.spthy DHKEA_NAXOS_C_eCK_PFS_partially_matching.spthy UM_one_pass_fix.spthy UM_three_pass.spthy NAXOS_eCK.spthy UM_three_pass_combined.spthy NAXOS_eCK_PFS.spthy UM_three_pass_combined_fixed.spthy UM_one_pass_attack.spthy

AKE_DH_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/ake/dh/,$(AKE_DH_CASE_STUDIES)))

# case studies
ake-dh-case-studies:	$(AKE_DH_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ake/dh/*.spthy


## Bilinear Pairing
####################

AKE_BP_CASE_STUDIES=Chen_Kudla.spthy Chen_Kudla_eCK.spthy Joux.spthy Joux_EphkRev.spthy RYY.spthy RYY_PFS.spthy Scott.spthy Scott_EphkRev.spthy TAK1.spthy TAK1_eCK_like.spthy

AKE_BP_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/ake/bilinear/,$(AKE_BP_CASE_STUDIES)))

# case studies
ake-bp-case-studies:	$(AKE_BP_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ake/dh/*.spthy


## Features
###########

FEATURES_CASE_STUDIES=cav13/DH_example.spthy features//multiset/counter.spthy features//private_function_symbols/NAXOS_eCK_PFS_private.spthy features//private_function_symbols/NAXOS_eCK_private.spthy

FEATURES_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/,$(FEATURES_CASE_STUDIES)))

# case studies
features-case-studies:	$(FEATURES_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/features/multiset/*.spthy case-studies/features/private_function_symbols/*.spthy case-studies/cav13/*.spthy



## All case studies
###################


CS_TARGETS=case-studies/Tutorial_analyzed.spthy $(CSF12_CS_TARGETS) $(CLASSIC_CS_TARGETS) $(IND_CS_TARGETS) $(AKE_DH_CS_TARGETS) $(AKE_BP_CS_TARGETS) $(FEATURES_CS_TARGETS) $(OBSEQ_TARGETS)

case-studies: 	$(CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies/
	-grep -iR "warning\|error" case-studies/

###############################################################################
## Developer specific targets (some out of date)
###############################################################################

# outdated targets
