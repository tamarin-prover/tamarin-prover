# Please make sure that you have 'stack' installed.
# https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

TAMARIN=~/.local/bin/tamarin-prover
SAPIC=~/.local/bin/sapic

# Settings for fast testing
SUBDIR=/
ifdef FAST  
	SUBDIR=/fast-tests/
endif
# Default installation via stack, multi-threaded
# Try to install Tamarin
default: tamarin

# Default Tamarin installation via stack, multi-threaded
.PHONY: tamarin
tamarin:
	stack setup
	stack install

# Single-threaded Tamarin
.PHONY: single
single:
	stack setup
	stack install --flag tamarin-prover:-threaded

# Tamarin with profiling options, single-threaded
.PHONY: profiling
profiling:
	stack setup
	stack install --no-system-ghc --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts" --flag tamarin-prover:-threaded

# Clean target for Tamarin
.PHONY: tamarin-clean
tamarin-clean:
	stack clean

# Clean Tamarin
.PHONY: clean
clean:	tamarin-clean

# ###########################################################################
# NOTE the remainder makefile is FOR DEVELOPERS ONLY.
# It is by no means official in any form and should be IGNORED :-)
# ###########################################################################

VERSION=1.11.0

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


CSF12_CASE_STUDIES=$(JKL1) $(JKL2) $(KEA) $(NAXOS) $(UM) $(STS) $(SDH) $(KAS) $(DH2)
CSF12_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)csf12/,$(CSF12_CASE_STUDIES)))

# CSF'12 case studies
csf12-case-studies:	$(CSF12_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)csf12/*.spthy

# individual case studies
case-studies$(SUBDIR)%_analyzed.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p $(dir $@)
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual case studies, special case with auto-sources
case-studies$(SUBDIR)%_analyzed-auto-sources.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p $(dir $@)
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --auto-sources --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual case studies, special case with tactics
case-studies$(SUBDIR)%_analyzed-oracle-chaum.spthy: examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)csf18-xor
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual case studies, special case with sequential dfs
case-studies$(SUBDIR)%_analyzed-seqdfs.spthy: examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)regression/trace
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=seqdfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual case studies, special case with default oracle
case-studies$(SUBDIR)%_analyzed-deforacle.spthy: examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)regression/trace
	# Use -N3, as the fourth core is used by the OS and the console
	cd examples/regression/trace && $(TAMARIN) defaultoracle.spthy --prove +RTS -N3 -RTS -odefaultoracle.spthy.tmp >defaultoracle.spthy.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out


## Observational Equivalence
############################

# individual diff-based case studies
case-studies$(SUBDIR)%_analyzed-diff.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)ccs15
	mkdir -p case-studies$(SUBDIR)features/equivalence
	mkdir -p case-studies$(SUBDIR)post17
	mkdir -p case-studies$(SUBDIR)regression/diff
	mkdir -p case-studies$(SUBDIR)csf18-xor/diff-models
	# Use -N3, as the fourth core is used by the OS and the console
	# For execution on server using -N14 for faster completion!
	$(TAMARIN) $< --prove --diff --stop-on-trace=dfs +RTS -N14 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual diff-based precomputed (no --prove) case studies
case-studies$(SUBDIR)%_analyzed-diff-noprove.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)ccs15
	mkdir -p case-studies$(SUBDIR)features/equivalence
	mkdir -p case-studies$(SUBDIR)regression/diff
	mkdir -p case-studies$(SUBDIR)csf18-xor/diff-models
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual diff-based case studies running only on the Observational_equivalence lemma
case-studies$(SUBDIR)%_analyzed-diff-obseqonly.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)csf18-xor/diff-models
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove=Observational_equivalence --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

CCS15_CASE_STUDIES=DDH.spthy  probEnc.spthy  rfid-feldhofer.spthy
CCS15_CS_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies$(SUBDIR)ccs15/,$(CCS15_CASE_STUDIES)))

CCS15_PRECOMPUTED_CASE_STUDIES=Attack_TPM_Envelope.spthy
CCS15_PCS_TARGETS=$(subst .spthy,_analyzed-diff-noprove.spthy,$(addprefix case-studies$(SUBDIR)ccs15/,$(CCS15_PRECOMPUTED_CASE_STUDIES)))

CCS15_TARGETS= $(CCS15_CS_TARGETS) $(CCS15_PCS_TARGETS)

# CCS15 case studies
ccs15-case-studies:	$(CCS15_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)ccs15/*.spthy


REGRESSION_OBSEQ_CASE_STUDIES=issue223.spthy issue198-1.spthy issue198-2.spthy issue324.spthy issue331.spthy
REGRESSION_OBSEQ_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies$(SUBDIR)regression/diff/,$(REGRESSION_OBSEQ_CASE_STUDIES)))

TESTOBSEQ_CASE_STUDIES=AxiomDiffTest1.spthy AxiomDiffTest2.spthy AxiomDiffTest3.spthy AxiomDiffTest4.spthy N5N6DiffTest.spthy MacroDiffprobEnc.spthy
TESTOBSEQ_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies$(SUBDIR)features/equivalence/,$(TESTOBSEQ_CASE_STUDIES))) $(REGRESSION_OBSEQ_TARGETS)

OBSEQ_TARGETS= $(CCS15_TARGETS) $(TESTOBSEQ_TARGETS)


# individual case studies, special case with tactics for csf19
case-studies$(SUBDIR)%_analyzed-oracle-gcm-wrapping.spthy: examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)csf19-wrapping
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual case studies, special case with tactics for csf19
case-studies$(SUBDIR)%_analyzed-oracle-siv-wrapping.spthy: examples/%.spthy $(TAMARIN)
	mkdir -p case-studies$(SUBDIR)csf19-wrapping
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# CSF19 case studies
CSF19_WRAPPING_GCM_CASE_STUDIES=gcm.spthy
CSF19_WRAPPING_GCM_TARGETS=$(subst .spthy,_analyzed-oracle-gcm-wrapping.spthy,$(addprefix case-studies$(SUBDIR)csf19-wrapping/,$(CSF19_WRAPPING_GCM_CASE_STUDIES)))

CSF19_WRAPPING_SIV_CASE_STUDIES=siv.spthy
CSF19_WRAPPING_SIV_TARGETS=$(subst .spthy,_analyzed-oracle-siv-wrapping.spthy,$(addprefix case-studies$(SUBDIR)csf19-wrapping/,$(CSF19_WRAPPING_SIV_CASE_STUDIES)))

CSF19_WRAPPING_TARGETS= $(CSF19_WRAPPING_GCM_TARGETS) $(CSF19_WRAPPING_SIV_TARGETS)

csf19-wrapping-case-studies: $(CSF19_WRAPPING_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)csf19-wrapping/*.spthy


#Observational equivalence test case studies:
obseq-test-case-studies:	$(TESTOBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)features/equivalence/*.spthy case-studies$(SUBDIR)regression/diff/*.spthy

#Observational equivalence case studies with CCS15
obseq-case-studies:	$(OBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)ccs15/*.spthy case-studies$(SUBDIR)features/equivalence/*.spthy


## non-subterm convergent equational theories
#############################################
POST17_TRACE_CASE_STUDIES= chaum_unforgeability.spthy foo_eligibility.spthy okamoto_eligibility.spthy needham_schroeder_symmetric_cbc.spthy denning_sacco_symmetric_cbc.spthy
POST17_TRACE_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)post17/,$(POST17_TRACE_CASE_STUDIES)))

POST17_DIFF_CASE_STUDIES= chaum_anonymity.spthy chaum_untraceability.spthy foo_vote_privacy.spthy okamoto_receipt_freeness.spthy okamoto_vote_privacy.spthy
POST17_DIFF_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies$(SUBDIR)post17/,$(POST17_DIFF_CASE_STUDIES)))

POST17_TARGETS= $(POST17_TRACE_TARGETS)  $(POST17_DIFF_TARGETS)

# POST17 case studies
post17-case-studies:	$(POST17_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)post17/*.spthy

## XOR-using case studies
#########################

XOR_TRACE_CASE_STUDIES= NSLPK3xor.spthy CRxor.spthy CH07.spthy KCL07.spthy LAK06.spthy
XOR_TRACE_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)csf18-xor/,$(XOR_TRACE_CASE_STUDIES)))

XOR_TRACE_ORACLE_CASE_STUDIES= chaum_offline_anonymity.spthy
XOR_TRACE_ORACLE_TARGETS=$(subst .spthy,_analyzed-oracle-chaum.spthy,$(addprefix case-studies$(SUBDIR)csf18-xor/,$(XOR_TRACE_ORACLE_CASE_STUDIES)))

XOR_BASIC_TRACE_CASE_STUDIES= xor0.spthy xor1.spthy xor2.spthy xor3.spthy xor4.spthy xor-basic.spthy
XOR_BASIC_TRACE_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)features/xor/basicfunctionality/,$(XOR_BASIC_TRACE_CASE_STUDIES)))

# Includes 6 out of 9 diff-case studies from CSF18, excluding KCL07-UK1, LAK06-UK2, LAK06-UK3 due to runtime!
XOR_DIFF_CASE_STUDIES= CH07-UK1.spthy CH07-UK2.spthy  KCL07-UK2.spthy LAK06-UK1.spthy
XOR_DIFF_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies$(SUBDIR)csf18-xor/diff-models/,$(XOR_DIFF_CASE_STUDIES)))

XOR_DIFF_OBSEQONLY_CASE_STUDIES= CH07-UK3.spthy
XOR_DIFF_OBSEQONLY_TARGETS=$(subst .spthy,_analyzed-diff-obseqonly.spthy,$(addprefix case-studies$(SUBDIR)csf18-xor/diff-models/,$(XOR_DIFF_OBSEQONLY_CASE_STUDIES)))

XOR_DIFF_PRECOMPUTED_CASE_STUDIES= KCL07-UK3_attack.spthy
XOR_DIFF_PRECOMPUTED_TARGETS=$(subst .spthy,_analyzed-diff-noprove.spthy,$(addprefix case-studies$(SUBDIR)csf18-xor/diff-models/,$(XOR_DIFF_PRECOMPUTED_CASE_STUDIES)))

# XOR case studies
xor-trace-case-studies: $(XOR_BASIC_TRACE_TARGETS) $(XOR_TRACE_TARGETS) $(XOR_TRACE_ORACLE_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)features/xor/basicfunctionality/*.spthy case-studies$(SUBDIR)csf18-xor/*.spthy

xor-diff-case-studies: $(XOR_DIFF_TARGETS) $(XOR_DIFF_OBSEQONLY_TARGETS) $(XOR_DIFF_PRECOMPUTED_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)csf18-xor/diff-models/*.spthy

XOR_TARGETS=$(XOR_BASIC_TRACE_TARGETS) $(XOR_TRACE_TARGETS) $(XOR_TRACE_ORACLE_TARGETS) $(XOR_DIFF_TARGETS) $(XOR_DIFF_OBSEQONLY_TARGETS) $(XOR_DIFF_PRECOMPUTED_TARGETS)

xor-full-case-studies: $(XOR_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)features/xor/basicfunctionality/*.spthy case-studies$(SUBDIR)csf18-xor/*.spthy case-studies$(SUBDIR)csf18-xor/diff-models/*.spthy

## Inductive Strengthening
##########################

TPM=related_work/TPM_DKRS_CSF11/TPM_Exclusive_Secrets.spthy related_work/TPM_DKRS_CSF11/Envelope.spthy

STATVERIF=related_work/StatVerif_ARR_CSF11/StatVerif_Security_Device.spthy related_work/StatVerif_ARR_CSF11/StatVerif_GM_Contract_Signing.spthy

AIF=related_work/AIF_Moedersheim_CCS10/Keyserver.spthy

YUBIKEY=related_work/YubiSecure_KS_STM12/Yubikey.spthy related_work/YubiSecure_KS_STM12/Yubikey_and_YubiHSM.spthy related_work/YubiSecure_KS_STM12/Yubikey_multiset.spthy related_work/YubiSecure_KS_STM12/Yubikey_and_YubiHSM_multiset.spthy

LOOPS=loops/TESLA_Scheme1.spthy loops/Minimal_KeyRenegotiation.spthy loops/Minimal_Create_Use_Destroy.spthy loops/RFID_Simple.spthy loops/Minimal_Create_Use_Destroy.spthy loops/Minimal_Crypto_API.spthy loops/Minimal_Loop_Example.spthy loops/JCS12_Typing_Example.spthy loops/Minimal_Typing_Example.spthy loops/Typing_and_Destructors.spthy
# TESLA_Scheme2.spthy (not finished)

IND_CASE_STUDIES=$(TPM) $(AIF) $(LOOPS) $(STATVERIF) $(YUBIKEY)
IND_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR),$(IND_CASE_STUDIES)))

# case studies
induction-case-studies:	$(IND_CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies$(SUBDIR)related_work/ case-studies$(SUBDIR)loops/


## Classical Protocols
######################


CLASSIC_CASE_STUDIES=TLS_Handshake.spthy NSPK3.spthy NSLPK3.spthy NSLPK3_untagged.spthy

CLASSIC_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)classic/,$(CLASSIC_CASE_STUDIES)))

# case studies
classic-case-studies:	$(CLASSIC_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)classic/*.spthy


## AKE Diffie-Hellman
####################

AKE_DH_CASE_STUDIES=DHKEA_NAXOS_C_eCK_PFS_keyreg_partially_matching.spthy DHKEA_NAXOS_C_eCK_PFS_partially_matching.spthy UM_one_pass_fix.spthy UM_three_pass.spthy NAXOS_eCK.spthy UM_three_pass_combined.spthy NAXOS_eCK_PFS.spthy UM_three_pass_combined_fixed.spthy UM_one_pass_attack.spthy

AKE_DH_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)ake/dh/,$(AKE_DH_CASE_STUDIES)))

# case studies
ake-dh-case-studies:	$(AKE_DH_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)ake/dh/*.spthy


## Bilinear Pairing
####################

AKE_BP_CASE_STUDIES=Chen_Kudla.spthy Chen_Kudla_eCK.spthy Joux.spthy Joux_EphkRev.spthy RYY.spthy RYY_PFS.spthy Scott.spthy Scott_EphkRev.spthy TAK1.spthy TAK1_eCK_like.spthy

AKE_BP_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)ake/bilinear/,$(AKE_BP_CASE_STUDIES)))

# case studies
ake-bp-case-studies:	$(AKE_BP_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)ake/bilinear/*.spthy


## Features
###########

FEATURES_CASE_STUDIES=cav13/DH_example.spthy features//multiset/counter.spthy features//multiset/NumberSubtermTests.spthy features//private_function_symbols/NAXOS_eCK_PFS_private.spthy features//private_function_symbols/NAXOS_eCK_private.spthy features//injectivity/injectivity.spthy features//configuration/configuration.spthy features//macros/MacroExample.spthy features//macros/MacroGlobalVarNSPK3.spthy features//macros/MacroWithRestrictionCRxor.spthy

FEATURES_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR),$(FEATURES_CASE_STUDIES)))

# case studies
features-case-studies:	$(FEATURES_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)features/multiset/*.spthy case-studies$(SUBDIR)features/private_function_symbols/*.spthy case-studies$(SUBDIR)cav13/*.spthy case-studies$(SUBDIR)features/injectivity/*.spthy

## Auto-sources
###############

AUTO_SOURCES_CASE_STUDIES=CCITT_X509_1.spthy CCITT_X509_1c.spthy \
                   CCITT_X509_3.spthy CCITT_X509_3_BAN.spthy \
                   AS_Concrete_RPC.spthy Lowe_AS_Concrete_RPC.spthy \
                   AS_Modified_RPC.spthy AS_RPC.spthy \
                   Denning-Sacco-SK-Lowe.spthy Denning-Sacco-SK.spthy \
                   Yahalom_BAN.spthy Yahalom-Lowe.spthy Yahalom.spthy \
                   Nssk.spthy Nssk_amended.spthy Otway-Rees.spthy \
                   Wide_Mouthed_Frog.spthy Wide_Mouthed_Frog_Lowe.spthy \
                   SpliceAS.spthy SpliceAS_2.spthy SpliceAS_3.spthy \
                   WooLam_Pi_f.spthy

AUTO_SOURCES_CS_TARGETS=$(subst .spthy,_analyzed-auto-sources.spthy,$(addprefix case-studies$(SUBDIR)features/auto-sources/spore/,$(AUTO_SOURCES_CASE_STUDIES)))

# case studies
auto-sources-case-studies:	$(AUTO_SOURCES_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)features/auto-sources/spore/*.spthy

## Accountability
################

ACCOUNTABILITY_CASE_STUDIES=ct.spthy whodunit.spthy ocsps-msr.spthy ocsps-msr-untrusted.spthy

ACCOUNTABILITY_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)accountability/csf21-acc-unbounded/previous/,$(ACCOUNTABILITY_CASE_STUDIES)))

# case studies
accountability-case-studies:	$(ACCOUNTABILITY_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)accountability/csf21-acc-unbounded/previous/*.spthy

## Regression (old issues)
##########################

FAST_REGRESSION_CASE_STUDIES=issue446-1.spthy issue446-2.spthy
FAST_REGRESSION_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)regression/trace/,$(FAST_REGRESSION_CASE_STUDIES)))


REGRESSION_CASE_STUDIES=issue216.spthy issue193.spthy issue310.spthy issue519.spthy issue527.spthy issue515.spthy

REGRESSION_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)regression/trace/,$(REGRESSION_CASE_STUDIES)))

SEQDFS_CASE_STUDIES=seqdfsneeded.spthy
SEQDFS_TARGETS=$(subst .spthy,_analyzed-seqdfs.spthy,$(addprefix case-studies$(SUBDIR)regression/trace/,$(SEQDFS_CASE_STUDIES)))

DEFAULTORACLE_CASE_STUDIES=defaultoracle.spthy
DEFAULTORACLE_CASE_TARGETS=$(subst .spthy,_analyzed-deforacle.spthy, $(addprefix case-studies$(SUBDIR)regression/trace/,$(DEFAULTORACLE_CASE_STUDIES)))

# case studies
regression-case-studies:	$(REGRESSION_TARGETS) $(SEQDFS_TARGETS) $(DEFAULTORACLE_CASE_TARGETS) $(FAST_REGRESSION_TARGETS)
	grep "verified\|falsified\|processing time" case-studies$(SUBDIR)regression/trace/*.spthy


## SAPIC output in Tamarin
##########################

# FAST <=> processing time less than 10sec on Robert's current computer (per file)
SAPIC_CASE_STUDIES_FAST=$(subst examples/sapic/,,$(wildcard examples/sapic/fast/*/*.spthy))

# SLOW <=> processing time more than 10sec on Robert's current computer, but less than a day
SAPIC_CASE_STUDIES_SLOW=$(subst examples/sapic/,,$(wildcard examples/sapic/slow/*/*.spthy))

# SUPER SLOW <=> processing time more than a day or take's more memory than Robert's computer can take
SAPIC_CASE_STUDIES_SUPER_SLOW=$(subst examples/sapic/,,$(wildcard examples/sapic/super-slow/*/*.spthy))

SAPIC_CS_TARGETS_FAST=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)sapic/,$(SAPIC_CASE_STUDIES_FAST)))
SAPIC_CS_TARGETS_SLOW=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)sapic/,$(SAPIC_CASE_STUDIES_SLOW)))
SAPIC_CS_TARGETS_SUPER_SLOW=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies$(SUBDIR)sapic/,$(SAPIC_CASE_STUDIES_SUPER_SLOW)))

# lol:
# 	$(info $$var is [${SAPIC_CS_TARGETS}])

# case studies
sapic-case-studies:	$(SAPIC_CS_TARGETS_FAST) $(SAPIC_CS_TARGETS_SLOW) # used for regressions, skips super slow tests
	grep "verified\|falsified\|processing time" $^
sapic-case-studies-fast:	$(SAPIC_CS_TARGETS_FAST) # used for quick checks during development
	grep "verified\|falsified\|processing time" $^
sapic-case-studies-superslow:	$(SAPIC_CS_TARGETS_SUPER_SLOW) # used to heat in winter
	grep "verified\|falsified\|processing time" $^

## All case studies
###################


UNAME_S := $(shell uname -s)
case-studies$(SUBDIR)system.info:
	mkdir -p case-studies
	mkdir -p case-studies/fast-tests
	hostname > $@
ifeq ($(UNAME_S),Linux)
	cat /proc/cpuinfo  | grep 'name'| uniq >> $@
	cat /proc/cpuinfo  | grep process| wc -l >> $@
	cat /proc/meminfo  | grep 'MemTotal'| uniq >> $@
else 	# ($(UNAME_S),Darwin)
	sysctl hw >> $@
endif
#	top -b | head >> $@

CS_TARGETS=case-studies$(SUBDIR)Tutorial_analyzed.spthy $(CSF19_WRAPPING_TARGETS) $(CSF12_CS_TARGETS) $(CLASSIC_CS_TARGETS) $(IND_CS_TARGETS) $(AKE_DH_CS_TARGETS) $(AKE_BP_CS_TARGETS) $(FEATURES_CS_TARGETS) $(OBSEQ_TARGETS) $(SAPIC_CS_TARGETS_FAST) $(SAPIC_CS_TARGETS_SLOW) $(POST17_TARGETS) $(REGRESSION_TARGETS) $(XOR_TARGETS) $(AUTO_SOURCES_CS_TARGETS) $(ACCOUNTABILITY_CS_TARGETS)

case-studies: 	case-studies$(SUBDIR)system.info $(CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies$(SUBDIR)
	-grep -iR "warning\|error" case-studies$(SUBDIR)

## Fast case studies
####################

FAST_CS_TARGETS = case-studies$(SUBDIR)Tutorial_analyzed.spthy $(CCS15_PCS_TARGETS) $(TESTOBSEQ_TARGETS) $(FEATURES_CS_TARGETS) $(REGRESSION_OBSEQ_TARGETS) $(CSF12_CS_TARGETS) $(IND_CS_TARGETS) $(CCS15_CS_TARGETS) $(XOR_TRACE_TARGETS) $(POST17_TRACE_TARGETS) $(CLASSIC_CS_TARGETS) $(AKE_BP_CS_TARGETS) $(SEQDFS_TARGETS) $(DEFAULTORACLE_CASE_TARGETS) $(FAST_REGRESSION_TARGETS) $(XOR_DIFF_OBSEQONLY_TARGETS)

fast-case-studies: case-studies$(SUBDIR)system.info $(FAST_CS_TARGETS)
	mkdir -p case-studies$(SUBDIR)
	grep -R "verified\|falsified\|processing time" case-studies$(SUBDIR)
	-grep -iR "warning\|error" case-studies$(SUBDIR)


###############################################################################
## Developer specific targets (some out of date)
###############################################################################

# outdated targets
