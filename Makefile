# Please make sure that you have 'stack' installed. 
# https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md

TAMARIN=~/.local/bin/tamarin-prover
SAPIC=~/.local/bin/sapic

# Default installation via stack, multi-threaded
# Try to install Tamarin and SAPIC
default: tamarin sapic

# Default Tamarin installation via stack, multi-threaded
.PHONY: tamarin
tamarin:
	# Uncomment the following if you use docker
	#stack docker pull
	stack setup
	stack install --flag tamarin-prover:threaded
	# Uncomment the following if you use docker
	#cp $(PWD)/.stack-work/docker/_home/.local/bin/tamarin-prover $(HOME)/.local/bin

# Single-threaded Tamarin
.PHONY: single
single: 
	stack setup
	stack install

# Tamarin with profiling options, single-threaded
.PHONY: profiling
profiling:
	stack setup
	stack install --no-system-ghc --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts"

# SAPIC
.PHONY: sapic
sapic:
	cd plugins/sapic && $(MAKE)

# Clean target for SAPIC
.PHONY: sapic-clean
sapic-clean:
	cd plugins/sapic && $(MAKE) clean

# Clean target for Tamarin
.PHONY: tamarin-clean
tamarin-clean:
	stack clean

# Clean Tamarin and SAPIC
.PHONY: clean
clean:	tamarin-clean sapic-clean

# ###########################################################################
# NOTE the remainder makefile is FOR DEVELOPERS ONLY.
# It is by no means official in any form and should be IGNORED :-)
# ###########################################################################

VERSION=1.3.0

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
	mkdir -p case-studies/features/injectivity
	mkdir -p case-studies/cav13
	mkdir -p case-studies/related_work/AIF_Moedersheim_CCS10
	mkdir -p case-studies/related_work/StatVerif_ARR_CSF11
	mkdir -p case-studies/related_work/YubiSecure_KS_STM12
	mkdir -p case-studies/related_work/TPM_DKRS_CSF11
	mkdir -p case-studies/post17
	mkdir -p case-studies/regression/trace
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
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
case-studies/%_analyzed-diff.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies/ccs15
	mkdir -p case-studies/features/equivalence
	mkdir -p case-studies/post17
	mkdir -p case-studies/regression/diff
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

# individual diff-based precomputed (no --prove) case studies
case-studies/%_analyzed-diff-noprove.spthy:	examples/%.spthy $(TAMARIN)
	mkdir -p case-studies/ccs15
	mkdir -p case-studies/features/equivalence
	mkdir -p case-studies/regression/diff
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --diff --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

CCS15_CASE_STUDIES=DDH.spthy  probEnc.spthy  rfid-feldhofer.spthy
CCS15_CS_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/ccs15/,$(CCS15_CASE_STUDIES)))

CCS15_PRECOMPUTED_CASE_STUDIES=Attack_TPM_Envelope.spthy
CCS15_PCS_TARGETS=$(subst .spthy,_analyzed-diff-noprove.spthy,$(addprefix case-studies/ccs15/,$(CCS15_PRECOMPUTED_CASE_STUDIES)))

CCS15_TARGETS= $(CCS15_CS_TARGETS) $(CCS15_PCS_TARGETS)

# CCS15 case studies
ccs15-case-studies:	$(CCS15_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ccs15/*.spthy


REGRESSION_OBSEQ_CASE_STUDIES=issue223.spthy
REGRESSION_OBSEQ_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/regression/diff/,$(REGRESSION_OBSEQ_CASE_STUDIES)))

TESTOBSEQ_CASE_STUDIES=AxiomDiffTest1.spthy AxiomDiffTest2.spthy AxiomDiffTest3.spthy AxiomDiffTest4.spthy N5N6DiffTest.spthy
TESTOBSEQ_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/features/equivalence/,$(TESTOBSEQ_CASE_STUDIES))) $(REGRESSION_OBSEQ_TARGETS)

OBSEQ_TARGETS= $(CCS15_TARGETS) $(TESTOBSEQ_TARGETS)

#Observational equivalence test case studies:
obseq-test-case-studies:	$(TESTOBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/features/equivalence/*.spthy case-studies/regression/diff/*.spthy

#Observational equivalence case studies with CCS15
obseq-case-studies:	$(OBSEQ_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/ccs15/*.spthy case-studies/features/equivalence/*.spthy


## non-subterm convergent equational theories
#############################################
POST17_TRACE_CASE_STUDIES= chaum_unforgeability.spthy foo_eligibility.spthy okamoto_eligibility.spthy needham_schroeder_symmetric_cbc.spthy denning_sacco_symmetric_cbc.spthy
POST17_TRACE_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/post17/,$(POST17_TRACE_CASE_STUDIES)))

POST17_DIFF_CASE_STUDIES= chaum_anonymity.spthy chaum_untraceability.spthy foo_vote_privacy.spthy okamoto_receipt_freeness.spthy okamoto_vote_privacy.spthy
POST17_DIFF_TARGETS=$(subst .spthy,_analyzed-diff.spthy,$(addprefix case-studies/post17/,$(POST17_DIFF_CASE_STUDIES)))

POST17_TARGETS= $(POST17_TRACE_TARGETS)  $(POST17_DIFF_TARGETS)

# POST17 case studies
post17-case-studies:	$(POST17_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/post17/*.spthy

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
	grep "verified\|falsified\|processing time" case-studies/ake/bilinear/*.spthy


## Features
###########

FEATURES_CASE_STUDIES=cav13/DH_example.spthy features//multiset/counter.spthy features//private_function_symbols/NAXOS_eCK_PFS_private.spthy features//private_function_symbols/NAXOS_eCK_private.spthy features//injectivity/injectivity.spthy

FEATURES_CS_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/,$(FEATURES_CASE_STUDIES)))

# case studies
features-case-studies:	$(FEATURES_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/features/multiset/*.spthy case-studies/features/private_function_symbols/*.spthy case-studies/cav13/*.spthy case-studies/features/injectivity/*.spthy

## Regression (old issues)
##########################

REGRESSION_CASE_STUDIES=issue216.spthy

REGRESSION_TARGETS=$(subst .spthy,_analyzed.spthy,$(addprefix case-studies/regression/trace/,$(REGRESSION_CASE_STUDIES)))

# case studies
regression-case-studies:	$(REGRESSION_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/regression/trace/*.spthy

## SAPIC
########

# sapic case studies
case-studies-sapic/%.spthy:	examples/sapic/%.sapic $(SAPIC)
	mkdir -p case-studies-sapic/basic
	mkdir -p case-studies-sapic/encWrapDecUnwrap
	mkdir -p case-studies-sapic/envelope
	mkdir -p case-studies-sapic/fairexchange-asw
	mkdir -p case-studies-sapic/fairexchange-gjm
	mkdir -p case-studies-sapic/fairexchange-km
	mkdir -p case-studies-sapic/fairexchange-mini
	mkdir -p case-studies-sapic/GJM-contract
	mkdir -p case-studies-sapic/locations
	mkdir -p case-studies-sapic/MoedersheimWebService
	mkdir -p case-studies-sapic/NSL
	mkdir -p case-studies-sapic/PKCS11
	mkdir -p case-studies-sapic/predicates
	mkdir -p case-studies-sapic/SCADA
	mkdir -p case-studies-sapic/statVerifLeftRight
	mkdir -p case-studies-sapic/Yubikey
	$(SAPIC) $< $<.tmp > $<.out
	cat $<.out >>$<.tmp
	mv $<.tmp $@
	\rm -f $<.out

SAPIC_CASE_STUDIES=basic/channels1.sapic basic/channels2.sapic basic/channels3.sapic basic/design-choices.sapic basic/exclusive-secrets.sapic basic/no-replication.sapic basic/replication.sapic  basic/running-example.sapic \
encWrapDecUnwrap/encwrapdecunwrap-nolocks.sapic encWrapDecUnwrap/encwrapdecunwrap.sapic \
envelope/envelope_allowsattack.sapic envelope/envelope.sapic envelope/envelope_simpler.sapic \
fairexchange-asw/aswAB-mod.sapic fairexchange-asw/aswAB-mod-weak-A.sapic fairexchange-asw/aswAB-mod-weak-B.sapic fairexchange-asw/aswAB.sapic fairexchange-asw/asw-mod-weak-locks.sapic \
fairexchange-gjm/gjm-locks-fakepcsbranch-B.sapic fairexchange-gjm/gjm-locks-fakepcsbranch.sapic fairexchange-gjm/gjm-locks-magic.sapic fairexchange-gjm/gjm-locks.sapic fairexchange-gjm/gjm-locks-unfairness-A.sapic fairexchange-gjm/gjm.sapic \
fairexchange-km/km.sapic fairexchange-km/km-with-comments.sapic \
fairexchange-mini/mini10.sapic fairexchange-mini/mini2.sapic fairexchange-mini/mini4.sapic fairexchange-mini/mini6.sapic fairexchange-mini/mini8.sapic fairexchange-mini/ndc-nested-2.sapic fairexchange-mini/ndc-nested-4.sapic fairexchange-mini/ndc-nested.sapic fairexchange-mini/mini1.sapic fairexchange-mini/mini3.sapic fairexchange-mini/mini5.sapic fairexchange-mini/mini7.sapic fairexchange-mini/mini9.sapic fairexchange-mini/ndc-nested-3.sapic fairexchange-mini/ndc-nested-5.sapic fairexchange-mini/ndc-two-replications.sapic \
GJM-contract/contract.sapic \
locations/AC.sapic locations/AKE.sapic locations/licensing.sapic locations/OTP.sapic locations/SOC.sapic \
MoedersheimWebService/set-abstr-lookup.sapic MoedersheimWebService/set-abstr.sapic \
NSL/nsl-no_as-untagged.sapic \
PKCS11/pkcs11-templates.sapic PKCS11/pkcs11-dynamic-policy.sapic \
predicates/decwrap_destr.sapic predicates/simple_example.sapic \
SCADA/opc_ua_secure_conversation.sapic \
statVerifLeftRight/stateverif_left_right.sapic \
Yubikey/Yubikey.sapic

SAPIC_CS_TARGETS=$(subst .sapic,.spthy,$(addprefix case-studies-sapic/,$(SAPIC_CASE_STUDIES)))

# case studies
sapic-case-studies:	$(SAPIC_CS_TARGETS)


## SAPIC output in Tamarin
##########################

# individual case studies
case-studies/%_analyzed-sapic.spthy:	case-studies-sapic-regression/%.spthy $(TAMARIN)
	mkdir -p case-studies/sapic/basic
#	mkdir -p case-studies/sapic/encWrapDecUnwrap
	mkdir -p case-studies/sapic/statVerifLeftRight
	mkdir -p case-studies/sapic/GJM-contract
#	mkdir -p case-studies/sapic/MoedersheimWebService
	mkdir -p case-studies/sapic/NSL
	mkdir -p case-studies/sapic/predicates
	mkdir -p case-studies/sapic/locations
	mkdir -p case-studies/sapic/SCADA
	mkdir -p case-studies/sapic/fairexchange-mini
	# Use -N3, as the fourth core is used by the OS and the console
	$(TAMARIN) $< --prove --stop-on-trace=dfs +RTS -N3 -RTS -o$<.tmp >$<.out
	# We only produce the target after the run, otherwise aborted
	# runs already 'finish' the case.
	printf "\n/* Output\n" >>$<.tmp
	cat $<.out >>$<.tmp
	echo "*/" >>$<.tmp
	mv $<.tmp $(subst case-studies,case-studies/sapic,$@)
	\rm -f $<.out

SAPIC_TAMARIN_CASE_STUDIES=basic/no-replication.spthy basic/replication.spthy basic/channels1.spthy basic/channels2.spthy basic/channels3.spthy basic/design-choices.spthy basic/exclusive-secrets.spthy basic/running-example.spthy \
statVerifLeftRight/stateverif_left_right.spthy \
GJM-contract/contract.spthy \
NSL/nsl-no_as-untagged.spthy \
predicates/decwrap_destr.spthy predicates/simple_example.spthy \
locations/AC.spthy locations/AKE.spthy locations/licensing.spthy \
SCADA/opc_ua_secure_conversation.spthy \
fairexchange-mini/mini10.spthy fairexchange-mini/mini2.spthy fairexchange-mini/mini4.spthy fairexchange-mini/mini6.spthy fairexchange-mini/mini8.spthy fairexchange-mini/ndc-nested-2.spthy fairexchange-mini/ndc-nested-4.spthy fairexchange-mini/ndc-nested.spthy fairexchange-mini/mini1.spthy fairexchange-mini/mini3.spthy fairexchange-mini/mini5.spthy fairexchange-mini/mini7.spthy fairexchange-mini/mini9.spthy fairexchange-mini/ndc-nested-3.spthy fairexchange-mini/ndc-nested-5.spthy fairexchange-mini/ndc-two-replications.spthy

# currently not working because of wrong heuristic:
# encWrapDecUnwrap/encwrapdecunwrap.spthy
# MoedersheimWebService/set-abstr.spthy MoedersheimWebService/set-abstr-lookup.spthy
# locations/SOC.spthy 

SAPIC_TAMARIN_CS_TARGETS=$(subst .spthy,_analyzed-sapic.spthy,$(addprefix case-studies/,$(SAPIC_TAMARIN_CASE_STUDIES)))

# case studies
sapic-tamarin-case-studies:	$(SAPIC_TAMARIN_CS_TARGETS)
	grep "verified\|falsified\|processing time" case-studies/sapic/basic/*.spthy case-studies/sapic/statVerifLeftRight/*.spthy case-studies/sapic/GJM-contract/*.spthy case-studies/sapic/NSL/*.spthy case-studies/sapic/predicates/*.spthy case-studies/sapic/locations/*.spthy case-studies/sapic/SCADA/*.spthy case-studies/sapic/fairexchange-mini/*.spthy


## All case studies
###################


CS_TARGETS=case-studies/Tutorial_analyzed.spthy $(CSF12_CS_TARGETS) $(CLASSIC_CS_TARGETS) $(IND_CS_TARGETS) $(AKE_DH_CS_TARGETS) $(AKE_BP_CS_TARGETS) $(FEATURES_CS_TARGETS) $(OBSEQ_TARGETS) $(SAPIC_TAMARIN_CS_TARGETS) $(POST17_TARGETS) $(REGRESSION_TARGETS)

case-studies: 	$(CS_TARGETS)
	grep -R "verified\|falsified\|processing time" case-studies/
	-grep -iR "warning\|error" case-studies/

###############################################################################
## Developer specific targets (some out of date)
###############################################################################

# outdated targets
