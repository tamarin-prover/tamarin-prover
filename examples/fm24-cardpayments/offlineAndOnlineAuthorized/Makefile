TAMARIN = tamarin-prover#-develop-1.9.0-initial
#TFLAGS = +RTS -N14 -M32G -RTS
DECOMMENT = tools/decomment
ORACLE_DIR = oracle
PROOF_DIR = models-n-proofs
SEPARATOR = ==============================================================================

#variables (with default values)
localAuth = Yes
CVM = OnlinePIN
copyIAD = Yes
value = High

#regex
left1 = if(\(|\(([a-zA-Z0-9]+\|)+)
left2 = endif(\(|\(([a-zA-Z0-9]+\|)+)
right = (\)|(\|[a-zA-Z0-9]+)+\))

value_regex = \/\*$(left1)$(value)$(right) *| *$(left2)$(value)$(right)\*\/
CVM_regex = \/\*$(left1)$(CVM)$(right) *| *$(left2)$(CVM)$(right)\*\/

ifeq ($(localAuth), Yes)
	auth_regex = \/\*$(left1)LocalAuth$(right) *| *$(left2)LocalAuth$(right)\*\/
	_auth = LocalAuth
else
	auth_regex = \/\*$(left1)NoLocalAuth$(right) *| *$(left2)NoLocalAuth$(right)\*\/
	_auth = NoLocalAuth
endif

ifeq ($(copyIAD), Yes)
	copyIAD_regex = \/\*$(left1)CopyIAD$(right) *| *$(left2)CopyIAD$(right)\*\/
	_copyIAD = CopyIAD
else
	copyIAD_regex = \/\*$(left1)NoCopyIAD$(right) *| *$(left2)NoCopyIAD$(right)\*\/
	_copyIAD = NoCopyIAD
endif

regex = ($(auth_regex)|$(copyIAD_regex)|$(CVM_regex)|$(value_regex))
theory = C8_$(_auth)_$(_copyIAD)_$(CVM)_$(value)

#set proof dir to default if none set
ifndef dir
	dir = $(PROOF_DIR)
endif

#use oracle if indicated
ifndef oracle
	oracle = $(ORACLE_DIR)/C8.oracle
endif
ifeq ($(oracle),$(wildcard $(oracle)))
  _oracle = --heuristic=O --oraclename=$(oracle)
endif

#prove only one lemma if indicated
ifdef lemma
  _lemma = =$(lemma)
endif

#the Tamarin command to be executed
cmd = $(TAMARIN) --prove$(_lemma) $(dir)/$(theory).spthy $(_oracle) $(TFLAGS) --output=$(dir)/$(theory).proof

.SILENT:
proof:
	#Create directory for specific models and their proofs
	mkdir -p $(dir)
	
	#Generate theory file $(theory).spthy
	sed -E 's/$(regex)//g' C8.spthy > $(dir)/$(theory).tmp
	sed -E 's/theory .*/theory $(theory)/' $(dir)/$(theory).tmp > $(dir)/$(theory).spthy
	
	#Remove all comments
ifeq ($(DECOMMENT),$(wildcard $(DECOMMENT)))
	$(DECOMMENT) $(dir)/$(theory).spthy > $(dir)/$(theory).tmp
	cat $(dir)/$(theory).tmp > $(dir)/$(theory).spthy
endif

	#Print date and time for monitoring
	date +'[%a %d %b %Y, %I:%M %p] Analysis started...'	
	
	#run Tamarin
	echo ' >> $(cmd)'
	#(time $(cmd))> $(dir)/$(theory).tmp 2>&1
	$(cmd) > $(dir)/$(theory).tmp 2>&1
	
	#add breaklines
	echo >> $(dir)/$(theory).proof
	echo >> $(dir)/$(theory).proof
	
	#add summary of results to proof file
	(sed -n '/^$(SEPARATOR)/,$$p' $(dir)/$(theory).tmp) >> $(dir)/$(theory).proof
	
	#Clean up
	$(RM) $(dir)/$(theory).tmp
	date +'[%a %d %b %Y, %I:%M %p] Done.'	

ceight:
	make localAuth=No copyIAD=No CVM=NoCVM value=Low
	make localAuth=No copyIAD=No CVM=NoCVM value=High
	make localAuth=No copyIAD=No CVM=OnlinePIN value=Low
	make localAuth=No copyIAD=No CVM=OnlinePIN value=High
	make localAuth=No copyIAD=No CVM=ODCVM value=Low
	make localAuth=No copyIAD=No CVM=ODCVM value=High

	make localAuth=No copyIAD=Yes CVM=NoCVM value=Low
	make localAuth=No copyIAD=Yes CVM=NoCVM value=High
	make localAuth=No copyIAD=Yes CVM=OnlinePIN value=Low
	make localAuth=No copyIAD=Yes CVM=OnlinePIN value=High
	make localAuth=No copyIAD=Yes CVM=ODCVM value=Low
	make localAuth=No copyIAD=Yes CVM=ODCVM value=High

	make localAuth=Yes copyIAD=No CVM=NoCVM value=Low
	make localAuth=Yes copyIAD=No CVM=NoCVM value=High
	make localAuth=Yes copyIAD=No CVM=OnlinePIN value=Low
	make localAuth=Yes copyIAD=No CVM=OnlinePIN value=High
	make localAuth=Yes copyIAD=No CVM=ODCVM value=Low
	make localAuth=Yes copyIAD=No CVM=ODCVM value=High

	make localAuth=Yes copyIAD=Yes CVM=NoCVM value=Low
	make localAuth=Yes copyIAD=Yes CVM=NoCVM value=High
	make localAuth=Yes copyIAD=Yes CVM=OnlinePIN value=Low
	make localAuth=Yes copyIAD=Yes CVM=OnlinePIN value=High
	make localAuth=Yes copyIAD=Yes CVM=ODCVM value=Low
	make localAuth=Yes copyIAD=Yes CVM=ODCVM value=High

ceight-executable:
	make localAuth=No copyIAD=No CVM=NoCVM value=Low lemma=executable
	make localAuth=No copyIAD=No CVM=NoCVM value=High lemma=executable
	make localAuth=No copyIAD=No CVM=OnlinePIN value=Low lemma=executable
	make localAuth=No copyIAD=No CVM=OnlinePIN value=High lemma=executable
	make localAuth=No copyIAD=No CVM=ODCVM value=Low lemma=executable
	make localAuth=No copyIAD=No CVM=ODCVM value=High lemma=executable

	make localAuth=No copyIAD=Yes CVM=NoCVM value=Low lemma=executable
	make localAuth=No copyIAD=Yes CVM=NoCVM value=High lemma=executable
	make localAuth=No copyIAD=Yes CVM=OnlinePIN value=Low lemma=executable
	make localAuth=No copyIAD=Yes CVM=OnlinePIN value=High lemma=executable
	make localAuth=No copyIAD=Yes CVM=ODCVM value=Low lemma=executable
	make localAuth=No copyIAD=Yes CVM=ODCVM value=High lemma=executable

	make localAuth=Yes copyIAD=No CVM=NoCVM value=Low lemma=executable
	make localAuth=Yes copyIAD=No CVM=NoCVM value=High lemma=executable
	make localAuth=Yes copyIAD=No CVM=OnlinePIN value=Low lemma=executable
	make localAuth=Yes copyIAD=No CVM=OnlinePIN value=High lemma=executable
	make localAuth=Yes copyIAD=No CVM=ODCVM value=Low lemma=executable
	make localAuth=Yes copyIAD=No CVM=ODCVM value=High lemma=executable

	make localAuth=Yes copyIAD=Yes CVM=NoCVM value=Low lemma=executable
	make localAuth=Yes copyIAD=Yes CVM=NoCVM value=High lemma=executable
	make localAuth=Yes copyIAD=Yes CVM=OnlinePIN value=Low lemma=executable
	make localAuth=Yes copyIAD=Yes CVM=OnlinePIN value=High lemma=executable
	make localAuth=Yes copyIAD=Yes CVM=ODCVM value=Low lemma=executable
	make localAuth=Yes copyIAD=Yes CVM=ODCVM value=High lemma=executable

html:
	./tools/collect $(dir) --columns=results/exec.txt --output=results/exec.html #--split_theory_regex="C8_(.*)LocalAuth_(.*)CopyIAD_(.*)_(.*)"
	./tools/collect $(dir) --columns=results/confidentiality.txt --output=results/confidentiality.html #--split_theory_regex="C8_(.*)LocalAuth_(.*)CopyIAD_(.*)_(.*)"
	./tools/collect $(dir) --columns=results/authenticity.txt --output=results/authenticity.html #--split_theory_regex="C8_(.*)LocalAuth_(.*)CopyIAD_(.*)_(.*)"
	./tools/collect $(dir) --columns=results/relay-resistance.txt --output=results/relay-resistance.html #--split_theory_regex="C8_(.*)LocalAuth_(.*)CopyIAD_(.*)_(.*)"
	./tools/collect $(dir) --columns=results/paper.txt --output=results/paper.html
	./tools/collect $(dir) --output=results/full.html

.PHONY: clean

clean:
	$(RM) $(dir)/*.tmp
	$(RM) $(dir)/*.aes

