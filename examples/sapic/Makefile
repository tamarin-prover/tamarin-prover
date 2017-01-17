include Makefile.include

BENCHMARKFILES = GJM-contract/contract.spthy.benchmark MoedersheimWebService/set-abstr-lookup.spthy.benchmark NSL/nsl-no_as-untagged.spthy.benchmark StatVerifLeftRight/stateverif_left_right.spthy.benchmark EncWrapDecUnwrap/encwrapdecunwrap.spthy.benchmark
# EncWrapDecUnwrap
BENCHMARKFILESNOH = $(subst benchmark,benchmark-noh,$(BENCHMARKFILES))
DATETIME = $(shell date "+%Y-%m-%d-%H:%M:%S")

TESTFILES = $(subst sapic,spthy,$(wildcard fairexchange-mini/*.sapic))

.PHONY: all benchmark-compute benchmark-verify benchmark-show

all: $(FILES).check

benchmark-compute: $(BENCHMARKFILES)
benchmark-show: $(BENCHMARKFILES)
	@for file in $(BENCHMARKFILES); do echo "$$file: "; tail -n 3 $$file | grep real; done
benchmark-verify: $(BENCHMARKFILES)
	@for file in $(BENCHMARKFILES); do echo "$$file: "; tail -n 20 "$$file-cert" | grep steps ; done

benchmark-noh-compute: $(BENCHMARKFILESNOH)
benchmark-noh-show: $(BENCHMARKFILESNOH)
	@for file in $(BENCHMARKFILESNOH); do echo "$$file: "; tail -n 3 $$file | grep real; done
benchmark-noh-verify: $(BENCHMARKFILESNOH)
	@for file in $(BENCHMARKFILESNOH); do echo "$$file: "; tail -n 20 "$$file-cert" | grep steps ; done


test: $(TESTFILES)
	    $(PROVER) $(FLAGS) --prove $(TESTFILES) | grep --color -E 'falsified|$$'

%.spthy: %.sapic $(SAPIC)
	$(SAPIC) $< > $@

%.trans: %.sapic
	$(SAPIC) $< 

%.check: %
	$(PROVER) $(FLAGS) $<

%.proof: %
	$(PROVER) $(FLAGS) --prove $<

%.altproof: %
	$(ALTPROVER) $(FLAGS) --prove $<

%.interactive: %
	$(PROVER) interactive $(INTERACTIVEFLAGS) $< 2> /dev/null & 
	sleep 1
	open http://localhost:3001

%.remote: %
	scp $< cassis:spthy/
	ssh -L 3002:localhost:3002 \
	cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) interactive --port=3002 $(REMOTEINTERACTIVEFLAGS) $(notdir $<)'
	sleep 1
	open http://localhost:3002

%.remote-proof: %
	scp $< cassis:spthy/
	ssh cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) --prove $(REMOTEFLAGS) $(notdir $<)'

%.remote-check: %
	scp $< cassis:spthy/
	ssh cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) $(REMOTEFLAGS) $(notdir $<)'

%.remote-quietproof: %
	scp $< cassis:spthy/
	ssh cassis "tmux new-window 'cd spthy; killall tamarin-prover; $(ULIMITS);LC_ALL=en_US.utf8 /usr/bin/time $(REMOTEPROVER) --prove $(REMOTEFLAGS) $(notdir $<) 2>$(notdir $<).errorlog | tee $(notdir $<).log '"

%.colossus: %
	scp $< colossus:spthy/
	ssh -L 3004:localhost:3001 \
	colossus 'cd spthy; $(ULIMITScolossus); $(colossusPROVER) interactive $(colossusINTERACTIVEFLAGS) $(notdir $<)'

%.colossus-proof: %
	scp $< colossus:spthy/
	ssh colossus 'cd spthy;  $(ULIMITScolossus); $(colossusPROVER) --prove $(colossusFLAGS) $(notdir $<)'

%.colossus-quietproof: %
	scp $< colossus:spthy/
	ssh colossus "tmux new-window 'cd spthy; $(ULIMITScolossus);/usr/bin/time $(colossusPROVER) --prove$(PROOFFLAGS) $(colossusFLAGS) $(notdir $<) 2>$(notdir $<)-$(DATETIME).errorlog | tee $(notdir $<)-$(DATETIME).log'"

%.colossus-check: %
	scp $< colossus:spthy/
	ssh colossus 'cd spthy; killall tamarin-prover; $(ULIMITScolossus); $(colossusPROVER) $(colossusFLAGS) $(notdir $<)'

%.colossus04: %
	scp $< colossus04:spthy/
	ssh -L 3005:localhost:3001 \
	colossus04 'cd spthy; $(ULIMITScolossus04); $(colossus04PROVER) interactive $(colossus04INTERACTIVEFLAGS) $(notdir $<)'

%.colossus04-proof: %
	scp $< colossus04:spthy/
	ssh colossus04 'cd spthy; $(ULIMITScolossus04); $(colossus04PROVER) --prove $(colossus04FLAGS) $(notdir $<)'

%.colossus04-quietproof: %
	scp $< colossus04:spthy/
	ssh colossus04 "tmux new-window 'cd spthy; $(ULIMITScolossus04);/usr/bin/time $(colossus04PROVER) --prove $(colossus04FLAGS) $(notdir $<) 2>$(notdir $<)-$(DATETIME).errorlog | tee $(notdir $<)-$(DATETIME).log '"

%.colossus04-check: %
	scp $< colossus04:spthy/
	ssh colossus04 'cd spthy; killall tamarin-prover; $(ULIMITScolossus04); $(colossus04PROVER) $(colossus04FLAGS) $(notdir $<)'

%.colossus08: %
	scp $< colossus08:spthy/
	ssh -L 3005:localhost:3001 \
	colossus08 'cd spthy; $(ULIMITScolossus08); $(colossus08PROVER) interactive $(colossus08INTERACTIVEFLAGS) $(notdir $<)'

%.colossus08-proof: %
	scp $< colossus08:spthy/
	ssh colossus08 'cd spthy; $(ULIMITScolossus08); $(colossus08PROVER) --prove $(colossus08FLAGS) $(notdir $<)'

%.colossus08-quietproof: %
	scp $< colossus08:spthy/
	ssh colossus08 "tmux new-window 'cd spthy; $(ULIMITScolossus08);/usr/bin/time $(colossus08PROVER) --prove $(colossus08FLAGS) $(notdir $<) 2>$(notdir $<)-$(DATETIME).errorlog | tee $(notdir $<)-$(DATETIME).log '"

%.colossus08-check: %
	scp $< colossus08:spthy/
	ssh colossus08 'cd spthy; killall tamarin-prover; $(ULIMITScolossus08); $(colossus08PROVER) $(colossus08FLAGS) $(notdir $<)'

%.interactive-proof: %
	$(PROVER) interactive $(FLAGS) --prove $<


%.benchmark-rechen: %
	scp $< rechen:spthy/
	ssh rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); $(REMOTEPROVER) --prove $(REMOTEFLAGS) $<'

%.benchmark: %
	scp $< $(BENCHMARKMACHINE):spthy/
	ssh $(BENCHMARKMACHINE) 'cd spthy; killall tamarin-prover; $(BENCHMARKULIMITS); time $(BENCHMARKPROVER) --prove $(BENCHMARKFLAGS) $(notdir $<)' > $@-cert 2> $@

%.benchmark-noh: %
	scp $< $(BENCHMARKMACHINE):spthy/
	ssh $(BENCHMARKMACHINE) 'cd spthy; killall tamarin-prover; $(BENCHMARKULIMITS); time $(BENCHMARKPROVER) --prove $(BENCHMARKFLAGSNOH) $(notdir $<)' > $@-cert 2> $@

