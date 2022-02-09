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

%.spthy: %.sapic
	$(SAPIC) $< > $@

%.trans: %.sapic
	$(SAPIC) $< 

%.check: %
	$(PROVER) $(FLAGS) $<

%.proof: %
	$(PROVER) $(FLAGS) --prove$(PROOFFLAGS) $<

%.altproof: %
	$(ALTPROVER) $(FLAGS) --prove$(PROOFFLAGS) $<

%.interactive: %
	$(PROVER) interactive $(INTERACTIVEFLAGS) $< 2> /dev/null & 
	sleep 1
	open http://localhost:3001
	
# Example make HOST=colossus11 testfile.spthy.remote-interactive
%.remote-interactive: %
	scp $< $(HOST):spthy/
	ssh -t -L $($(HOST)LOCALPORT):localhost:$($(HOST)REMOTEPORT) \
	$(HOST) 'cd spthy; $($(HOST)ULIMITS); $($(HOST)PROVER) interactive --port=$($(HOST)REMOTEPORT) $($(HOST)INTERACTIVEFLAGS) $(notdir $<)'
	sleep 1
	open http://localhost:$($(HOST)LOCALPORT)

%.remote-proof: %
	scp $< $(HOST):spthy/
	ssh -t $(HOST) 'cd spthy; $($(HOST)ULIMITS); $($(HOST)PROVER) --prove$(PROOFFLAGS) $($(HOST)FLAGS) $(notdir $<)'

%.remote-check: %
	scp $< $(HOST):spthy/
	ssh -t $(HOST) 'cd spthy; $($(HOST)ULIMITS); $($(HOST)PROVER) $($(HOST)FLAGS) $(notdir $<)'

%.remote-quietproof: %
	scp $< $(HOST):spthy/
	ssh $(HOST) "tmux new-window 'cd spthy; $($(HOST)ULIMITS);LC_ALL=en_US.utf8 /usr/bin/time $($(HOST)PROVER) --prove$(PROOFFLAGS) $($(HOST)FLAGS) $(notdir $<) 2>$(notdir $<)-$(HOST)-$(DATETIME).errorlog | tee $(notdir $<)-$(HOST)-$(DATETIME).log '"

%.remote-quietinteractive: %
	scp $< $(HOST):spthy/
	ssh $(HOST) "tmux new-window 'cd spthy; $($(HOST)ULIMITS); $($(HOST)PROVER) interactive --port=$($(HOST)REMOTEPORT) $($(HOST)INTERACTIVEFLAGS) $(notdir $<) 2>$(notdir $<)-$(HOST)-$(DATETIME).errorlog | tee $(notdir $<)-$(HOST)-$(DATETIME).log'"
	sleep 1
	ssh -f -N -t -L $($(HOST)LOCALPORT):localhost:$($(HOST)REMOTEPORT) $(HOST) 
	open http://localhost:$($(HOST)LOCALPORT)

%.benchmark-rechen: %
	scp $< rechen:spthy/
	ssh rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); $(REMOTEPROVER) --prove$(PROOFFLAGS) $(REMOTEFLAGS) $<'

%.benchmark: %
	scp $< $(BENCHMARKMACHINE):spthy/
	ssh $(BENCHMARKMACHINE) 'cd spthy; killall tamarin-prover; $(BENCHMARKULIMITS); time $(BENCHMARKPROVER) --prove$(PROOFFLAGS) $(BENCHMARKFLAGS) $(notdir $<)' > $@-cert 2> $@

%.benchmark-noh: %
	scp $< $(BENCHMARKMACHINE):spthy/
	ssh $(BENCHMARKMACHINE) 'cd spthy; killall tamarin-prover; $(BENCHMARKULIMITS); time $(BENCHMARKPROVER) --prove$(PROOFFLAGS) $(BENCHMARKFLAGSNOH) $(notdir $<)' > $@-cert 2> $@

