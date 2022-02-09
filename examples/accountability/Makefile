include Makefile.include

BENCHMARKFILES =  whodunit_signatures.spthy.benchmark
BENCHMARKFILESNOH = $(subst benchmark,benchmark-noh,$(BENCHMARKFILES))
DATETIME = $(shell date "+%Y-%m-%d-%H:%M:%S")

TESTFILES = $(subst sapic,spthy,$(wildcard fairexchange-mini/*.sapic))

.PHONY: all benchmark-compute benchmark-verify benchmark-show

all: $(FILES).check

benchmark-compute: $(BENCHMARKFILES)
benchmark-show: $(BENCHMARKFILES)
	@for file in $(BENCHMARKFILES); do echo "$$file: "; tail -n 3 $$file | grep real; done
benchmark-verify: $(BENCHMARKFILES)
	@for file in $(BENCHMARKFILES); do echo "$$file: "; tail -n 20 "$$file-cert" | grep steps | grep --color -E 'falsified|$$'; done

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

%.benchmark: %
	/usr/bin/time $(PROVER) $(FLAGS) --prove$(PROOFFLAGS) $<  > $@-cert 2> $@

