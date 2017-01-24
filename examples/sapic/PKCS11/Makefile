PROVER=tamarin-prover
REMOTEPROVER=~/.cabal/bin/tamarin-prover
# ALTPROVER=/Users/robert/Library/Haskell/ghc-7.0.4/lib/tamarin-prover-0.4.1.0/bin/tamarin-prover
HEURISTIC=--heuristic=p
BOUND=--bound=36
INTERACTIVEBOUND=--bound=2
MAUDE=#--with-maude=/Users/robert/bin/maudelib/maude.intelDarwin
FLAGS=$(MAUDE) $(HEURISTIC) $(BOUND) #+RTS -N -RTS
INTERACTIVEFLAGS=$(MAUDE) $(HEURISTIC) $(INTERACTIVEBOUND) #+RTS -N -RTS
REMOTEFLAGS=$(MAUDE) $(HEURISTIC) $(BOUND) #+RTS -N -RTS
REMOTEINTERACTIVEFLAGS=$(MAUDE) $(HEURISTIC) $(INTERACTIVEBOUND) #+RTS -N -RTS
ULIMITS       = ulimit -Sv 40000000
ULIMITSRECHEN = ulimit -Sv 30000000
APIP=../../apip #-t first

FILES= $(wildcard *.spthy)

.PHONY: all

all: $(FILES).check

%.spthy: %.apip
	$(APIP) $< > $@

%.trans: %.apip
	$(APIP) $< 

%.check: %
	$(PROVER) $(FLAGS) $<

%.proof: %
	$(PROVER) $(FLAGS) --prove $<

%.altproof: %
	$(ALTPROVER) $(FLAGS) --prove $<

%.interactive: %
	$(PROVER) interactive $(FLAGS) $< 2> /dev/null & 
	sleep 1
	open http://localhost:3001

%.remote: %
	scp $< cassis:spthy/
	ssh -L 3002:localhost:3001 \
	cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) interactive $(REMOTEINTERACTIVEFLAGS) $<'
	sleep 1
	open http://localhost:3001

%.remote-proof: %
	scp $< cassis:spthy/
	ssh cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) --prove $(REMOTEFLAGS) $<'

%.remote-check: %
	scp $< cassis:spthy/
	ssh cassis 'cd spthy; killall tamarin-prover; $(ULIMITS); $(REMOTEPROVER) $(REMOTEFLAGS) $<'

%.rechen: %
	scp $< rechen:spthy/
	ssh -L 3003:localhost:3001 \
	rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); $(REMOTEPROVER) interactive $(REMOTEINTERACTIVEFLAGS) $<'

%.rechen-proof: %
	scp $< rechen:spthy/
	ssh rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); $(REMOTEPROVER) --prove $(REMOTEFLAGS) $<'

%.rechen-check: %
	scp $< rechen:spthy/
	ssh rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); $(REMOTEPROVER) $(REMOTEFLAGS) $<'

%.interactive-proof: %
	$(PROVER) interactive $(FLAGS) --prove $<


%.benchmark: %
	scp $< rechen:spthy/
	ssh rechen 'cd spthy; killall tamarin-prover; $(ULIMITSRECHEN); 
	$(REMOTEPROVER) --prove $(REMOTEFLAGS) $<'

