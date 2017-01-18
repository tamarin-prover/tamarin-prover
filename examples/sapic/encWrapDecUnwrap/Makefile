PROVER=tamarin-prover
REMOTEPROVER=~/.cabal/bin/tamarin-prover
# ALTPROVER=/Users/robert/Library/Haskell/ghc-7.0.4/lib/tamarin-prover-0.4.1.0/bin/tamarin-prover
HEURISTIC=--heuristic=p
MAUDE=#--with-maude=/Users/robert/bin/maudelib/maude.intelDarwin
FLAGS=$(MAUDE) $(HEURISTIC) #+RTS -N -RTS
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
	scp $< cassis.loria.fr:spthy/
	ssh -L 3002:localhost:3001 \
	cassis.loria.fr 'cd spthy; killall tamarin-prover; $(REMOTEPROVER) interactive $(HEURISTIC) $<'
	sleep 1
	open http://localhost:3001

%.remote-proof: %
	scp $< cassis.loria.fr:spthy/
	ssh -L 3002:localhost:3001 \
	cassis.loria.fr 'cd spthy; killall tamarin-prover; $(REMOTEPROVER) --prove $(HEURISTIC) $<'

%.interactive-proof: %
	$(PROVER) interactive $(FLAGS) --prove $<



