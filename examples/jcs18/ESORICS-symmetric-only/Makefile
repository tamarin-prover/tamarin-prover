# Makefile for Tamarin files associated with DNP3 SAv5.

UNAME_S := $(shell uname -s)

default: local

local:	dnp3.m4
	m4 dnp3.m4 > dnp3.spthy
	tamarin-prover test
ifeq ($(UNAME_S), Linux)
	(sleep 1 && xopen http://localhost:3001/) &
	tamarin-prover interactive . --interface='*4' --port=3001 --heuristic=i
endif
ifeq ($(UNAME_S), Darwin)
	(sleep 1 && open http://localhost:3001/) &
	tamarin-prover interactive . --interface='*4' --port=3001 --heuristic=i
endif

clean:
	\rm -f client_session_key.aes
