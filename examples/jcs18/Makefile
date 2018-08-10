# Makefile for Tamarin files associated with DNP3 SAv5.

default: local

local:	dnp3.m4
	m4 dnp3.m4 > dnp3.spthy
	tamarin-prover test
	tamarin-prover interactive . --interface='*4' --port=3001 --heuristic=i

clean:
	\rm -f client_session_key.aes
