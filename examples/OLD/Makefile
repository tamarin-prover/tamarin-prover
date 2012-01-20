SRC= $(wildcard *.m4)
DEST= $(SRC:.m4=.spthy)

default: protocols

test:
	echo "Sources:      $(SRC)"
	echo "Destinations: $(DEST)"

protocols:	$(DEST)

%.spthy:	%.m4 macros.m4h compromise.m4h
	#cpp -w -P -C $< >$@
	m4 $< >$@


clean:
	\rm -f $(DEST)

