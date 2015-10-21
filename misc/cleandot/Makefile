DEPS= tamarin-cleandot.py
SRC= test1.dot test2.dot
DST1= $(SRC:.dot=-basic.png)
DST2= $(SRC:.dot=-clean.png)
DST= $(DST1) $(DST2)

ALL: $(DST)

%-basic.png:	%.dot $(DEPS)
	\rm -if $@
	-/usr/bin/dot -Tpng -o $@ $< >$@-clean

%-clean.png:	%.dot $(DEPS)
	\rm -if $@
	-./tamarin-cleandot.py -Tpng -o $@ $< >$@-clean

clean:
	\rm -if $(DST)
