TARGET = sapic
OBJS= deoptionalize.cmo exceptions.cmo btree.cmo position.cmo positionplusinit.cmo var.cmo term.cmo fact.cmo atomformulaaction.cmo action.cmo atom.cmo formula.cmo verdict.cmo lemma.cmo  tamarin.cmo sapicterm.cmo sapicvar.cmo sapicaction.cmo lexer.cmo  sapic.cmo annotatedsapicaction.cmo annotatedsapictree.cmo progressfunction.cmo restrictions.cmo sufficient.cmo annotatedrule.cmo translationhelper.cmo basetranslation.cmo firsttranslation.cmo main.cmo 
FLAGS=-g

OCAMLC    := $(shell command -v ocamlc    2> /dev/null)
OCAMLLEX  := $(shell command -v ocamllex  2> /dev/null)
OCAMLYACC := $(shell command -v ocamlyacc 2> /dev/null)
OCAMLDEP  := $(shell command -v ocamldep  2> /dev/null)
OCAMLC_GTEQ_402 := $(shell expr `ocamlc -version | sed -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/'` \>= 40200)

default: sapic

sapic:
ifdef OCAMLC
	@echo "Found ocamlc."
ifdef OCAMLLEX
	@echo "Found ocamllex."
ifdef OCAMLYACC
	@echo "Found ocamlyacc."
ifdef OCAMLDEP
	@echo "Found ocamldep."
ifeq "$(OCAMLC_GTEQ_402)" "1"
	@echo "Building SAPIC."
	$(MAKE) $(OBJS)
	ocamlc $(FLAGS) -o $@ str.cma $(OBJS)
	@echo "Installing SAPIC into ~/.local/bin/"
	cp sapic ~/.local/bin
else
	@echo "Found OCAML version < 4.02. SAPIC will not be installed."
endif
else
	@echo "ocamldep not found. SAPIC will not be installed."
endif
else
	@echo "ocamlyacc not found. SAPIC will not be installed."
endif
else
	@echo "ocamllex not found. SAPIC will not be installed."
endif
else
	@echo "ocamlc not found. SAPIC will not be installed."
endif

depend:
	ocamldep *.ml *.mli > .depend

lexer.ml: sapic.cmi

.PHONY: clean
clean:
	rm -rf *.cmi *.cmo $(TARGET)
	rm -rf sapic.ml sapic.mli lexer.ml lexer.mli

.SUFFIXES: .ml .mli .mll .mly .cmo .cmi

.ml.cmo:
	ocamlc $(FLAGS) -c $<
.mli.cmi:
	ocamlc $(FLAGS) -c $<
.mll.ml:
	ocamllex $<
.mly.ml:
	ocamlyacc $<
.ml.mli:
	ocamlc -i $< > $@

-include .depend
