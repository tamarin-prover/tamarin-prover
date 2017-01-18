TARGET = sapic
OBJS=exceptions.cmo btree.cmo position.cmo positionplusinit.cmo var.cmo term.cmo fact.cmo atomformulaaction.cmo action.cmo atom.cmo formula.cmo tamarin.cmo sapicterm.cmo sapicvar.cmo sapicaction.cmo lexer.cmo  sapic.cmo annotatedsapicaction.cmo annotatedsapictree.cmo progressfunction.cmo axioms.cmo annotatedrule.cmo translationhelper.cmo basetranslation.cmo firsttranslation.cmo main.cmo 

FLAGS=-g

.ocaml_ok:
	./check_ocaml.sh

sapic: 	$(OBJS)
	ocamlc $(FLAGS) -o $@ str.cma $(OBJS)
	cp sapic ~/.local/bin

default: .ocaml_ok sapic

depend:
	ocamldep *.ml *.mli > .depend

lexer.ml: sapic.cmi

clean:
	rm -rf *.cmi *.cmo $(TARGET)
	rm -rf sapic.ml sapic.mli lexer.ml lexer.mli
	rm -f .ocaml_ok

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
