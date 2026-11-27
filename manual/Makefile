PANDOC = pandoc
IFORMAT = markdown
FLAGS = --standalone --toc --toc-depth=2

TEMPLATE_HTML = templates/template.html
TEMPLATE_TEX = templates/template.latex

SRC = $(sort $(wildcard src/*.md))
# Chapters in the HTML navigation; 000_prelims.md holds notes for manual authors.
CHAPTERS = $(filter-out src/000_prelims.md,$(SRC))
OBJ = $(subst .md,.html,$(subst src,book,$(SRC)))
TMP = $(subst src,tmp,$(SRC))

# The HTML navigation labels builds of master with the Tamarin release and all
# other builds as the development branch.
MANUAL_BRANCH ?= $(shell git rev-parse --abbrev-ref HEAD 2>/dev/null)
CABAL = $(wildcard ../tamarin-prover.cabal)
TAMARIN_VERSION ?= $(if $(CABAL),$(shell sed -n 's/^version: *//p' $(CABAL)))

all: $(OBJ)

tmp/%.md: src/%.md ./filter.py grammar/grammar.ebnf
	./filter.py $< $@

tmp/navigation.stamp: $(SRC) ./chapters.py $(CABAL)
	./chapters.py tmp "$(MANUAL_BRANCH)" "$(TAMARIN_VERSION)" \
	  --pages $(SRC) --chapters $(CHAPTERS)
	touch $@

# --mathml is deprecated from pandoc 3.11 in favour of --math-method=mathml,
# which older versions such as the one used for deployment do not support.
book/%.html: tmp/%.md tmp/navigation.stamp $(TEMPLATE_HTML) latex_macros
	$(PANDOC) --mathml \
	  --metadata-file=tmp/$*.json \
	  --template $(TEMPLATE_HTML) -s -f $(IFORMAT) \
	  --citeproc \
	  --bibliography=src/manual.bib \
	  -t html $(FLAGS) -o $@ $<


pdf:	$(TMP) $(TEMPLATE_LATEX) latex_macros
	sed 's,[0-9]*_.*.html#,#,' < $(TMP) > tex/all.md
	echo "\n# References\n\n" >> tex/all.md
	$(PANDOC) -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --pdf-engine=xelatex $(FLAGS) \
	  --citeproc \
	  --bibliography=src/manual.bib \
	  -o tex/tamarin-manual.tex tex/all.md
	make -C tex

simple: $(TMP) $(TEMPLATE_LATEX) latex_macros
	$(PANDOC) -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --pdf-engine=xelatex $(FLAGS) \
	  --bibliography=src/manual.bib \
	  -o tex/tamarin-manual.tex $(TMP)
	make -C tex


grammar/grammar.ebnf: ../tree-sitter/tree-sitter-spthy/grammar.js 
	cd grammar && npm install
	cd grammar && node generate-ebnf.js ../../tree-sitter/tree-sitter-spthy/grammar.js > grammar.ebnf

clean:
	-rm -f book/*.html tex/*.pdf tmp/*.md tmp/*.json tmp/navigation.stamp grammar/grammar.ebnf
