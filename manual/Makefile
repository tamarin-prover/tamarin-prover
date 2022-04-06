PANDOC = pandoc
IFORMAT = markdown
FLAGS = --standalone --toc --toc-depth=2 --mathjax=$(MATHJAX)
STYLE = css/style.css

ifdef MATHJAX_LOCAL
  MATHJAX = ${MATHJAX_LOCAL}
else
  MATHJAX ?= "https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"
endif

TEMPLATE_HTML = templates/template.html
TEMPLATE_TEX = templates/template.latex

SRC = $(sort $(wildcard src/*.md))
OBJ = $(subst .md,.html,$(subst src,book,$(SRC)))
TMP = $(subst src,tmp,$(SRC))

all: $(OBJ)

tmp/%.md: src/%.md ./filter.py
	./filter.py $< $@

book/%.html: tmp/%.md $(TEMPLATE_HTML) latex_macros
	$(PANDOC) -c $(STYLE) \
	  --metadata title="Tamarin Manual" \
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

clean:
	-rm -f book/*.html tex/*.pdf tmp/*.md
