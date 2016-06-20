PANDOC = pandoc
IFORMAT = markdown
FLAGS = --standalone --toc --toc-depth=2 --mathjax=$(MATHJAX)
STYLE = css/style.css

ifdef USE_FILTER
  FILTER = --filter includes.hs
else
  FILTER =
endif

ifdef MATHJAX_LOCAL
  MATHJAX = ${MATHJAX_LOCAL}
else
  MATHJAX ?= "http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"
endif

TEMPLATE_HTML = templates/template.html
TEMPLATE_TEX = templates/template.latex

SRC = $(sort $(wildcard src/*.md))
OBJ = $(subst .md,.html,$(subst src,book,$(SRC)))

all: $(OBJ)

book/%.html: src/%.md $(TEMPLATE_HTML) latex_macros
	$(PANDOC) -c $(STYLE) \
	  ${FILTER} \
	  --template $(TEMPLATE_HTML) -s -f $(IFORMAT) \
	  -t html $(FLAGS) -o $@ $<


pdf:
	$(PANDOC) ${FILTER} -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --latex-engine=xelatex $(FLAGS) \
	  -o tex/tamarin-manual.tex $(SRC)

simple: 
	$(PANDOC) -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --latex-engine=xelatex $(FLAGS) \
	  -o tex/tamarin-manual.tex $(SRC)
	make -C tex

clean:
	-rm book/*.html *.pdf
