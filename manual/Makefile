PANDOC = pandoc
IFORMAT = markdown
FLAGS = --standalone --toc --toc-depth=2 --mathjax=$(MATHJAX)
STYLE = css/style.css

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

book/%.html: src/%.md $(TEMPLATE_HTML) latex_macros includes
	$(PANDOC) -c $(STYLE) \
	  --filter ./includes \
	  --template $(TEMPLATE_HTML) -s -f $(IFORMAT) \
	  --bibliography=src/manual.bib \
	  -t html $(FLAGS) -o $@ $<


pdf:
	sed 's,[0-9]*_.*.html#,#,' < $(SRC) > tex/all.md
	$(PANDOC) -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --latex-engine=xelatex $(FLAGS) \
	  --filter ./includes \
	  --bibliography=src/manual.bib \
	  -o tex/tamarin-manual.tex tex/all.md
	make -C tex

simple: 
	$(PANDOC) -f $(IFORMAT) \
	  --template $(TEMPLATE_TEX) --latex-engine=xelatex $(FLAGS) \
	  --bibliography=src/manual.bib \
	  -o tex/tamarin-manual.tex $(SRC)
	make -C tex

includes: includes.hs
	stack ghc -- --make includes.hs -o includes

clean:
	-rm book/*.html *.pdf
