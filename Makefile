all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

graph:
	./depgraph.sh

install:
	$(MAKE) -f Makefile.coq install

html: all
	rm -rf docs
	mkdir docs
	coqdoc --html --interpolate --parse-comments --utf8 \
		--toc \
		--external https://math-comp.github.io/htmldoc_2_1_0/ mathcomp \
		-R theories SSProve \
		-d docs --multi-index `find . -name "*.v" ! -wholename "./_opam/*"`
.PHONY: html
