all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

Makefile.rocq:
	rocq makefile -f _RocqProject -o Makefile.rocq

graph:
	./depgraph.sh

install:
	$(MAKE) -f Makefile.rocq install

html: all
	rm -rf docs
	mkdir docs
	rocq doc --html --interpolate --parse-comments --utf8 \
		--toc \
		--external https://math-comp.github.io/htmldoc_2_3_0/ mathcomp \
		-R theories SSProve \
		-d docs --multi-index `find . -name "*.v" ! -wholename "./_opam/*"`
.PHONY: html
