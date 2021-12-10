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
