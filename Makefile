.PHONY: clean all coq

COQPATHFILE=$(wildcard _CoqPath)

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm _CoqProject

_CoqProject: $(COQPATHFILE) _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
ifneq ("$(COQPATHFILE)","")
	@ echo "# including: _CoqPath"
	@ cp _CoqPath _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject
