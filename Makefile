.PHONY: clean all coq test tests examples install uninstall depgraph \
  example-imp example-lc example-io example-nimp

COQPATHFILE=$(wildcard _CoqPath)

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq all
	$(MAKE) -f $< $@

uninstall: Makefile.coq
	$(MAKE) -f $< $@

test: examples tests

tests:
	make -C tests

examples: example-imp example-lc example-io example-nimp

example-imp: examples/Imp.v
	coqc -Q theories/ ITree examples/Imp.v

example-lc: examples/stlc.v
	coqc -Q theories/ ITree examples/stlc.v

example-lc: examples/stlc.v
	coqc -Q theories/ ITree examples/Nimp.v

example-io: examples/IO.v
	cd examples && \
	  coqc -Q ../theories/ ITree IO.v && \
	  ocamlbuild io.native && ./io.native

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(RM) {*,*/*}/*.{vo,glob} {*,*/*}/.*.aux
	$(RM) _CoqProject Makefile.coq*

_CoqProject: $(COQPATHFILE) _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
	@ echo "# THIS IS AN AUTOMATICALLY GENERATED FILE" >> _CoqProject
	@ echo "# PLEASE EDIT _CoqConfig INSTEAD" >> _CoqProject
	@ echo >> _CoqProject
ifneq ("$(COQPATHFILE)","")
	@ echo "# including: _CoqPath"
	@ cat _CoqPath >> _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) $(shell cat _CoqProject) > /dev/null 2>&1
	# sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)
