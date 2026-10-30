.PHONY: clean all coq test tests examples tutorial hoare_example secure_example install uninstall depgraph for-dune

COQPATHFILE=$(wildcard _CoqPath)

build: coq

include common.mk

all:
	# Build the library before tests
	$(MAKE) coq
	$(MAKE) test
	$(MAKE) hoare_example
	$(MAKE) secure_example

install: Makefile.coq coq
	$(MAKE) -f $< $@

uninstall: Makefile.coq
	$(MAKE) -f $< $@

test: examples tests

tests:
	$(MAKE) -C tests
	$(MAKE) -C tutorial test

examples:
	$(MAKE) -C examples

tutorial:
	$(MAKE) -C tutorial

hoare_example:
	$(MAKE) -C hoare_example

secure_example:
	$(MAKE) -C secure_example

clean: clean-coq
	$(RM) _CoqProject
	$(MAKE) -C tests clean
	$(MAKE) -C examples clean
	$(MAKE) -C tutorial clean
	$(MAKE) -C hoare_example clean
	$(MAKE) -C secure_example clean

_CoqProject: $(COQPATHFILE) _CoqProject.itree _CoqProject.extra Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
	@ echo "# THIS IS AN AUTOMATICALLY GENERATED FILE" >> _CoqProject
	@ echo "# PLEASE EDIT _CoqProject.itree or _CoqPRoject.extra INSTEAD" >> _CoqProject
	@ echo >> _CoqProject
ifneq ("$(COQPATHFILE)","")
	@ echo "# including: _CoqPath"
	@ cat _CoqPath >> _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqProject.itree _CoqProject.extra"
	@ cat _CoqProject.itree _CoqProject.extra >> _CoqProject

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	sh depgraph.sh
