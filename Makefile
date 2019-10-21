.PHONY: clean all coq test tests examples tutorial install uninstall depgraph

COQPATHFILE=$(wildcard _CoqPath)

build: coq

include common.mk

all:
	# Build the library before tests
	$(MAKE) coq
	$(MAKE) tutorial
	$(MAKE) test

install: Makefile.coq coq
	$(MAKE) -f $< $@

uninstall: Makefile.coq
	$(MAKE) -f $< $@

test: examples tests

tests:
	$(MAKE) -C tests

examples:
	$(MAKE) -C examples

echo-example:
	$(MAKE) -C examples example-echo

tutorial:
	$(MAKE) -C tutorial

clean: clean-coq
	$(RM) _CoqProject
	$(MAKE) -C tests clean
	$(MAKE) -C examples clean
	$(MAKE) -C tutorial clean

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
	$(COQDEP) -dumpgraph $(DEPS_DOT) $(shell cat _CoqConfig) > /dev/null 2>&1
	sed 's%\("theories/\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\\n%' -i $(DEPS_DOT)
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)

docker:
	docker build -t lysxia/itree .
	docker run -it lysxia/itree
