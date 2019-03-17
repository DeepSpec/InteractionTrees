.PHONY: clean all coq test tests examples tutorial install uninstall depgraph

COQPATHFILE=$(wildcard _CoqPath)

build: coq

all:
	# Build the library before tests
	$(MAKE) coq
	$(MAKE) tutorial
# TODO: add tests examples html (left out for speed while we develop tutorial)

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq all
	$(MAKE) -f $< $@

uninstall: Makefile.coq
	$(MAKE) -f $< $@

test: examples tests

tests:
	$(MAKE) -C tests

examples:
	$(MAKE) -C examples

tutorial:
	$(MAKE) -C tutorial

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@


## coqdoc -------------------------------------------------
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments 

ifdef COQDOCJS_DIR
COQDOCFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

export COQDOCFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(COQDOCJS_DIR)/extra/resources/* html
else

export COQDOCFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
endif

## -------------------------------------------------------



clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C tests clean
	$(MAKE) -C examples clean
	$(MAKE) -C tutorial clean
	$(RM) theories/{.,*,*/*}/*.{vo,glob} theories/{.,*,*/*}/.*.aux
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
