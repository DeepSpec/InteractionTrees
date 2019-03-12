.PHONY: clean all coq test tests examples install uninstall depgraph

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
	$(MAKE) -C tests

examples:
	$(MAKE) -C examples

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@


## Use coqdocjs
EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C tests clean
	$(MAKE) -C examples clean
	$(RM) theories/{*,*/*}/*.{vo,glob} theories/{*,*/*}/.*.aux
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
