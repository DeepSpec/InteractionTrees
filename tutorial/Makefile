.PHONY: tutorial test clean

tutorial: coq test

coq: _CoqProject

test: coq
	ocamlopt -w -33-20-3 imp_test.mli imp_test.ml -o imp_test.native
	./imp_test.native

include ../common.mk

_CoqProject:
	cp _CoqProject.make _CoqProject

clean: clean-coq
	rm -f _CoqProject
