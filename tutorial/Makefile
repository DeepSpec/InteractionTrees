.PHONY: tutorial test clean

tutorial: coq test

test: coq
	ocamlbuild imp_test.native
	./imp_test.native

include ../common.mk

clean: clean-coq
