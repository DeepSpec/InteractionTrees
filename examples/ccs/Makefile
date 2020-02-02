examples: Makefile.coq
	mkdir -p extracted
	$(MAKE) -f Makefile.coq

include ../../common.mk

clean: clean-coq
	ocamlbuild -clean
	$(RM) -r extracted
