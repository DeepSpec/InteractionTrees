.PHONY: tutorial clean

tutorial: coq

include ../common.mk

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) *.{vo,glob} .*.aux
	# ocamlbuild -clean
	$(RM) -rf extracted Makefile.coq*
