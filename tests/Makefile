.PHONY: all build extraction clean

all: coq extraction

include ../common.mk

extraction: coq
	ocamlbuild extraction/MetaModule.native -no-links

clean: clean-coq
	$(RM) -rf _build/
	$(RM) extraction/*.ml{i,}
