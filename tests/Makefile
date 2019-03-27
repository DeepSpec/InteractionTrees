.PHONY: all build extraction clean

all: coq extraction

include ../common.mk

extraction: coq
	ocamlbuild extraction/MetaModule.native -no-links

clean:
	$(RM) {*,*/*}/*.{vo,glob} {*,*/*}/.*.aux
	$(RM) -rf _build/
	$(RM) *.{vo,glob} .*.aux
	$(RM) extraction/*.ml{i,}
