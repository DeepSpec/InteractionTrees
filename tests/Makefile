.PHONY: all extraction clean

all: coq extraction

coq: output

EXTRDIR:=output

$(EXTRDIR):
	mkdir -p $(EXTRDIR)

include ../common.mk

extraction: coq
	sh extraction-test.sh

clean: clean-coq
	$(RM) -rf _build/
	$(RM) extraction/*.ml{i,}
