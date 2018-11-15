.PHONY: all build

all: build

build: Makefile.coq
	make -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@
