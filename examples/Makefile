.PHONY: example-lc example-io example-nimp example-factorial example-threads 

examples: Makefile.coq
	mkdir -p extracted
	$(MAKE) -f Makefile.coq

include ../common.mk

example-echo:
	coqc -Q ../theories ITree Echo.v
	ocamlc echo.mli echo.ml echo_driver.ml -o echo

example-lc:
	$(MAKE) -f Makefile.coq stlc.vo

example-io:
	$(MAKE) -f Makefile.coq IO.vo

example-nimp:
	$(MAKE) -f Makefile.coq Nimp.vo

example-factorial:
	$(MAKE) -f Makefile.coq Factorial.vo

THREADSV=MultiThreadedPrinting.vo ExtractThreadsExample.vo
THREADSML=runthread.ml

example-threads: Makefile.coq $(THREADSML)
	$(MAKE) -f Makefile.coq $(THREADSV)
	ocamlbuild -I extracted runthread.native
	./runthread.native

clean: clean-coq
	ocamlbuild -clean
	$(RM) -r extracted
