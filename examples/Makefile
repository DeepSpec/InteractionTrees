.PHONY: example-imp example-lc example-io example-nimp example-asm example-threads

examples: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

example-imp:
	$(MAKE) -f Makefile.coq Imp.vo

example-asm:
	$(MAKE) -f Makefile.coq Asm.vo

example-lc:
	$(MAKE) -f Makefile.coq stlc.vo

example-io:
	$(MAKE) -f Makefile.coq IO.vo

example-nimp:
	$(MAKE) -f Makefile.coq Nimp.vo

THREADSV=MultiThreadedPrinting.vo ExtractThreadsExample.vo
THREADSML=runthread.ml

example-threads: Makefile.coq $(THREADSML)
	$(MAKE) -f Makefile.coq $(THREADSV)
	coqc -Q theories/ ITree -Q examples/ Examples $(THREADSV)
	ocamlbuild -I extracted runthread.native
	./runthread.native

clean:
	ocamlbuild -clean
	$(RM) extracted/*.*
