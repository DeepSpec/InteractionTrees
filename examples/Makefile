.PHONY: example-lc example-io example-nimp example-factorial example-threads 

examples: Makefile.coq
	mkdir -p extracted
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

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

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	ocamlbuild -clean
	$(RM) -rf extracted Makefile.coq*


## SAZ: This code is copied from ../Makefile -- deduplicate?
## coqdoc -------------------------------------------------
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments 

ifdef COQDOCJS_DIR
COQDOCFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

echo "COQDOCJS_DIR" = @(COQDOCJS_DIR)

html: Makefile.coq 
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(COQDOCJS_DIR)/extra/resources/* html
else

html: Makefile.coq 
	rm -rf html
	$(MAKE) -f Makefile.coq html
endif

## -------------------------------------------------------
