.PHONY: tutorial clean

tutorial: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	# ocamlbuild -clean
	$(RM) -rf extracted Makefile.coq*
