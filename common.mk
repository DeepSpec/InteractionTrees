# Shared make commands

.PHONY: coq clean-coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean-coq:
	if [ -e Makefile.coq ] ; then $(MAKE) -f Makefile.coq cleanall ; fi
	$(RM) Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

## coqdoc -------------------------------------------------
COQDOCFLAGS:= \
  -t "Interaction Trees" \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments 

ifdef COQDOCJS_DIR
COQDOCFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

export COQDOCFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(COQDOCJS_DIR)/extra/resources/* html
else

export COQDOCFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
endif

## -------------------------------------------------------
