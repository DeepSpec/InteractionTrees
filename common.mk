# Shared make commands

.PHONY: coq clean-coq html

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean-coq: _CoqProject
	if [ -e Makefile.coq ] ; then $(MAKE) -f Makefile.coq cleanall ; fi
	$(RM) Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

## coqdoc -------------------------------------------------
COQDOCEXTRAFLAGS:= \
  -t "Interaction Trees" \
  --toc --toc-depth 2 \
  --index indexpage --no-lib-name --parse-comments \

COQDOCJS_DIR:=$(wildcard coqdocjs)

ifneq ($(COQDOCJS_DIR),)
COQDOCEXTRAFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

export COQDOCEXTRAFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(COQDOCJS_DIR)/extra/resources/* html
else

export COQDOCEXTRAFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
endif

## -------------------------------------------------------
