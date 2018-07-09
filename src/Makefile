.PHONY: all coq

# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) ITrees)
# -R $(COQLIBDIR)/paco/src Paco -R $(EXTRACTDIR) Extract -R ../lib/CompCert compcert
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES := ITrees
OLLVMFILES := 

VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

all:
	$(MAKE) coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: _CoqPath _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
ifneq ("$(wildcard _CoqPath)","")
	@ echo "# including: _CoqPath"
	@ cp _CoqPath _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject

_CoqPath:
	@ echo > /dev/null

# Directories containing plain Caml code
OCAMLDIRS= $(EXTRACTDIR) $(MLDIR) 

COMMA=,
OCAMLINCLUDES=$(patsubst %,-I %, $(OCAMLDIRS))
print-ocaml-includes:
	@echo $(OCAMLINCLUDES)

OCAMLLIBS := unix,str

.PHONY: clean test qc restore

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	ocamlbuild -clean

-include .depend
