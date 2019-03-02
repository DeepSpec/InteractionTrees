.PHONY: all extraction clean

all: extraction

# Ensure extracted code is compilable
# - MetaModule.v is a module that depends on the
#   ITree library
# - Extract.v contains the extraction command for
#   MetaModule (and recursively its dependencies)
COQC=coqc -Q ../../theories ITree -Q . TestExtraction

extraction:
	cd extraction; \
	    $(COQC) ./MetaModule.v; \
	    $(COQC) ./Extract.v
	ocamlbuild extraction/MetaModule.native -no-links

clean:
	$(RM) {*,*/*}/*.{vo,glob} {*,*/*}/.*.aux
	$(RM) -rf _build/
	$(RM) extraction/*.ml{i,}
