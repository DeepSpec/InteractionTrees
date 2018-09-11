.PHONY: all extraction

all: extraction

# Ensure extracted code is compilable
# - MetaModule.v is a module that depends on the
#   ITree library
# - Extract.v contains the extraction command for
#   MetaModule (and recursively its dependencies)
extraction:
	cd extraction; \
	  coqc -Q ../../theories ITree \
	    -Q . TestExtraction \
	    ./MetaModule.v \
	    ./Extract.v
	ocamlbuild extraction/MetaModule.native -no-links
