#!/bin/sh
DOCDIR=docs/master
URL="https://github.com/DeepSpec/InteractionTrees"
sed "s%href=\"../\"%href=\"$URL\"%" -i $DOCDIR/*.html
