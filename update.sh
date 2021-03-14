#!/bin/sh
# Clear dune _CoqProject before building
if [ -f ../_CoqProject ]; then
  diff -q ../_CoqProject ../_CoqProject.dune
  if [ 0 -eq "$?" ] ; then rm ../_CoqProject; fi
fi

set -xe
make -C .. html -j2
DOCDIR=docs/master
rm -rf $DOCDIR
mv ../html $DOCDIR
sh ./cleanup.sh
set +x
echo "OK!"
echo "Now do this > git add -u ; git status ; git commit -m \"Update\""
