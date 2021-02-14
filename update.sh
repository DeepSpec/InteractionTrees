#!/bin/sh
set -xe
make -C .. html
DOCDIR=docs/master
rm -rf $DOCDIR
mv ../html $DOCDIR
sh ./cleanup.sh
set +x
echo "OK!"
echo "Now do this > git add -u ; git commit -m \"Update\""
