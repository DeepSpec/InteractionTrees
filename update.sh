#!/bin/sh
set -xe
make -C .. html
DOCDIR=docs/master
rm -rf $DOCDIR
mv ../html $DOCDIR
sh ./cleanup.sh
git add $DOCDIR
set +x
echo "OK!"
echo "Now do this > git commit -m \"Update\""
