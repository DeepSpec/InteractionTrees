#!/usr/bin/env sh

cd InteractionTrees/lib/
git clone https://github.com/coq-contribs/paco.git
cd ../ # at /

cd src && make
cd ../ # at /

