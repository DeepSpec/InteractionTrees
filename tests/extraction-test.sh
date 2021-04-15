set -xe
mkdir -p output
cd output/

COQOPTS="-Q ../../theories ITree -Q ../ ITreeTestExtraction"

coqc $COQOPTS ../extract-tests/Tests.v

ocamlopt test.mli test.ml -o test.native
./test.native

# This executable should do absolutely nothing
