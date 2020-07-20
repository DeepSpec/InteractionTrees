set -xe
cd output/

ocamlbuild test.native
./test.native

ocamlbuild MetaModule.native
./MetaModule.native
# This executable should do absolutely nothing
