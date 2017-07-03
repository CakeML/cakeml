#!/bin/sh
pushd $(dirname $0)
cd ocaml
make
cd ..
cd cakeml
make
cd ..
cd sml
make
cd ..
python benchmark.py
popd
