#!/bin/bash

set -e

pushd $HOME

# Poly/ML

svn checkout svn://svn.code.sf.net/p/polyml/code/trunk polyml
pushd polyml/polyml
./configure --prefix=$HOME --enable-shared
make
make compiler
make install
popd

export PATH=$PATH:$HOME/bin
export LD_LIBRARY_PATH=$HOME/lib

# HOL

git clone https://github.com/mn200/HOL.git
pushd HOL
poly < tools/smart-configure.sml
bin/build -nograph
popd

popd
