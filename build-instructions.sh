#!/bin/sh
## This file describes how to install Poly/ML, HOL and CakeML.

## build Poly/ML
## alternatively on macOS
# brew install polyml
cd
git clone https://github.com/polyml/polyml
cd polyml
## optionally use a branch other than master
# git checkout fixes-5.7
./configure
## optionally pass an installation prefix to configure
# ./configure --prefix=<dir>
## if necessary, put <dir>/bin in your PATH
# export PATH=<dir>/bin:$PATH
make
make compiler
make install

## build HOL
cd
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
## optionally switch to a released version, e.g., kananaskis-11
# git checkout kananaskis-11
## note: currently, we only aim to ensure that
##       CakeML branch master builds on HOL branch master
poly < tools/smart-configure.sml
bin/build
## optionally set HOLDIR to point to the HOL installation
# export HOLDIR=$HOME/HOL
## optionally put $HOLDIR/bin in your PATH
# export PATH=$HOLDIR/bin:$PATH

## build CakeML
cd
git clone https://github.com/CakeML/cakeml
cd cakeml
## optionally switch to a released version, e.g., version2
# git checkout version2
"$HOME/HOL/bin/Holmake"
## or just Holmake if you set up your PATH as above
# Holmake
