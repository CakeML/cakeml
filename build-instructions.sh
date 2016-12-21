#!/bin/sh
## This script installs Poly/ML, HOL and CakeML.

## build Poly/ML
cd
git clone https://github.com/polyml/polyml -b fixes-5.6
cd polyml
## optionally use polyml master, but that has some bugs (Aug 2016)
# git checkout master
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
# git checkout k11-release-prep # kananaskis-11 when released
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
## optionally switch to a released version, e.g., version1
# git checkout version1
$HOME/HOL/bin/Holmake
## or just Holmake if you set up your PATH as above
# Holmake
