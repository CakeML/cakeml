#!/bin/sh

## build Poly/ML
cd
git clone https://github.com/polyml/polyml
cd polyml
## optionally switch to a released version, e.g., fixes-5.5.2
# git checkout fixes-5.5.2
./configure --enable-shared
## optionally pass an installation prefix to configure
# ./configure --enable-shared --prefix=<dir>
## then you need to put <dir>/bin in your PATH
##       and <dir>/lib in your LD_LIBRARY_PATH
# export PATH=<dir>/bin:$PATH
# export LD_LIBRARY_PATH=<dir>/lib:$LD_LIBRARY_PATH
make
make compiler
make install

## build HOL
cd
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
## optionally switch to a released version, e.g., kananaskis-10
# git checkout kananaskis-10
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
