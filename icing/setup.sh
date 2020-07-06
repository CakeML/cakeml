#!/bin/bash

HOLCOMMIT=9eb85f2893da888359e9bff54ed3bca6467523d1
FLOVERCOMMIT=06ad54dec40fbf0bbee97243be5ceab57517eadb

BASEDIR=/opt/CakeML_Icing

mkdir $BASEDIR

cd $BASEDIR

# Install HOL4
cd $BASEDIR && \
    git clone https://github.com/HOL-Theorem-Prover/HOL HOL && \
    cd HOL && git checkout $HOLCOMMIT &&\
    poly < tools/smart-configure.sml && bin/build

export HOLDIR=$BASEDIR/HOL/

# Install FloVer
cd $BASEDIR && \
    git clone https://gitlab.mpi-sws.org/AVA/FloVer FloVer && \
    cd FloVer &&\
    git checkout  &&\
    cd hol4/ &&\
    $HOLDIR/bin/Holmake

export FLOVERDIR=$BASEDIR/FloVer/

# Install CakeML
cd $BASEDIR && git clone https://github.com/CakeML/cakeml cakeml &&\
    cd cakeml && git checkout Iced_cake && \
    git checkout Iced_cake &&\
    cd icing &&\
    $HOLDIR/bin/Holmake
