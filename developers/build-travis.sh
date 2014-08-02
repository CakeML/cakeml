#!/bin/bash

set -e

HOLDIR=$(heapname | xargs dirname) || exit $?
echo "HOL revision: $(cd $HOLDIR; git rev-parse --short HEAD)"
echo "Machine: $(uname -nmo)"

git clean -xdf

while read i
do
  if [ ! -d $i ]
  then
      echo "Ignoring non-existent directory $i"
      continue
  fi
  pushd $i
  Holmake cleanAll &&
  if Holmake
  then
      if [ -x selftest.exe ]
      then
        ./selftest.exe || {
          echo "FAILED: $i selftest"
          exit 1
        }
      fi
  else
      echo "FAILED: $i"
      exit 1
  fi
  popd
done < developers/build-sequence
