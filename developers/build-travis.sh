#!/bin/bash

set -o pipefail

if developers/regression-test.sh |& tee build.log
then
  exit 0
else
  cd $(tail -n1 build.log | cut -f2 -d' ')
  cat timing.log regression.log
  exit 1
fi
