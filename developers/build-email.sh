#!/bin/bash

set -e

cd $(dirname "$0")/..

tmpfile=/tmp/vml-build-email.txt

if developers/regression-test.sh > $tmpfile 2>&1
then
  echo "build succeeded"
else
  subject=$(tail -n1 $tmpfile)
  cd $(echo $subject | cut -f2 -d' ')
  cat timing.log <(tail -n80 regression.log) | col -bx | mail -S from='"CakeML Builds" <builds@cakeml.org>' -s "'$subject'"  -q $tmpfile builds@cakeml.org
  echo "build failed; email sent"
fi
