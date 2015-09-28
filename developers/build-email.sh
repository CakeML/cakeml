#!/bin/bash

cd $(dirname "$0")/..

tmpfile=/tmp/vml-build-email.txt

from='"CakeML Builds" <builds@cakeml.org>'
to='builds@cakeml.org'

timeout 8h developers/regression-test.sh &>$tmpfile

case $? in
  124)
    cat $tmpfile | mail -S from="$from" -s "TIMEOUT" $to
    echo "build timed out"
    ;;
  0)
    cat $tmpfile | mail -S from="$from" -s "OK" $to
    echo "build succeeded"
    ;;
  *)
    subject=$(tail -n1 $tmpfile)
    cd $(echo $subject | cut -f2 -d' ')
    cat timing.log <(tail -n80 regression.log) | col -bx | mail -S from="$from" -s "$subject"  -q $tmpfile $to
    echo "build failed"
    ;;
esac
