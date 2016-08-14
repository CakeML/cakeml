#!/bin/bash

cd $(dirname "$0")/..

if test -n "$1" -a "$1" = "--bamboo"; then
  tmpfile="${bamboo.build.working.directory}/vml-build-email.txt"
else
  tmpfile=/tmp/vml-build-email.txt
fi

to='builds@cakeml.org'

timeout 8h developers/regression-test.sh &>$tmpfile

case $? in
  124)
    cat $tmpfile | mail -s "TIMEOUT" $to
    echo "build timed out"
    ;;
  0)
    cat $tmpfile | mail -s "OK" $to
    echo "build succeeded"
    ;;
  *)
    subject=$(tail -n1 $tmpfile)
    cd $(echo $subject | cut -f2 -d' ')
    cat $tmpfile timing.log <(tail -n80 regression.log) | col -bx | mail -s "$subject" $to
    echo "build failed"
    ;;
esac
