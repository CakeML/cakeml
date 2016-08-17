#!/bin/bash

cd $(dirname "$0")/..

tmpdir=${1:-"/tmp"}
tmpfile="$tmpdir/vml-build-email.txt"

to='builds@cakeml.org'

timeout 8h developers/regression-test.sh &> >(tee $tmpfile)

case $? in
  124)
    cat $tmpfile | mail -s "TIMEOUT" $to
    echo "build timed out"
    exit 124
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
    exit 1
    ;;
esac
