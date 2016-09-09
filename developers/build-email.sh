#!/bin/bash

cd $(dirname "$0")/..

tmpdir=${1:-"/tmp"}
tmpfile="$tmpdir/vml-build-email.txt"

# Create a temporary file to keep track of the state
state_f=$(mktemp /tmp/reg-test.XXXXXX)
trap "rm -f $state_f" 0 2 3 15 EXIT

to='builds@cakeml.org'

timeout 12h developers/regression-test.sh $state_f &> >(tee $tmpfile)

case $? in
  124)
    cur_build_dir=`cat $state_f`
    echo "build timed out when testing: $cur_build_dir"
    echo "" >> $tmpfile
    echo "build timed out when testing: $cur_build_dir" >> $tmpfile
    echo "Regression Log:" >> $tmpfile
    echo "----------------------------" >> $tmpfile
    tail -n80 $(dirname "$0")/$cur_build_dir/regression.log | col -bpx >> $tmpfile
    echo "----------------------------" >> $tmpfile
    cat $tmpfile | mail -s "TIMEOUT" $to
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
