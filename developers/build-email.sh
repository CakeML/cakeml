#!/bin/bash

cd $(dirname "$0")/..

# Create a temporary file to keep track of the state
log_f=$(mktemp /tmp/cakeml-log.XXXXXX)
state_f=$(mktemp /tmp/cakeml-state.XXXXXX)
trap "rm -f $log_f $state_f" 0 2 3 15 EXIT

to='builds@cakeml.org'

timeout 12h developers/regression-test.sh $state_f &> >(tee $log_f)
result=$?

cur_build_dir=`cat $state_f`
cd $cur_build_dir

case $result in
  0)
    cat $log_f | mail -s "OK" $to
    echo "build succeeded"
    ;;
  124)
    cat $log_f timing.log <(tail -n80 regression.log) | col -bpx | mail -s "TIMEOUT" $to
    echo "build timed out in: $cur_build_dir"
    ;;
  *)
    subject=$(tail -n1 $log_f)
    cat $log_f timing.log <(tail -n80 regression.log) | col -bpx | mail -s "$subject" $to
    echo "build failed in: $cur_build_dir"
    ;;
esac

exit $result
