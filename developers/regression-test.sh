#!/bin/bash

set -e

echo -n "Running regression test on "
git rev-parse --short HEAD
echo "HOL revision: $(cd $(heapname | xargs dirname); git rev-parse --short HEAD)"
echo -n "Machine: "
uname -nmo

status=$(git status 2> /dev/null)

if [[ ! ${status} =~ "working directory clean" ]]
then
    echo "WARNING: working directory is dirty!"
fi

cd $(dirname "$0")/..

case $(uname -a) in
    Linux* ) TIMECMD="/usr/bin/time -o timing.log -f 'User:%U Mem:%M'";;
esac

while read i
do
  if [ ! -d $i ]
  then
      echo "Ignoring non-existent directory $i"
      continue
  fi
  pushd $i > /dev/null 2>&1
  /bin/rm -f timing.log 2> /dev/null
  Holmake cleanAll &&
  if eval $TIMECMD Holmake > regression.log 2>&1
  then
      echo -n "OK: $i"
      if [ -f timing.log ]
      then
          echo -n " -- " ; cat timing.log
      else
          echo
      fi
  else
      echo "FAILED: $i"
      exit 1
  fi
  popd > /dev/null 2>&1
done < developers/build-sequence
