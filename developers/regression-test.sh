#!/bin/bash

set -e

echo "Running regression test on $(git log -1 --oneline --no-color)"
HOLDIR=$(heapname | xargs dirname) || exit $?
echo "HOL revision: $(cd $HOLDIR; git log -1 --oneline --no-color)"
echo "Machine: $(uname -nmo)"

status=$(git status 2> /dev/null)

if [[ ! ${status} =~ "working directory clean" ]]
then
    echo "WARNING: working directory is dirty!"
fi

cd $(dirname "$0")
source misc.sh
cd ..

case $(uname -a) in
  Linux* ) TIMECMD="/usr/bin/time -o timing.log -f '%U %M'";;
esac

echo

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
        printf '%0.*s' $((32 - ${#i})) "$pad"
        eval displayline $(cat timing.log)
      else
          echo
      fi
      if [ -x selftest.exe ]
      then
        if ./selftest.exe >> regression.log 2>&1
        then
          echo "OK: $i (selftest)"
        else
          echo "FAILED: $i (selftest)"
          exit 1
        fi
      fi
  else
      echo "FAILED: $i"
      exit 1
  fi
  popd > /dev/null 2>&1
done < developers/build-sequence
