#!/bin/bash
## A script that runs the regression test.

set -e

if [ -n "$bamboo_planRepository_integrationBranch_revision" ]
then
  echo "Running regression test on $(git log -1 --oneline --no-color ${bamboo_planRepository_revision})"
  echo "Merged ${bamboo_planRepository_branch} with $(git log -1 --oneline --no-color ${bamboo_planRepository_integrationBranch_revision})"
else
  echo "Running regression test on $(git log -1 --oneline --no-color)"
fi
HOLDIR=$(heapname | xargs dirname) || exit $?
echo "HOL revision: $(cd $HOLDIR; git log -1 --oneline --no-color)"
echo "Machine: $(uname -nmo)"

if [ -n "$(git status -z)" ]
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
  #save the current state
  if [ -n "$1" ]; then
      echo $i > $1;
  fi

  [[ $i == '#'* ]] || [[ -z $i ]] && continue
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
        printf '%0.*s' $((36 - ${#i})) "$pad"
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
