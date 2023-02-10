#!/bin/bash

# exit when any command fails
set -e
# keep track of the last executed command
trap 'last_command=$current_command; current_command=$BASH_COMMAND' DEBUG
# echo an error message before exiting
trap 'echo "\"${last_command}\" command filed with exit code $?."' EXIT

LBR=$'\n'
TIMES=""
AVG=0.0

#define some functions:
function run () {
    #First get raw running time data
    TIME1="$( { /usr/bin/time -f "%e" -a $1 $2 $3 $4 $5 $6 $7 $8 $9 ${10}; } 2>&1)"
    TIME2="$( { /usr/bin/time -f "%e" -a $1 $2 $3 $4 $5 $6 $7 $8 $9 ${10}; } 2>&1)"
    TIME3="$( { /usr/bin/time -f "%e" -a $1 $2 $3 $4 $5 $6 $7 $8 $9 ${10}; } 2>&1)"
    #Append it to the CSV line
    TIMES="$TIMES, $TIME1, $TIME2, $TIME3"
    CURRAVG=$(echo "$TIME1 $TIME2 $TIME3" | awk '{print (($1+$2+$3)/3); exit}')
    AVG=$(echo "$AVG $CURRAVG" | awk '{print ($1 + $2)}')
    #Print average to stdout for current file
    #echo "$1 $TIME1 $TIME2 $TIME3" | awk ' {print $1 "\t|" (($2+$3+$4)/3); exit}'
}

mkdir -p 1_results 2_results 3_results 4_results 6_results 8_results 9_results

export CAKEFLAGS="--sexp=true --target=x64"

for f in $(ls ./1/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./2/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./3/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./4/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./6/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./8/*.sexp.cml); do make ${f/cml/cake.S}; done
for f in $(ls ./9/*.sexp.cml); do make ${f/cml/cake.S}; done

echo "Cleaning up stale files"
rm -rf 1/*.cml 2/*.cml 3/*.cml 4/*.cml 6/*.cml 8/*.cml 9/*.cml

echo "Compiling FFI"
cc -c basis_ffi.c -o basis_ffi.o

echo "Compiling benchmarks"

for f in $(ls ./1)
do
  cc 1/$f basis_ffi.o -o "1_results/${f%cake.S}cake"
done

for f in $(ls ./2)
do
  cc 2/$f basis_ffi.o -o "2_results/${f%cake.S}cake"
done

for f in $(ls ./3)
do
  cc 3/$f basis_ffi.o -o "3_results/${f%cake.S}cake"
done

for f in $(ls ./4)
do
  cc 4/$f basis_ffi.o -o "4_results/${f%cake.S}cake"
done

for f in $(ls ./6)
do
  cc 6/$f basis_ffi.o -o "6_results/${f%cake.S}cake"
done

for f in $(ls ./8)
do
  cc 8/$f basis_ffi.o -o "8_results/${f%cake.S}cake"
done

for f in $(ls ./9)
do
  cc 9/$f basis_ffi.o -o "9_results/${f%cake.S}cake"
done

echo "Compilation done, starting performance eval"

export CML_HEAP_SIZE=100
export CML_STACK_SIZE=100

for f in $(ls ./1_results)
do
  TIMES="$TIMES$f"
  run 1_results/$f 4593671619917905920
  run 1_results/$f 4612811918334230528
  run 1_results/$f 4614951128157231514
  run 1_results/$f 13834562659323152957
  run 1_results/$f 4621509495114589798
  #Print average to stdout for current file
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./2_results)
do
  TIMES="$TIMES$f"
  run 2_results/$f 4593671619917905920 4620130267728707584
  run 2_results/$f 4612811918334230528 4594103965482133488
  run 2_results/$f 4614951128157231514 4622320143047516488
  run 2_results/$f 4611190622468377149 13843446009588141261
  run 2_results/$f 4621509495114589798 4594031907888095560
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./3_results)
do
  TIMES="$TIMES$f"
  run 3_results/$f 4593671619917905920 4620130267728707584 4626322717216342016
  run 3_results/$f 4612811918334230528 4594103965482133488 4625267186053677056
  run 3_results/$f 4614951128157231514 4622320143047516488 4623693740933864489
  run 3_results/$f 4611190622468377149 13843446009588141261 4621064764651386962
  run 3_results/$f 4621509495114589798 4594031907888095560 4616583683022153318
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./4_results)
do
  TIMES="$TIMES$f"
  run 4_results/$f 4593671619917905920 4620130267728707584 4626322717216342016 4612811918334230528
  run 4_results/$f 4612811918334230528 4594103965482133488 4625267186053677056 4593671619917905920
  run 4_results/$f 4614951128157231514 4622320143047516488 4623693740933864489 4621509495114589798
  run 4_results/$f 4611190622468377149 13843446009588141261 4621064764651386962 4614951128157231514
  run 4_results/$f 4621509495114589798 4594031907888095560 4616583683022153318 4611190622468377149
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./6_results)
do
  TIMES="$TIMES$f"
  run 6_results/$f 4593671619917905920 4620130267728707584 4626322717216342016 4612811918334230528 4616583683022153318 13843446009588141261
  run 6_results/$f 4612811918334230528 4594103965482133488 4625267186053677056 4593671619917905920 4614951128157231514 4623693740933864489
  run 6_results/$f 4614951128157231514 4622320143047516488 4623693740933864489 4621509495114589798 13849694754071117824 4593671619917905920
  run 6_results/$f 4611190622468377149 13843446009588141261 4621064764651386962 4614951128157231514 4594103965482133488 4612451630364040888
  run 6_results/$f 4621509495114589798 4594031907888095560 4616583683022153318 4611190622468377149 4620332929711939256 4625407923542032384
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./8_results)
do
  TIMES="$TIMES$f"
  run 8_results/$f 4593671619917905920 4620130267728707584 4626322717216342016 4612811918334230528 4616583683022153318 13843446009588141261 4622320143047516488 4623693740933864489
  run 8_results/$f 4612811918334230528 4594103965482133488 4625267186053677056 4593671619917905920 4614951128157231514 4623693740933864489 13843446009588141261 4621064764651386962
  run 8_results/$f 4614951128157231514 4622320143047516488 4623693740933864489 4621509495114589798 13849694754071117824 4593671619917905920 4620332929711939256 4625407923542032384
  run 8_results/$f 4611190622468377149 13843446009588141261 4621064764651386962 4614951128157231514 4594103965482133488 4612451630364040888 4625267186053677056 4593671619917905920
  run 8_results/$f 4621509495114589798 4594031907888095560 4616583683022153318 4611190622468377149 4620332929711939256 4625407923542032384 4626415603958656532 4612811918334230528
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

for f in $(ls ./9_results)
do
  TIMES="$TIMES$f"
  run 9_results/$f 4593671619917905920 4620130267728707584 4626322717216342016 4612811918334230528 4616583683022153318 13843446009588141261 4622320143047516488 4623693740933864489 4617034042984890368
  run 9_results/$f 4612811918334230528 4594103965482133488 4625267186053677056 4593671619917905920 4614951128157231514 4623693740933864489 13843446009588141261 4621064764651386962 4620445519702623519
  run 9_results/$f 4614951128157231514 4622320143047516488 4623693740933864489 4621509495114589798 13849694754071117824 4593671619917905920 4620332929711939256 4625407923542032384 4621678380100616192
  run 9_results/$f 4611190622468377149 13843446009588141261 4621064764651386962 4614951128157231514 4594103965482133488 4612451630364040888 4625267186053677056 4593671619917905920 4608793806746690571
  run 9_results/$f 4621509495114589798 4594031907888095560 4616583683022153318 4611190622468377149 4620332929711939256 4625407923542032384 4626415603958656532 4612811918334230528 4618367108474592035
  echo "$f $AVG" | awk '{print $1 "\t|" (($2)/5); exit}'
  AVG=0
  TIMES="$TIMES$LBR"
done

echo $TIMES | sort -o times.csv
