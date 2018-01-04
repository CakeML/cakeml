#!/bin/sh

TIMEFORMAT=%R
for benchmark in ocamlc_*; do
  echo "$benchmark"
  for _ in $(seq 30)
  do
    time "./$benchmark"
  done
done

for benchmark in ocamlopt_*; do
  echo "$benchmark"
  for _ in $(seq 30)
  do
    time "./$benchmark"
  done
done
