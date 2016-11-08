TIMEFORMAT=%R
for benchmark in ocamlc_*; do
  echo $benchmark
  for i in `seq 10`
  do
    time ./$benchmark
  done
done

for benchmark in ocamlopt_*; do
  echo $benchmark
  for i in `seq 10`
  do
    time ./$benchmark
  done
done
