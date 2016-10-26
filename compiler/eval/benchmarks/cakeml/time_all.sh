TIMEFORMAT=%R
for benchmark in cake_*; do
  echo $benchmark
  for i in `seq 10`
  do
    time ./$benchmark
  done
done
