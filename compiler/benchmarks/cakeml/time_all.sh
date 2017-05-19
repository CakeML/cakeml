TIMEFORMAT=%R
for benchmark in cake_*; do
  echo $benchmark
  for i in `seq 30`
  do
    time ./$benchmark
  done
done
