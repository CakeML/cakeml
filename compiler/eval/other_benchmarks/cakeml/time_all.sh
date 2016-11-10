TIMEFORMAT=%R
for benchmark in cake_*; do
  echo $benchmark
  for i in `seq 5`
  do
    time ./$benchmark
  done
done

