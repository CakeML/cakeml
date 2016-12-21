TIMEFORMAT=%R
for benchmark in polyc_*; do
  echo $benchmark
  for i in `seq 30`
  do
    time ./$benchmark
  done
done
for benchmark in mlton_*; do
  echo $benchmark
  for i in `seq 30`
  do
    time ./$benchmark
  done
done
