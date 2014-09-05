pad=$(printf '%0.1s' "."{1..40})

function displaytime() {
  local T=${1%.*}
  local H=$((T/60/60))
  local M=$((T/60%60))
  local S=$((T%60))
  [[ $H > 0 ]] && printf '%dh' $H
  [[ $M > 0 ]] && printf '%dm' $M
  printf '%ds' $S
}

function displaymem() {
  local T=$1
  local G=$((T/1000/1000))
  local M=$((T/1000))
  if [[ $G > 0 ]]
  then
    printf '%dGB' $G
  elif [[ $M > 0 ]]
  then
    printf '%dMB' $M
  else
    printf '%dkB' $T
  fi
}

function displayline() {
  local U=$1
  local M=$2
  printf '%5s %8s\n' $(displaymem $M) $(displaytime $U)
}
