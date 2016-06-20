for src in benchmark*.S ; do
  BNAME=${src%%.S}
  echo $BNAME
  gcc $src -g -o $BNAME
	objdump $BNAME -M intel -d > "${BNAME}_dump.txt"
	time ./$BNAME
  echo "returned $?"
done
