// TODO Fix depends on https://github.com/dafny-lang/dafny/issues/5739
method Main() {
  print ("ab", ghost "ab"), "\n";
}
