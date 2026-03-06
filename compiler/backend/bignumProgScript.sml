(*
  Various programs written in bignumLang.
*)
Theory bignumProg
Ancestors
  bignumLang
Libs
  preamble
  bignumLangLib

Quote add = bignum:
  add(x,y) { return x + y; }
End
