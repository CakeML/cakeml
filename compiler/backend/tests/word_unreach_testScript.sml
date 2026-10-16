(*
  Tests for removal of unreachable wordLang code.
*)
Theory word_unreach_test[no_sig_docs]
Ancestors
  word_unreach
Libs
  preamble

Theorem remove_unreach_test[local]:
  remove_unreach (Seq (Move 1 [(1,11);(2,22);(3,33)])
                      (Move 1 [(3,1);(2,99)]))
  =
  Move 1 [(3,11); (2,99); (1,11)]
Proof
  EVAL_TAC
QED
