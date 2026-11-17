(*
  Tests for the Assert-based runtime checks of runtime_checkLib.
*)
Theory runtime_check_test
Ancestors
  holKernel runtime_check ml_translator
Libs
  preamble ml_translatorLib runtime_checkLib

val _ = register_type “:type”;
val _ = register_type “:term”;
val _ = register_type “:thm”;

Definition rc_test_def:
  rc_test (tm:term) (tys:(type # type) list) (s:mlstring) = (0:num)
End

val th = translate (assert_check [‘tm’,‘tys’,‘s’] rc_test_def);

val _ = null (hyp th) orelse failwith "assert_check retained a hypothesis";

val _ = length (find_terms (can (match_term “Assert e sa”))
                  (fetch "-" "rc_test_v_def" |> concl |> rhs)) = 3 orelse
        failwith "assert_check did not produce three Assert expressions";
