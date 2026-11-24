(*
  A test showing that the monadic translator turns assert_shape checks
  (placed with pure_seq) into Assert expressions.
*)
Theory assert_shapeProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

val state_type = ``:unit``;

Datatype:
  state_exn = Fail string
End

val config = global_state_config |>
             with_exception ``:state_exn``;

Overload failwith = ``raise_Fail``

Definition check_args_def:
  check_args (n:num) (xs:(int # mlstring) list) =
    pure_seq (assert_shape (PrimA IntT) n)
      (pure_seq (assert_shape (ListA (TupleA [PrimA IntT; PrimA StrT])) xs)
        (if n = 0 then failwith "zero" else return n))
End

val _ = start_translation config;

val check_args_v_thm = check_args_def |> m_translate;

val _ = null (hyp check_args_v_thm) orelse
        failwith "m_translate of assert_shape retained a hypothesis";

val _ = length (find_terms (can (match_term “Assert e sa”))
                  (fetch "-" "check_args_v_def" |> concl |> rhs)) = 2 orelse
        failwith "m_translate did not produce two Assert expressions";
