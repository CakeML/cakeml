(*
  Examples of pointer equality in a global-state monad, translated with
  ml_monad_oracleLib and evaluated under different source oracles.
*)
Theory monadic_ptr_eq
Ancestors
  ml_monad_oracle ml_monadBase
Libs
  preamble ml_monad_oracleLib

val _ = ml_monad_translator_interfaceLib.set_up_monadic_translator ();

(* The state carries the logical oracle that models the source PtrEq oracle *)
Datatype:
  ptr_state = <| oracle : num -> bool; count : num |>
End

Overload same_ptr =
  “Mptr_eq ptr_state_oracle (λoracle s. s with oracle := oracle)”

Theorem ptr_oracle_accessors:
  ORACLE_ACCESSORS ptr_state_oracle (λoracle s. s with oracle := oracle)
    ((λs. emp):ptr_state -> hprop, p:'ffi ffi_proj)
Proof
  simp [ORACLE_ACCESSORS_def]
QED

val _ = start_oracle_translation ptr_oracle_accessors;
val _ = ml_translatorLib.register_type “:bool # bool”;
val _ = ml_translatorLib.register_type “:num list”;

(* Each test consumes its own oracle choice, so the results can differ *)
Definition ptr_twice_def:
  ptr_twice (x:num) y =
    do
      first <- same_ptr x y;
      second <- same_ptr x y;
      return (first, second)
    od
End

(* A retry after a failed test uses the next oracle choice *)
Definition ptr_retry_def:
  ptr_retry (x:num) y =
    do
      same <- same_ptr x y;
      if same then return T else same_ptr x y
    od
End

(* Compound values use the ordinary translator's refinements *)
Definition ptr_list_def:
  ptr_list (xs:num list) ys = same_ptr xs ys
End

val ptr_twice_v_thm = oracle_translate ptr_twice_def;
val ptr_retry_v_thm = oracle_translate ptr_retry_def;
val ptr_list_v_thm = oracle_translate ptr_list_def;

(* Running the logical model leaves the other state fields unchanged *)
Theorem ptr_twice_model:
  ptr_twice 7 7 <| oracle := (λi. i = 0); count := 42 |> =
    (M_success (T,F), <| oracle := (λi. F); count := 42 |>)
Proof
  simp [ptr_twice_def, Mptr_eq_def, st_ex_bind_def, st_ex_return_def,
        FUN_EQ_THM]
QED

(* Evaluate the generated code on integer arguments, where the source oracle
   gives the listed answers to successive PtrEq tests and F afterwards *)
fun source_run def args answers = let
  val code = translate_definition def |> concl |> rator |> rand
  fun int n = intSyntax.term_of_int (Arbint.fromInt n)
  val call = foldl (fn (n,f) => “App Opapp [^f; Lit (IntLit ^(int n))]”)
               code args
  val bs = listSyntax.mk_list (map (fn b => if b then T else F) answers, bool)
  in
    “evaluate (empty_state with <| clock := 10;
                 ptr_eq_oracle := λepoch i. i < LENGTH ^bs ∧ EL i ^bs |>)
       empty_env [^call]”
  end;

fun assert_eval tm =
  EQT_ELIM ((REWRITE_CONV [ml_progTheory.write_def,
                           ml_progTheory.empty_env_def] THENC EVAL) tm);

(* The first or the second test succeeds, depending on the oracle *)
val r = source_run ptr_twice_def [7,7] [true,false];
val _ = assert_eval “SND ^r = Rval [Conv NONE [Boolv T; Boolv F]]”;

val r = source_run ptr_twice_def [7,7] [false,true];
val _ = assert_eval “SND ^r = Rval [Conv NONE [Boolv F; Boolv T]]”;

(* Unequal operands give F, but still consume oracle choices *)
val r = source_run ptr_twice_def [7,8] [true,true,false];
val _ = assert_eval “SND ^r = Rval [Conv NONE [Boolv F; Boolv F]] ∧
                     ¬(FST ^r).ptr_eq_oracle 0 0”;

(* The retry succeeds when the second oracle choice is T *)
val r = source_run ptr_retry_def [7,7] [false,true,false];
val _ = assert_eval “SND ^r = Rval [Boolv T] ∧
                     ¬(FST ^r).ptr_eq_oracle 0 0”;
