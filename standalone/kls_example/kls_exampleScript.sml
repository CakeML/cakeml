(*
NEW BRANCH: cenv_close

git clone -b cenv_close https://github.com/xrchz/vml.git
*)

(*---------------------------------------------------------------------------*)
(* Adapted from bootstrap/compilereplDecsScript.sml                          *)
(*                                                                           *)
(* Build note:                                                               *)
(* HOL process should run in vml/standalone/, in order to get the goodness   *)
(* that stems from being there, e.g., heap and loadPath set up properly.     *)
(*---------------------------------------------------------------------------*)

max_print_depth := 0;
max_print_depth := ~1;

open arithmeticTheory listTheory combinTheory pairTheory;
open cakeml_computeLib

(*
use "eval_compset";
*)

(*
open preamble 
     flookupLib
     replDecsTheory 
     replDecsProofsTheory;
load "../metatheory/interpTheory";

*)

(*
loadPath := !loadPath @ ["../translator"];
*)

open ml_translatorLib ml_translatorTheory evalPropsTheory;

open compilerProofTheory initialProgramTheory bigClockTheory;


fun type_info ty =  (* utility for looking up type information *)
 let open TypeBasePure 
     val SOME tyinfo = TypeBase.fetch ty
 in {constructors = constructors_of tyinfo,
     fields = fields_of tyinfo, 
     theory_defined_in = #Thy (dest_thy_type ty)}
 end;


val _ = new_theory "kls_example";

(*---------------------------------------------------------------------------*)
(* Basic example to be pushed through the compiler                           *)
(*---------------------------------------------------------------------------*)

val fact_def = 
 Define
  `fact (n:num) = if n <= 1 then 1 else n * fact(n-1)`;

(*---------------------------------------------------------------------------*)
(* Property to be pushed through the compiler                                *)
(*---------------------------------------------------------------------------*)

val fact_lem = Q.prove
(`!n. 0 < fact n`,
 recInduct (fetch "-" "fact_ind") THEN 
 REPEAT STRIP_TAC THEN
 RW_TAC arith_ss [Once fact_def,ZERO_LESS_MULT]);

val it_def = Define `it = fact 5`;

(*---------------------------------------------------------------------------*)
(* Translate the function into exp form.                                     *)
(*---------------------------------------------------------------------------*)

val res = translate fact_def;
val res1 = translate it_def;

val () = finalise_translation();

val kls_example_decls_def = fetch "-" "kls_example_decls";

val th = fetch "-" "kls_example_translator_state_thm";

val klsDeclAssumExists = Q.prove
(`DeclAssumExists kls_example_decls`,
ASSUME_TAC th THEN
FULL_SIMP_TAC (srw_ss()) [markerTheory.Abbrev_def,ml_translatorTheory.TAG_def]);

val evaluate_decs_exists =
 klsDeclAssumExists |> SIMP_RULE std_ss [DeclAssumExists_def,DeclAssum_def,Decls_def];

val (fact_eval,_) = get_cert "fact";  (* same as res .... *)

val fact_eval_thm = SIMP_RULE std_ss [] (DISCH_ALL fact_eval);

val Eval_fact_app = Q.prove
(`Eval env (Var (Short "n")) (NUM n) /\
  DeclAssum kls_example_decls env tys
  ==>
  Eval env
      (App Opapp (Var (Short "fact"))
                 (Var (Short "n")))
     (NUM (fact n))`,
 METIS_TAC [fact_eval_thm, Eval_Arrow]);

val Eval_Var_lemma = prove(
  ``(lookup name (all_env_to_env env) = SOME x) /\ P x ==> Eval env (Var (Short name)) P``,
  REPEAT STRIP_TAC THEN
  PairCases_on`env` THEN
  FULL_SIMP_TAC (srw_ss())
    [Eval_def, Once evaluate_cases,lookup_var_id_def,all_env_to_env_def]);

val ML_fact_CORRECT = store_thm
("ML_fact_CORRECT",
 ``!env tys n nml.
      DeclAssum kls_example_decls env tys /\
      (NUM n nml) /\ (lookup "n" (all_env_to_env env) = SOME nml)
      ==>
      ?k kml.
        evaluate F
           env (0,empty_store)
           (App Opapp
               (Var (Short "fact"))
               (Var (Short "n")))
           ((0,empty_store), Rval kml)
         /\ NUM k kml /\ 0 < k``,
 METIS_TAC [Eval_Var_lemma,Eval_fact_app,fact_lem,Eval_def]);

(*---------------------------------------------------------------------------*)
(* Same as ML_fact_CORRECT, but phrased in terms of Eval instead of evaluate'*)
(*---------------------------------------------------------------------------*)

val ML_fact_THM = store_thm
("ML_fact_THM",
 ``!env tys n nml.
      DeclAssum kls_example_decls env tys /\
     (lookup "n" (all_env_to_env env) = SOME nml)/\
      NUM n nml
      ==>
      ?k.
        Eval env
            (App Opapp
                (Var (Short "fact"))
                (Var (Short "n")))
         (\kml. NUM k kml /\ 0 < k)``,
 REPEAT STRIP_TAC THEN Q.EXISTS_TAC `fact n` THEN
 SIMP_TAC std_ss [fact_lem] THEN
 METIS_TAC [Eval_Var_lemma,Eval_fact_app,Eval_def]);

(*---------------------------------------------------------------------------*)
(* Evaluate the compiler                                                     *)
(*---------------------------------------------------------------------------*)

val (foo,_) = get_cert "it"
val th1 = klsDeclAssumExists |> REWRITE_RULE[DeclAssumExists_def] |> SIMP_RULE std_ss [Ntimes EXISTS_PROD 2]
val results_def = new_specification("results",["kls_menv","kls_cenv","kls_env","kls_tys"],th1)
val th2 = MATCH_MP (DISCH_ALL foo) results_def
val th3 = th2 |> REWRITE_RULE[Eval_def]
  |> SIMP_RULE(srw_ss())[Once evaluate_cases,lookup_var_id_def,NUM_def,INT_def]

val kls_decs = results_def |> SIMP_RULE (srw_ss())[DeclAssum_def,Decls_def]
val intermediates_def = new_specification("intermediates",["int_s","int_new_tds","int_res_env"],kls_decs)
val int1_def = intermediates_def |> CONJUNCT1
val int2_def = MATCH_MP decs_add_clock int1_def |> SIMP_RULE (srw_ss())[]
val kls_init_clock_def = new_specification("kls_init_clock",["kls_init_clock"],int2_def)
val kls_progs = kls_init_clock_def |> SIMP_RULE(srw_ss())[evaluate_decs_evaluate_prog_MAP_Tdec]

val option_case_lemma = prove(
  ``((case x of NONE => NONE | SOME x => SOME x) = SOME z) ⇔ (x = SOME z)``,
  BasicProvers.EVERY_CASE_TAC)

val lookup_int_res_env =
  th3 |> SIMP_RULE std_ss [
    last(CONJUNCTS intermediates_def)
    |> SIMP_RULE std_ss [merge_def],
    libPropsTheory.lookup_append]
  |> SIMP_RULE(srw_ss())[initialEnvTheory.init_env_def,option_case_lemma]

val closed_prog_kls =
``closed_prog (MAP Tdec kls_example_decls)``
  |> (REWRITE_CONV[kls_example_decls_def] THENC cakeml_computeLib.eval)

val kls_compiler_correctness =
    compile_prog_thm
  |> C MATCH_MP kls_progs
  |> SIMP_RULE(srw_ss()) [closed_prog_kls]
  |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> SIMP_RULE (srw_ss())[LET_THM,lookup_int_res_env]
  |> SIMP_RULE (srw_ss())[replTheory.print_v_def,replTheory.print_lit_def]
  |> CONV_RULE (RESORT_FORALL_CONV List.rev)
  |> Q.SPECL[`initial_bc_state.code`,`install_code (compile_prog (MAP Tdec kls_example_decls)) initial_bc_state`]

val computed_bytecode =
  ``code_labels (\x. 0) (compile_prog (MAP Tdec kls_example_decls))``
  |> (REWRITE_CONV[kls_example_decls_def] THENC cakeml_computeLib.eval)

(*
val encoded =``(MAP bc_inst_to_string ^(rhs(concl computed_bytecode)))``
  |> cakeml_computeLib.eval
  ``(encode_num 10):(word64 option)``|>cakeml_computeLib.eval
*)
