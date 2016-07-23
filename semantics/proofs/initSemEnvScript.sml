open preamble;
open libTheory astTheory evaluateTheory semanticPrimitivesTheory initialProgramTheory;
open semanticsTheory;
open semanticPrimitivesPropsTheory;
open evaluateComputeLib;
open terminationTheory;
open boolSimps;

val _ = new_theory "initSemEnv";

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
``add_to_sem_env (<| clock := 0; ffi := ffi; refs := []; defined_types := {}; defined_mods := {} |>,
                  <| m := []; c := ([],[]); v := [] |>)
                 prim_types_program``
  |> SIMP_CONV(srw_ss())[add_to_sem_env_def, prim_types_program_def]
  |> CONV_RULE evaluate_conv
  |> (fn th => let
        val pth = SPEC_ALL prim_sem_env_def
        val th1 = mk_eq(rhs(concl pth),lhs(concl th)) |> EVAL |> EQT_ELIM
        in TRANS (TRANS pth th1) th end));

(* Too big to evaluate in a reasonable timely was due to exponential explosion in closure envs
val basis_sem_env_eq = save_thm ("basis_sem_env_eq",
  ``basis_sem_env ffi``
  |> SIMP_CONV(srw_ss())[basis_sem_env_def,add_to_sem_env_def,basis_program_def, mk_binop_def, mk_unop_def, prim_sem_env_eq]
  |> CONV_RULE evaluate_conv
  *)


(* recursively decend into the test position of case expressions and apply to conversion to the inner-most *)
fun CASE_CONV conv tm =
let
  fun CASE_CONV0 tm =
    if TypeBase.is_case tm then
      let
        val (case_const, (test::rest)) = strip_comb tm
      in
        List.foldl (fn (a,th) => AP_THM th a) (AP_TERM case_const (CASE_CONV0 test)) rest
      end
    else
      conv tm
in
  if TypeBase.is_case tm then
    CASE_CONV0 tm
  else
    raise UNCHANGED
end;

val basis_sem_env_SOME = Q.store_thm ("basis_sem_env_SOME",
`?se. basis_sem_env ffi = SOME se`,
 cheat);

(*
val lemma = Q.prove (
`merge_alist_mod_env new_ctors' ([],[]) = new_ctors' ∧
 ((case r of
        Rval (menv',env') => Rval (menv',env')
      | Rerr e => Rerr e) = r) ∧
 (( case x of (a,b,c) => (a,b,c)) = x) `,
 Cases_on `new_ctors'` >>
 rw [merge_alist_mod_env_def]
 >- (
   Cases_on `r`
   >> rw []
   >> split_pair_case_tac
   >> fs [])
 >- (
   split_pair_case_tac
   >> fs []));


fun do1_tac t =
  (REWRITE_TAC [Once evaluate_tops_def] >>
   CONV_TAC (RAND_CONV (LHS_CONV (CASE_CONV evaluate_conv))) >>
   simp [extend_top_env_def, extend_dec_env_def, combine_dec_result_def,
         merge_alist_mod_env_def,pmatch_def, pat_bindings_def,
         combine_mod_result_def, lemma]) t;

val basis_sem_env_SOME = Q.store_thm ("basis_sem_env_SOME",
`?se. basis_sem_env ffi = SOME se`,
 simp [basis_sem_env_def]
 >> Cases_on `THE (prim_sem_env ffi)`
 >> simp [add_to_sem_env_def]
 >> split_pair_case_tac
 >> simp []
 >> pop_assum mp_tac
 >> simp [basis_program_def, evaluate_prog_def, no_dup_mods_def,
          prog_to_mods_def, no_dup_top_types_def, prog_to_top_types_def,
          decs_to_types_def, mk_binop_def, mk_unop_def]
 >> rw []
 >- (
   qpat_assum `evaluate_tops _ _ _ = _` mp_tac
   >> simp [mk_ffi_def]
   >> Cases_on `v7`
   >> simp []
   >- (Cases_on `a`
       >> simp [])
   (do1_tac >> TRY (Q.PAT_ABBREV_TAC`cl = (X0,Closure X Y Z)`))

 >- (
   fs [prim_sem_env_eq]
   >> rw []
   >> fs [])

 >> split_pair_case_tac
 >> rw []
 >> fs [basis_program_def, evaluate_prog_def]
 >> rw []
 >> pop_assum mp_tac
 >> rw []
 >- (ntac 2 (pop_assum kall_tac) >>
     simp ([mk_ffi_def, mk_binop_def, mk_unop_def, Once run_eval_prog_def, run_eval_top_def, run_eval_dec_def,
            merge_alist_mod_env_def,pmatch_def, pat_bindings_def]) >>
     rpt (do1_tac >> TRY (Q.PAT_ABBREV_TAC`cl = (X0,Closure X Y Z)`)))
 >- (fs [] >>
     pop_assum mp_tac >>
     match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
     rw [basis_program_def, mk_binop_def, mk_unop_def] >>
     CONV_TAC evaluate_conv));
     *)

val prim_tdecs_def = Define
  `prim_tdecs =
    <|defined_mods := {};
      defined_exns :=
        {Short"Subscript"
        ;Short"Div"
        ;Short"Chr"
        ;Short"Bind"};
      defined_types :=
        {Short"option"
        ;Short"list"
        ;Short"bool"}|>`;

val prim_tenv_def = Define`
  prim_tenv = <|c := ([],[]); m := FEMPTY; v := Empty; t := (FEMPTY,FEMPTY)|>`;

(* TODO: rename semantics and call semantics_init semantics instead? *)
val semantics_init_def = Define`
  semantics_init ffi =
    semantics <| sem_st := FST(THE (prim_sem_env ffi));
                 sem_env := SND(THE (prim_sem_env ffi));
                 tdecs := prim_tdecs;
                 tenv := prim_tenv |>`;

val _ = export_theory ();
