open preamble;
open libTheory astTheory evaluateTheory semanticPrimitivesTheory;
open semanticsTheory;
open semanticPrimitivesPropsTheory;
open evaluateComputeLib;
open primTypesTheory;
open typeSystemTheory;
open typeSoundInvariantsTheory;
open namespaceTheory;
open namespacePropsTheory;
open typeSysPropsTheory;
open terminationTheory;

val _ = new_theory "primSemEnv";

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
``add_to_sem_env (<| clock := 0; ffi := ffi; refs := [];
                     next_exn_stamp := 0; next_type_stamp := 0; |>,
                  <| c := nsEmpty; v := nsEmpty |>)
                 prim_types_program``
  |> SIMP_CONV(srw_ss())[add_to_sem_env_def, prim_types_program_def]
  |> CONV_RULE evaluate_conv
  |> (fn th => let
        val pth = SPEC_ALL prim_sem_env_def
        val th1 = mk_eq(rhs(concl pth),lhs(concl th)) |> EVAL |> EQT_ELIM
        in TRANS (TRANS pth th1) th end));

val prim_tenv_def = Define`
  prim_tenv =
    <| c := alist_to_ns (REVERSE
          [("Bind", ([],[],Texn_num));
           ("Chr", ([],[],Texn_num));
           ("Div", ([],[],Texn_num));
           ("Subscript", ([],[],Texn_num));
           ("false", ([],[], Tbool_num));
           ("true", ([],[], Tbool_num));
           ("nil", (["'a"],[],Tlist_num));
           ("::", (["'a"],[Tvar "'a"; Tlist (Tvar "'a")], Tlist_num));
           ("NONE", (["'a"],[],Toption_num));
           ("SOME", (["'a"],[Tvar "'a"], Toption_num))]);
       v := nsEmpty;
       t := nsEmpty|>`;

val prim_type_sound_invariants = Q.store_thm("prim_type_sound_invariants",
  `!type_ids sem_st prim_env.
   (sem_st,prim_env) = THE (prim_sem_env ffi) ∧
   DISJOINT type_ids {Tlist_num; Tbool_num; Toption_num; Texn_num}
   ⇒
   ?ctMap.
     type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv`,
  rw[type_sound_invariant_def, prim_sem_env_eq, prim_tenv_def] >>
  qexists_tac`FEMPTY |++ REVERSE [
      (bind_stamp, ([],[],Texn_num));
      (div_stamp, ([],[],Texn_num));
      (chr_stamp, ([],[],Texn_num));
      (subscript_stamp, ([],[],Texn_num));
      (TypeStamp "nil" list_type_num, (["'a"],[],Tlist_num));
      (TypeStamp "::" list_type_num, (["'a"],[Tvar "'a"; Tlist (Tvar "'a")], Tlist_num));
      (TypeStamp "true" bool_type_num, ([],[], Tbool_num));
      (TypeStamp "false" bool_type_num, ([],[], Tbool_num));
      (TypeStamp "SOME" option_type_num, (["'a"],[Tvar "'a"], Toption_num));
      (TypeStamp "NONE" option_type_num, (["'a"],[],Toption_num))]` >>
  rw []
  >- (
    simp [tenv_ok_def, tenv_ctor_ok_def] >>
    rpt (
      irule nsAll_nsBind >>
      rw [check_freevars_def]))
  >- (
    simp [good_ctMap_def, ctMap_ok_def, flookup_fupdate_list] >>
    EVAL_TAC >>
    rw [] >>
    rw [same_type_def] >>
    rw [FEVERY_FUPDATE, check_freevars_def, FEVERY_FEMPTY])
  >- (
    rw [consistent_ctMap_def] >>
    fs [FDOM_FUPDATE_LIST, option_type_num_def, bool_type_num_def,
        list_type_num_def, subscript_stamp_def, chr_stamp_def, div_stamp_def,
        bind_stamp_def] >>
    simp [DISJOINT_DEF, EXTENSION, IN_FRANGE_FLOOKUP, FLOOKUP_o_f,
         flookup_fupdate_list] >>
    CCONTR_TAC >>
    fs [] >>
    every_case_tac >>
    rw [] >>
    fs [])
  >- (
    simp [type_all_env_def, GSYM namespaceTheory.nsEmpty_def,
          GSYM namespaceTheory.nsBind_def] >>
    rpt (
      irule nsAll2_nsBind >>
      rw [type_ctor_def, flookup_fupdate_list, bind_stamp_def, div_stamp_def,
          chr_stamp_def, subscript_stamp_def, option_type_num_def,
          bool_type_num_def, list_type_num_def]))
  >- simp [type_s_def, store_lookup_def]);

(* TODO: rename semantics and call semantics_init semantics instead? *)
val semantics_init_def = Define`
  semantics_init ffi =
    semantics <| sem_st := FST(THE (prim_sem_env ffi));
                 sem_env := SND(THE (prim_sem_env ffi));
                 tenv := prim_tenv |>`;

val _ = export_theory ();
