(*
  TODO: document
*)
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
``add_to_sem_env (<| clock := 0; ffi := (ffi:'ffi ffi_state); refs := [];
                     next_exn_stamp := 0; next_type_stamp := 0;
                     fp_state := <| rws := []; opts := no_fp_opts; canOpt := F; choices := 0; assertions := no_assertions|> |>,
                  <| c := nsEmpty; v := nsEmpty |>)
                 prim_types_program``
  |> SIMP_CONV(srw_ss())[add_to_sem_env_def, prim_types_program_def]
  |> CONV_RULE evaluate_conv
  |> (fn th => let
        val pth = SPEC_ALL prim_sem_env_def
        val th1 = mk_eq(rhs(concl pth),lhs(concl th)) |> EVAL |> EQT_ELIM
        in TRANS (TRANS pth th1) th end));

Theorem prim_type_sound_invariants:
   !type_ids sem_st prim_env fp_st.
   (sem_st, prim_env) = THE (prim_sem_env ffi) ∧
   DISJOINT type_ids {Tlist_num; Tbool_num; Texn_num}
   ⇒
   ?ctMap.
     type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv ∧
     FRANGE ((SND o SND) o_f ctMap) ⊆ prim_type_ids
Proof
  rw[type_sound_invariant_def, prim_sem_env_eq, prim_tenv_def] >>
  qexists_tac`FEMPTY |++ REVERSE [
      (bind_stamp, ([],[],Texn_num));
      (div_stamp, ([],[],Texn_num));
      (chr_stamp, ([],[],Texn_num));
      (subscript_stamp, ([],[],Texn_num));
      (TypeStamp "[]" list_type_num, (["'a"],[],Tlist_num));
      (TypeStamp "::" list_type_num, (["'a"],[Tvar "'a"; Tlist (Tvar "'a")], Tlist_num));
      (TypeStamp "True" bool_type_num, ([],[], Tbool_num));
      (TypeStamp "False" bool_type_num, ([],[], Tbool_num))]` >>
  rw []
  >- (
    simp [tenv_ok_def, tenv_ctor_ok_def, tenv_abbrev_ok_def]>>
    rw[] >>
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
    fs [FDOM_FUPDATE_LIST, bool_type_num_def,
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
          chr_stamp_def, subscript_stamp_def,
          bool_type_num_def, list_type_num_def]))
  >- simp [type_s_def, store_lookup_def]
  >- (
    simp[SUBSET_DEF]
    \\ ho_match_mp_tac IN_FRANGE_o_f_suff
    \\ ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff
    \\ simp[]
    \\ EVAL_TAC
    \\ rpt strip_tac \\ rveq
    \\ EVAL_TAC)
QED

val _ = export_theory ();
