(*
  A data-cost example of a list sum function using fold
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;

open preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "allProg"

val _ = reset_translation();

(* List *)
val _ = ml_prog_update (open_module "List");

val result = translate FOLDL;

val _ = ml_prog_update (close_module NONE);

Definition all_def:
  all l = FOLDL (λa b. a /\ b) T l
End

val _ = translate all_def;

val maincall = process_topdecs `val _ = all [True,False,True,True,False]`

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

local
  val prog = get_prog(get_ml_prog_state())
in
  val all = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem all_prog_def = mk_abbrev "all_prog" all;

val _ = intermediate_prog_prefix := "all_";
Theorem all_thm = compile_x64 "all" (REFL all);
val _ = intermediate_prog_prefix := "";

val all_data_code_def       = definition"all_data_prog_def"
val all_to_data_thm         = theorem"all_to_data_thm"
val all_config_def          = definition"all_config_def"
val all_x64_conf            = (rand o rator o lhs o concl) all_thm
val all_x64_conf_def        = mk_abbrev"all_x64_conf" all_x64_conf
Theorem all_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) all_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) all_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem all_data_code_def = all_data_code_def;

Theorem data_safe_sum:
   ∀ffi.
  backend_config_ok ^all_x64_conf
  ⇒ is_safe_for_space ffi
       all_x64_conf
       all_prog
       (* (s_size,h_size) *)
       (100,100)
Proof
let
  val code_lookup   = mk_code_lookup
                        `fromAList all_data_prog`
                         all_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `all_config.word_conf.stack_frame_size`
                         all_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
in
 REWRITE_TAC [all_prog_def,all_x64_conf_def]
 \\ strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac all_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac all_to_data_updated_thm
 \\ fs [data_lang_safe_for_space_def]
 \\ strip_tac
 \\ qmatch_goalsub_abbrev_tac `_ v0`
 \\ `data_safe v0` suffices_by
    (Cases_on `v0` \\ fs [data_safe_def])
 \\ UNABBREV_ALL_TAC
 \\ qmatch_goalsub_abbrev_tac `is_64_bits c0`
 \\ `is_64_bits c0` by (UNABBREV_ALL_TAC \\ EVAL_TAC)
 \\ fs []
 \\ rpt (pop_assum kall_tac)
 (* start data_safe proof *)
 \\ REWRITE_TAC [ to_shallow_thm
                , to_shallow_def
                , initial_state_def
                , bvl_to_bviTheory.InitGlobals_location_eq]
 (* Make first call *)
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 \\ strip_makespace
 \\ ntac 49 strip_assign
 \\ make_tailcall
 \\ ntac 3
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
     \\ UNABBREV_ALL_TAC)
  \\ ntac 6 strip_assign
  \\ ntac 3
     (open_tailcall
     \\ ntac 4 strip_assign
     \\ make_if
     \\ ntac 2 strip_assign)
  \\ open_tailcall
  \\ ntac 4 strip_assign
  \\ make_if
  \\ ASM_REWRITE_TAC [code_lookup,frame_lookup]
  \\ simp []
  \\ IF_CASES_TAC >- (simp [data_safe_def,size_of_def,frame_lookup] \\ EVAL_TAC)
  \\ REWRITE_TAC [to_shallow_def]
  \\ ntac 3
     (strip_makespace
     \\ ntac 6 strip_assign
     \\ make_tailcall)
  \\ strip_makespace
  \\ ntac 12 strip_assign
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ irule data_safe_res
  \\ conj_tac >- (Cases \\ simp [] \\ IF_CASES_TAC \\ simp [])
  \\ UNABBREV_ALL_TAC
  \\ strip_call
  \\ ntac 4 strip_assign
  \\ open_tailcall
  \\ qmatch_goalsub_abbrev_tac ‘(bind _ _) st’
  \\ qabbrev_tac ‘vl = THE(sptree$lookup (0:num) st.locals)’
  \\ qabbrev_tac ‘il = THE(repint_to_list vl)’
  \\ qabbrev_tac ‘tsl = THE(repint_to_tsl vl)’
  \\ qabbrev_tac ‘ssum = THE(all_stack_size st.stack_frame_sizes st.limits 0 il)’
  \\ qspecl_then [‘LENGTH il’,‘st’,‘vl’,‘il’,‘0’,‘tsl’] mp_tac foldl_evaluate
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspecl_then [‘THE(st.stack_max)’,‘ssum’,
                             ‘THE(st.locals_size)’,
                             ‘THE(size_of_stack st.stack)’] mp_tac)
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  (* Prove that the preconditions of foldl_evaluate are satisfied *)
  >- (unabbrev_all_tac \\ simp[]
      \\ simp[size_of_stack_def,size_of_stack_frame_def]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(SIMP_CONV std_ss [code_lookup,frame_lookup])))
      \\ simp[]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV EVAL))
      \\ simp[]
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- (EVAL_TAC \\ METIS_TAC [])
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac
      >- ((* TODO: currently hard-coded to n=5 for no good reason *)
          EVAL_TAC >>
          Cases >- EVAL_TAC >>
          ntac 4 (simp[ADD1] >>
                  rename1 ‘n + _’ >>
                  Cases_on ‘n’ >- EVAL_TAC >>
                  rename1 ‘SUC n’) >>
          simp[] >> EVAL_TAC)
      \\ simp[frame_lookup,code_lookup,foldl_body_def,Int_plus_clos_body_def,Int_plus_body_def])
  \\ simp[ to_shallow_thm, to_shallow_def, initial_state_def,foldl_body_def ]
  \\ strip_tac
  >- (unabbrev_all_tac \\ simp[data_safe_def])
  \\ simp[pop_env_def,Abbr ‘st’]
  \\ qunabbrev_tac ‘rest_call’
  \\ strip_assign
  \\ simp[return_def]
  \\ eval_goalsub_tac “sptree$lookup _ _”
  \\ simp[flush_state_def]
  \\ simp[data_safe_def]
end
QED




val _ = export_theory();
