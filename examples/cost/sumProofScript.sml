(* Prove of sum space consumption *)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;
open sumProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "sumProof"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val sum_x64_conf = (rand o rator o lhs o concl) sum_thm

val _ = install_naming_overloads "sumProg";
val _ = write_to_file sum_data_prog_def;

Theorem data_safe_sum:
   ∀ffi.
  backend_config_ok ^sum_x64_conf
  ⇒ is_safe_for_space ffi
       sum_x64_conf
       sum_prog
       (* (s_size,h_size) *)
       (100,100)
Proof
let
  val code_lookup   = mk_code_lookup
                        `fromAList sum_data_prog`
                         sum_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `sum_config.word_conf.stack_frame_size`
                         sum_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
in
 REWRITE_TAC [sum_prog_def,sum_x64_conf_def]
 \\ strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac sum_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac sum_to_data_updated_thm
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
  (* Call to sum *)
  \\ cheat
end
QED

val _ = export_theory();
