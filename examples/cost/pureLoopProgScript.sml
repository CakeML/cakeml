(*
  A data-cost example of a non-terminating function (pureLoop)
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory;
open costLib costPropsTheory;
open dataSemTheory data_monadTheory dataLangTheory;

val _ = new_theory "pureLoopProg"


Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************ *)
(* * pureLoop * *)
(* ************ *)

(* A simple infinite loop that does nothing *)

val pureLoop2 = process_topdecs
  `fun pureLoop x = pureLoop (x+1);
   val _ = pureLoop 1`

val _ = intermediate_prog_prefix := "pureLoop2_"
val pureLoop2_thm = compile_x64 1000 1000 "pureLoop2" (REFL pureLoop2)
val _ = intermediate_prog_prefix := ""

val pureLoop2_data_code_def       = definition"pureLoop2_data_prog_def"
val pureLoop2_to_data_thm         = theorem"pureLoop2_to_data_thm"
val pureLoop2_config_def          = definition"pureLoop2_config_def"
val pureLoop2_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) pureLoop2_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) pureLoop2_thm)
  |> SIMP_RULE (srw_ss()) [];

val pureLoop = process_topdecs
  `fun pureLoop x = pureLoop x;
   val _ = pureLoop 1`;

val _ = intermediate_prog_prefix := "pureLoop_";
val pureLoop_thm = compile_x64 1000 1000 "pureLoop" (REFL pureLoop);
val _ = intermediate_prog_prefix := "";

val pureLoop_data_code_def       = definition"pureLoop_data_prog_def"
val pureLoop_to_data_thm         = theorem"pureLoop_to_data_thm"
val pureLoop_config_def          = definition"pureLoop_config_def"
val pureLoop_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) pureLoop_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) pureLoop_thm)
  |> SIMP_RULE (srw_ss()) [];

val (p1,p2) = diff_code pureLoop_data_code_def pureLoop2_data_code_def;

Theorem data_safe_pureLoop_code[local]:
  ∀s sstack smax.
   s.safe_for_space ∧
   (s.stack_frame_sizes = pureLoop_config.word_conf.stack_frame_size) ∧
   (s.stack_max = SOME smax) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (sstack < s.limits.stack_limit) ∧
   (smax < s.limits.stack_limit) ∧
   (∃x. lookup 0 s.locals = SOME x) ∧
   (lookup 249 s.code =
      ^((``lookup 249 (fromAList pureLoop_data_prog)``
        |> (REWRITE_CONV [pureLoop_data_code_def]
            THENC EVAL)
        |> rhs o concl)))
   ⇒ data_safe (evaluate ((SND o SND) ^p1, s))
Proof
  measureInduct_on `^s.clock`
  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def
        , flush_state_def ]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]
  \\ first_x_assum (drule_then
       (qspecl_then [`THE (size_of_stack s'.stack)`
                    ,`THE s'.stack_max`] mp_tac))
  \\ impl_tac
  >- (rw [Abbr `s'`,lookup_fromList,pureLoop_config_def,lookup_def]
     \\ fs [lookup_def,libTheory.the_def,MAX_DEF])
  \\ rw []
  \\ qmatch_asmsub_abbrev_tac `evaluate (_,s'')`
  \\ `s' = s''`
     by (UNABBREV_ALL_TAC
        \\ rw [state_component_equality]
        \\ EVAL_TAC)
  \\ fs [] \\ EVERY_CASE_TAC \\ fs [data_safe_def]
QED

Theorem data_safe_pureLoop_code_shallow[local] =
  data_safe_pureLoop_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_pureLoop_code_timeout[local]:
  ∀s. (∃x. lookup 0 s.locals = SOME x) ∧
      (lookup 249 s.code =
         ^((``lookup 249 (fromAList pureLoop_data_prog)``
           |> (REWRITE_CONV [pureLoop_data_code_def]
               THENC EVAL)
           |> rhs o concl)))
      ⇒ ∃s'. evaluate ((SND o SND) ^p1, s) =
               (SOME (Rerr(Rabort Rtimeout_error)),s')
Proof
  measureInduct_on `^s.clock`
  \\ rw [ evaluate_def,get_var_def
        , lookup_fromAList,get_vars_def
        , find_code_def,call_env_def,data_safe_def]
  \\ rw [lookup_fromList,dec_clock_def,lookup_fromAList,data_safe_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s')`
  \\ `s'.clock < s.clock` by rw [Abbr `s'`]
  \\ first_x_assum drule
  \\ impl_tac
  >- rw [Abbr `s'`,lookup_fromList]
  \\ rw [] \\ rw []
QED

Theorem data_safe_pureLoop_code_timeout_shallow[local] =
  data_safe_pureLoop_code_timeout |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_pureLoop:
 ∀ffi.
   backend_config_ok (^((rand o rator o lhs o concl) pureLoop_thm))
   ⇒ is_safe_for_space ffi
       (^((rand o rator o lhs o concl) pureLoop_thm))
       ^pureLoop
       (1000,1000)
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList pureLoop_data_prog`
                        pureLoop_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `pureLoop_config.word_conf.stack_frame_size`
                        pureLoop_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac pureLoop_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac pureLoop_to_data_updated_thm
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
 (* Some tactics *)
 \\ REWRITE_TAC [ to_shallow_thm
                , to_shallow_def
                , initial_state_def
                , bvl_to_bviTheory.InitGlobals_location_eq]
 \\ rpt strip_tac
  (* Make first call *)
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 (* Another call *)
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 (* Another tailcall *)
 \\ make_tailcall
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ ntac 6 strip_assign
 \\ open_tailcall
 \\ ntac 4 strip_assign
 \\ make_if
 \\ ntac 2 strip_assign
 \\ open_tailcall
 \\ ntac 4 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 \\ strip_assign
 \\ make_tailcall
 \\ strip_makespace
 \\ ntac 6 strip_assign
 \\ make_tailcall
 \\ strip_assign
 (* Finally we reach our function call *)
 \\ ho_match_mp_tac data_safe_bind_error
 \\ open_call
 \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
 \\ qmatch_goalsub_abbrev_tac `f s`
 \\ `∃s'. f s = (SOME (Rerr(Rabort Rtimeout_error)),s')`
    by (unabbrev_all_tac
       \\ ho_match_mp_tac data_safe_pureLoop_code_timeout_shallow
       \\ rw [lookup_def,lookup_fromList,code_lookup])
 \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
 \\ unabbrev_all_tac
 \\ ho_match_mp_tac data_safe_pureLoop_code_shallow
 \\ rw [lookup_def,lookup_fromList,code_lookup,size_of_stack_def
       ,size_of_stack_frame_def]
 end
QED

val _ = check_thm data_safe_pureLoop;

val _ = export_theory();
