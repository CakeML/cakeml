(*
  A data-cost example of a non-terminating function (cyes)
  that prints a character indefinitely

*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;

val _ = new_theory "yesProg"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************************** *)
(* * yes (with mini-basis) * *)
(* ************************** *)

(* val _ = translation_extends "basisProg"; *)

val _ = translation_extends "miniBasisProg";

val whole_prog = whole_prog ()

(* val word8_mod = *)
(*   find_term (can (match_term ``Dmod "Word8" _``)) whole_prog *)

(* val word8_fromInt = *)
(*   find_term (can (match_term ``Dlet _ (Pvar "fromInt") _``)) word8_mod *)

(* val string_mod = *)
(*   find_term (can (match_term ``Dmod "String" _``)) whole_prog *)

(* val string_implode = *)
(*   find_term (can (match_term ``Dlet _ (Pvar "implode") _``)) string_mod *)

(* val string_strcat = *)
(*   find_term (can (match_term ``Dlet _ (Pvar "strcat") _``)) string_mod *)

(* val word8array_mod = *)
(*   find_term (can (match_term ``Dmod "Word8Array" _``)) whole_prog *)

(* val word8array_array = *)
(*   find_term (can (match_term ``Dlet _ (Pvar "array") _``)) word8array_mod *)

val _ = (append_prog o process_topdecs) `
  fun put_line l = let
      val s = String.strcat l "\n"
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val _ = #(put_char) s a
    in () end;
  `

val _ = (append_prog o process_topdecs) `
  fun printLoop l = (put_line l; printLoop l);
  `

val maincall = process_topdecs `val _ = printLoop "yes"`

local
  val prog = get_prog(get_ml_prog_state())
in
  val yes = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

(*  ``(LAST o FRONT o FRONT) ^yes`` *)


(* find_term (can (match_term ``Dlet _ (Pvar "strcat") _``)) yes *)


(* find_term (can (match_term ``Dlet _ (Pvar "implode") _``)) yes *)

Theorem yes_prog_def = mk_abbrev "yes_prog" yes;

val yes2 =
  let val prog = process_topdecs `
      fun put_line l = let
          val s = String.strcat l "\n"
          val a = Word8Array.array 0 (Word8.fromInt 0)
          val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_line c);

      val _ = printLoop "yes"`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val yes2_thm = compile_to_data (compilation_compset())
                               x64_backend_config_def
                               (REFL yes2)
                               "yes2_data_prog"

val yes2_data_code_def       = definition"yes2_data_prog_def"

val _ = intermediate_prog_prefix := "yes_"
val yes_thm = compile_x64 1000 1000 "yes" (REFL yes)
val _ = intermediate_prog_prefix := ""

val yes_data_code_def       = definition"yes_data_prog_def"
val yes_to_data_thm         = theorem"yes_to_data_thm"
val yes_config_def          = definition"yes_config_def"
val yes_x64_conf            = (rand o rator o lhs o concl) yes_thm
val yes_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) yes_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) yes_thm)
  |> SIMP_RULE (srw_ss()) []

val f_diff = diff_codes yes_data_code_def yes2_data_code_def

(* val (f11,f12) = hd f_diff *)
val (f21,f22) = hd f_diff

Theorem data_safe_yes_code:
  ∀s ts smax sstack lsize.
   s.safe_for_space ∧
   wf s.refs ∧
   (s.stack_frame_sizes = yes_config.word_conf.stack_frame_size) ∧
   (s.stack_max = SOME smax) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   (sstack + 103 < s.limits.stack_limit) ∧
   (sstack + lsize + 100 < s.limits.stack_limit) ∧
   (smax < s.limits.stack_limit) ∧
   s.limits.arch_64_bit ∧
   closed_ptrs (stack_to_vs s) s.refs ∧
   size_of_heap s + 11 ≤ s.limits.heap_limit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (s.locals = fromList [RefPtr 2]) ∧
   (lookup 2 s.refs = SOME (ByteArray T [121w; 101w; 115w])) ∧
   (s.code = fromAList yes_data_prog)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
  in
  measureInduct_on `^s.clock`
  \\ fs [ to_shallow_thm
        , to_shallow_def
        , initial_state_def ]
  \\ rw [] \\ fs [fromList_def]
  \\ strip_call
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe) _`
  \\ `safe` by (fs [Abbr `safe`, size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 6))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* strip_assign *)
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp1) _`
  \\ `pp1 = p1`  by
     (UNABBREV_ALL_TAC \\ fs [least_from_def]
     \\ Cases_on `lookup 0 s.refs` \\ fs []
     >- (numLib.LEAST_ELIM_TAC
        \\ conj_tac >- (asm_exists_tac \\ fs [])
        \\ rw [] \\ Cases_on `n` \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (qexists_tac `ptr` \\ fs [])
     \\ rw [] \\ CCONTR_TAC
     \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [])
     \\ fs [NOT_LESS] \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def,small_num_def]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ _ _ = (_,refs'',seen'')`
     \\ drule size_of_RefPtr_head
     \\ eval_goalsub_tac ``sptree$lookup _ _``
     \\ rw [] \\ fs [])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ Q.ABBREV_TAC `pred = ∃w. 10 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 10` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 6 (strip_assign \\ fs [])
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  \\ `lookup p1 s.refs = NONE`  by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ 2` by (CCONTR_TAC  \\ fs [])
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq
     \\ drule_then drule wf_size_of
     \\ strip_tac
     \\ drule_then (qspecl_then [`p1`,`ByteArray T [0w]`] mp_tac) delete_insert_eq
     \\ impl_tac
     >- (drule_then drule size_of_lookup_NONE \\ fs [])
     \\ drule size_of_RefPtr_head
     \\ eval_goalsub_tac ``sptree$lookup _ _``
     \\ rw [] \\ fs [])
  \\ simp []
  \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  (* open_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     (* \\ Cases_on `ts` *)
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     >- (rveq \\ fs [] \\ rveq \\ fs []
        \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [])
     \\ rveq \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs []
     >- (fs [] \\ rveq
        \\ Cases_on `IS_SOME (lookup ts seen')` \\ fs []
        \\ rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs []
        \\ rveq \\ fs []
        \\ rveq \\ fs [])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_delete])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     (* \\ Cases_on `ts` *)
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     \\ rveq \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [lookup_delete]
     >- (rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs [])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  (* strip_assign *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_def,lookup_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [lookup_delete]
     >- (rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs [])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p2 _ _)) _`
  \\ fs [insert_shadow]
  \\ `lookup p2 s.refs = NONE` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ `p1 ≠ p2` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ qmatch_asmsub_rename_tac `size_of _ _ LN = (n'',_,seen0)`
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [] \\ rveq
     \\ fs [lookup_insert,lookup_delete] \\ rfs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ qmatch_asmsub_rename_tac `size_of _ _ LN = (n'',_,seen0)`
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [] \\ rveq
     \\ fs [lookup_insert,lookup_delete] \\ rfs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p3 _ _)) _`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp3) _`
  \\ `pp3 = p3` by
     (rw [Abbr`pp3`,Abbr`p3`,least_from_def]
     >- (Cases_on `0 = p2` \\ fs []
        \\ Cases_on `0 = p1` \\ fs []
        \\ numLib.LEAST_ELIM_TAC
        \\ rw []
        >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
           \\ rw [] \\ pop_assum (qspec_then `domain ((insert p2 ARB (insert p1 ARB s.refs)))` assume_tac)
           \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
           \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ Cases_on `x = p2` \\ fs [lookup_insert])
        \\ CCONTR_TAC \\ `0 < n` by rw []
        \\ first_x_assum drule \\ rw [])
     \\ fs [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [] \\ Cases_on `n'` \\ fs [])
     \\ fs [NOT_LESS]
     \\ CCONTR_TAC
     \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ `p3 ≠ p2` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `p3 ≠ p1` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [] \\ rfs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `lookup p3 s.refs = NONE` by
     (Q.UNABBREV_TAC `p3`
     \\ rw [least_from_def]
     >- (Cases_on `0 = p2` \\ Cases_on `0 = p1` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p2`
        \\ Cases_on `ptr = p1`
        \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p3` by (CCONTR_TAC  \\ fs [])
  \\ strip_assign
  \\ fs [lookup_insert]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ pop_assum (qspec_then `ByteArray T [121w; 101w; 115w; 10w]` assume_tac)
     \\ `wf (insert p2 (ByteArray T [121w; 101w; 115w; 10w])
              (insert p1 (ByteArray T [10w]) s.refs))` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p2` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [121w; 101w; 115w; 10w]` mp_tac)
     \\ fs [lookup_insert]
     \\ impl_tac
     >- (irule closed_ptrs_refs_insert \\ fs [closed_ptrs_def,lookup_insert])
     \\ strip_tac
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p3`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq
     \\ fs [lookup_delete]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq)
  \\ simp[] \\ ntac 2 (pop_assum kall_tac) \\ fs []
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [121w; 101w; 115w; 10w] []`
             \\ fs [])
  >- (fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq)
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ rveq \\ fs [flush_state_def]
  \\ Q.UNABBREV_TAC `rest_call`
  (* strip tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter,frame_lookup]
  \\ IF_CASES_TAC
  >- fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `data_safe (_ s0)`
  \\ first_x_assum (qspec_then `s0` assume_tac)
  \\ `s0.clock < s.clock` by (UNABBREV_ALL_TAC \\ rw [])
  \\ first_x_assum (drule_then irule) \\ Q.UNABBREV_TAC `s0` \\  fs []
  \\ simp [ size_of_heap_def,size_of_Number_head,stack_to_vs_def
          , lookup_def,toList_def,toListA_def
          , wf_insert, wf_delete ]
  \\ rw []
  >- fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
  >- fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
  >- (pairarg_tac \\ fs []
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ rveq \\ fs []
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ pop_assum (qspec_then `ByteArray T [121w; 101w; 115w; 10w]` assume_tac)
     \\ `wf (insert p2 (ByteArray T [121w; 101w; 115w; 10w])
              (insert p1 (ByteArray T [10w]) s.refs))` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p2` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [121w; 101w; 115w; 10w]` mp_tac)
     \\ fs [lookup_insert]
     \\ impl_tac
     >- (irule closed_ptrs_refs_insert \\ fs [closed_ptrs_def,lookup_insert])
     \\ strip_tac
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`LN`,`p3`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq
     \\ fs [lookup_delete]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq)
  >- fs [lookup_insert]
  >- rw [Once insert_def]
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ fs [closed_ptrs_def])
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ fs [closed_ptrs_def])
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [closed_ptrs_def])
  \\ ONCE_REWRITE_TAC [closed_ptrs_cons]
  \\ conj_tac >- fs [closed_ptrs_APPEND,stack_to_vs_def]
  \\ fs [closed_ptrs_def,closed_ptrs_list_def]
  end
QED

Theorem data_safe_yes_code_shallow[local] =
  data_safe_yes_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_yes_code_abort:
 ∀s ts.
   (s.locals = fromList [RefPtr 2]) ∧
   (lookup 2 s.refs = SOME (ByteArray T [121w; 101w; 115w])) ∧
   2 ≤ s.limits.length_limit ∧
   (s.stack_frame_sizes = yes_config.word_conf.stack_frame_size) ∧
   s.limits.arch_64_bit ∧
   (s.tstamps = SOME ts) ∧
   (s.code = fromAList yes_data_prog)
   ⇒ ∃s' e. evaluate ((SND o SND) ^f21, s) =
       (SOME (Rerr (Rabort e)),s')
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
  in
  measureInduct_on `^s.clock`
  \\ fs [ to_shallow_thm
        , to_shallow_def
        , initial_state_def ]
  \\ rw [] \\ fs [fromList_def]
  \\ strip_call
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp1) _`
  \\ `pp1 = p1`  by
     (UNABBREV_ALL_TAC \\ fs [least_from_def]
     \\ Cases_on `lookup 0 s.refs` \\ fs []
     >- (numLib.LEAST_ELIM_TAC
        \\ conj_tac >- (asm_exists_tac \\ fs [])
        \\ rw [] \\ Cases_on `n` \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (qexists_tac `ptr` \\ fs [])
     \\ rw [] \\ CCONTR_TAC
     \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [])
     \\ fs [NOT_LESS] \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ Q.ABBREV_TAC `pred = ∃w. 10 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 10` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 6 (strip_assign \\ fs [])
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  \\ `lookup p1 s.refs = NONE`  by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ 2` by (CCONTR_TAC  \\ fs [])
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  (* open_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  (* strip_assign *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p2 _ _)) _`
  \\ fs [insert_shadow]
  \\ `lookup p2 s.refs = NONE` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ `p1 ≠ p2` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p3 _ _)) _`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp3) _`
  \\ `pp3 = p3` by
     (rw [Abbr`pp3`,Abbr`p3`,least_from_def]
     >- (Cases_on `0 = p2` \\ fs []
        \\ Cases_on `0 = p1` \\ fs []
        \\ numLib.LEAST_ELIM_TAC
        \\ rw []
        >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
           \\ rw [] \\ pop_assum (qspec_then `domain ((insert p2 ARB (insert p1 ARB s.refs)))` assume_tac)
           \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
           \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ Cases_on `x = p2` \\ fs [lookup_insert])
        \\ CCONTR_TAC \\ `0 < n` by rw []
        \\ first_x_assum drule \\ rw [])
     \\ fs [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [] \\ Cases_on `n'` \\ fs [])
     \\ fs [NOT_LESS]
     \\ CCONTR_TAC
     \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ `p3 ≠ p2` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `p3 ≠ p1` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [] \\ rfs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `lookup p3 s.refs = NONE` by
     (Q.UNABBREV_TAC `p3`
     \\ rw [least_from_def]
     >- (Cases_on `0 = p2` \\ Cases_on `0 = p1` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p2`
        \\ Cases_on `ptr = p1`
        \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p3` by (CCONTR_TAC  \\ fs [])
  \\ strip_assign
  \\ fs [lookup_insert]
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [121w; 101w; 115w; 10w] []`
             \\ fs [])
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ rveq \\ fs [flush_state_def]
  \\ Q.UNABBREV_TAC `rest_call`
  (* strip tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter,frame_lookup]
  \\ IF_CASES_TAC
  >- fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
  \\ simp[dec_clock_def]
  \\ eval_goalsub_tac ``dataSem$call_env _ _``
  \\ qmatch_goalsub_abbrev_tac `f0 (evaluate _)`
  \\ qmatch_goalsub_abbrev_tac `f0 e0`
  \\ reverse (sg `∃s' e. e0 = (SOME (Rerr (Rabort e)),s')`)
  \\ fs [Abbr`f0`,Abbr`e0`]
  \\ qmatch_goalsub_abbrev_tac `evaluate (p0,s0)`
  \\ `s0.clock < s.clock` by fs [Abbr `s0`,dec_clock_def]
  \\ first_x_assum (drule_then (qspec_then `ts + 2` mp_tac))
  \\ impl_tac >- (fs [Abbr `s0`,lookup_insert,call_env_def] \\ EVAL_TAC)
  \\ rw [Abbr`p0`,to_shallow_def,to_shallow_thm] \\ fs []
  end
QED

Theorem data_safe_yes_code_abort_shallow[local] =
  data_safe_yes_code_abort |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_yes:
 ∀ffi.
  backend_config_ok ^yes_x64_conf
  ⇒ is_safe_for_space ffi
      ^yes_x64_conf
      ^yes
      (1000,1000)
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
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
 \\ assume_tac yes_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac yes_to_data_updated_thm
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
 \\ rpt strip_tac
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
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 \\ make_tailcall
 \\ ntac 5
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
  \\ strip_call
  \\ ntac 9 strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ntac 6
     (open_tailcall
     \\ ntac 4 strip_assign
     \\ make_if
     \\ ntac 2 strip_assign)
  \\ open_tailcall
  \\ ntac 4 strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call`
  \\ ntac 3 strip_assign
  \\ make_tailcall
  \\ ntac 5
     (strip_makespace
     \\ ntac 7 strip_assign
     \\ make_tailcall)
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 121 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 121` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 101 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 101` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 115 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 115` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr (Rabort e')),s')`
     by (UNABBREV_ALL_TAC
        \\ ho_match_mp_tac data_safe_yes_code_abort_shallow
        \\ fs [] \\ EVAL_TAC)
  \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac data_safe_yes_code_shallow
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  \\ qexists_tac `12` \\ fs []
  end
QED

Theorem yes_x64_conf_def = mk_abbrev "yes_x64_conf" yes_x64_conf;
Theorem yes_s_def = mk_abbrev"yes_s"
                      ((rand o rand o rhs o concl) primSemEnvTheory.prim_sem_env_eq)

(* TODO *)
(*
Definition yes_env_def:
  yes_env ffi = FST (THE (prim_sem_env sio_ffi_state))
End

Theorem prim_sem_env_yes:
  THE (prim_sem_env sio_ffi_state) = (yes_env ffi,yes_s)
Proof
EVAL_TAC \\ rw [yes_s_def]
QED
*)

(* TODO *)
Theorem backend_config_ok_yes:
  backend_config_ok yes_x64_conf
Proof
 cheat
QED

Theorem yes_semantics_prog_Diverge:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in semantics_prog s env yes_prog (Diverge (LREPEAT [put_char_event "yes\n"]))
Proof
  cheat
QED

Theorem yes_semantics_prog_not_Fail:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in ¬semantics_prog s env yes_prog Fail
Proof
  assume_tac yes_semantics_prog_Diverge
  \\ fs [] \\ pairarg_tac \\  fs []
  \\ CCONTR_TAC \\ fs []
  \\ drule semanticsPropsTheory.semantics_prog_deterministic
  \\ pop_assum kall_tac
  \\ disch_then drule
  \\ fs []
QED

Theorem IMP_IMP_TRANS_THM:
  ∀W P R Q. (W ⇒ Q) ⇒ (P ⇒ R ⇒ W) ⇒ P ⇒ R ⇒ Q
Proof
 rw []
QED

Theorem machine_sem_eq_semantics_prog:
semantics_prog s env prog (Diverge io_trace) ⇒
  (machine_sem mc (ffi:'ffi ffi_state) ms = semantics_prog s env prog) ⇒
     machine_sem mc ffi ms (Diverge io_trace)
Proof
  rw []
QED

Theorem machine_sem_eq_semantics_prog_ex:
(∃io_trace. semantics_prog s env prog (Diverge io_trace)) ⇒
  (machine_sem mc (ffi:'ffi ffi_state) ms = semantics_prog s env prog) ⇒
     (∃io_trace. machine_sem mc ffi ms (Diverge io_trace))
Proof
  rw []
QED

(* TODO: fill the missing pieces *)
(*
val yes_safe_thm =
    let
      val ffi = ``sio_ffi_state``
      val is_safe = data_safe_yes
                    |> REWRITE_RULE [GSYM yes_prog_def
                                    ,GSYM yes_x64_conf_def]
                    |> ISPEC ffi
      val not_fail = yes_semantics_prog_not_Fail
                     |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_yes
                                         ,ELIM_UNCURRY]
      val is_corr = MATCH_MP compile_correct_is_safe_for_space yes_thm
                    |> REWRITE_RULE [GSYM yes_prog_def
                                    ,GSYM yes_x64_conf_def]
                    |> Q.INST [`stack_limit` |-> `1000`
                              ,`heap_limit` |-> `1000`]
                    |> INST_TYPE [``:'ffi`` |-> ``:unit``]
                    |> Q.INST [`ffi` |-> `sio_ffi_state`]
                    |> SIMP_RULE std_ss [prim_sem_env_yes,LET_DEF,not_fail,ELIM_UNCURRY]
      val machine_eq = MATCH_MP (machine_sem_eq_semantics_prog |> INST_TYPE [``:'ffi`` |-> ``:unit``])
                                (yes_semantics_prog_Diverge
                                   |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_yes,ELIM_UNCURRY])
      val safe_thm_aux = MATCH_MP (IMP_TRANS is_safe is_corr) backend_config_ok_yes
    in MATCH_MP (MATCH_MP IMP_IMP_TRANS_THM machine_eq)
                (safe_thm_aux |> SIMP_RULE std_ss [prim_sem_env_yes,LET_DEF,ELIM_UNCURRY])
    end

Theorem yes_safe = yes_safe_thm
*)

val _ = export_theory();
