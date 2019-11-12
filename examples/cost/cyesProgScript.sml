(*
  A data-cost example of a non-terminating function (cyes)
  that prints a character indefinitely

*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;

val _ = new_theory "cyesProg"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************************** *)
(* * cyes (with mini-basis) * *)
(* ************************** *)

val _ = translation_extends "basisProg";

val whole_prog = whole_prog ()

val word8_mod =
  find_term (can (match_term ``Dmod "Word8" _``)) whole_prog

val word8_fromInt =
  find_term (can (match_term ``Dlet _ (Pvar "fromInt") _``)) word8_mod

val string_mod =
  find_term (can (match_term ``Dmod "String" _``)) whole_prog

val string_implode =
  find_term (can (match_term ``Dlet _ (Pvar "implode") _``)) string_mod

val word8array_mod =
  find_term (can (match_term ``Dmod "Word8Array" _``)) whole_prog

val word8array_array =
  find_term (can (match_term ``Dlet _ (Pvar "array") _``)) word8array_mod

val cyes =
  let val prog = process_topdecs `
      fun put_char c = let
        val s = String.implode [c]
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (put_char c; printLoop c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``[Dmod "Word8"      [^word8_fromInt];
                             Dmod "String"     [^string_implode];
                             Dmod "Word8Array" [^word8array_array]
                            ] ++ ^prog``
  end

val cyes2 =
  let val prog = process_topdecs `
      fun put_char c = let
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val s = String.implode [c]
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_char c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``[Dmod "Word8"      [^word8_fromInt];
                             Dmod "String"     [^string_implode];
                             Dmod "Word8Array" [^word8array_array]
                            ] ++ ^prog``
  end

val _ = intermediate_prog_prefix := "cyes2_"
val cyes2_thm = compile_x64 1000 1000 "cyes2" (REFL cyes2)
val _ = intermediate_prog_prefix := ""

val cyes2_data_code_def       = definition"cyes2_data_prog_def"
val cyes2_to_data_thm         = theorem"cyes2_to_data_thm"
val cyes2_config_def          = definition"cyes2_config_def"
val cyes2_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) cyes2_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) cyes2_thm)
  |> SIMP_RULE (srw_ss()) []


val _ = intermediate_prog_prefix := "cyes_"
val cyes_thm = compile_x64 1000 1000 "cyes" (REFL cyes)
val _ = intermediate_prog_prefix := ""

val cyes_data_code_def       = definition"cyes_data_prog_def"
val cyes_to_data_thm         = theorem"cyes_to_data_thm"
val cyes_config_def          = definition"cyes_config_def"
val cyes_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) cyes_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) cyes_thm)
  |> SIMP_RULE (srw_ss()) []


val f_diff = diff_codes cyes_data_code_def cyes2_data_code_def

val (f11,f12) = hd f_diff
val (f21,f22) = (hd o tl) f_diff

Theorem data_safe_cyes_code:
  ∀s ts smax sstack lsize.
   s.safe_for_space ∧
   wf s.refs ∧
   (s.stack_frame_sizes = cyes_config.word_conf.stack_frame_size) ∧
   (s.stack_max = SOME smax) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   (sstack + 103 < s.limits.stack_limit) ∧
   (sstack + lsize + 100 < s.limits.stack_limit) ∧
   (smax < s.limits.stack_limit) ∧
   s.limits.arch_64_bit ∧
   closed_ptrs (stack_to_vs s) s.refs ∧
   size_of_heap s + 4 ≤ s.limits.heap_limit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (lookup 0 s.locals = SOME (Number 97)) ∧
   (s.code = fromAList cyes_data_prog)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
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
  \\ rw []
  \\ strip_call
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe) _`
  \\ `safe` by (fs [Abbr `safe`, size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 6))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Useful simplification through the proof *)
  \\ `toListA [] (inter s.locals (LS ())) = [Number 97]`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def,toListA_def])
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  (* strip_assign *)
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ ntac 3 (strip_assign \\ fs [])
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
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def]
     \\ `n ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ irule LESS_EQ_TRANS \\ qexists_tac `n' + 3` \\ rw [])
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
  \\ ntac 4 strip_assign
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
     \\ Cases_on `ts`
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def]
     \\ `n1''''' ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ Cases_on `lookup (SUC n) seen1'''''` \\ fs [] \\ rveq \\ fs [])
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
     \\ Cases_on `ts` \\ fs [size_of_def,lookup_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def]
     \\ rveq
     \\ `n1''' ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ Cases_on `lookup (SUC n) seen1'''` \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ ntac 4 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ `closed_ptrs (b ++ c) s.refs` by fs [closed_ptrs_APPEND]
     (* \\ map_every  Q.UNABBREV_TAC [`a`,`b`,`c`] *)
     \\ drule size_of_insert \\ disch_then drule
     \\ disch_then (qspecl_then [`LN`,`p1`] mp_tac)
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ Cases_on `size_of (b ++ c) s.refs LN` \\ Cases_on `r`
     \\ disch_then drule \\ fs []
     \\ disch_then (qspec_then `x` assume_tac)
     \\ fs [] \\ rveq \\ rfs []
     \\ Q.UNABBREV_TAC `x`
     \\ fs [] \\ rveq \\ fs []
     \\ `n1' ≤ n'` by
        (irule size_of_le_APPEND
        \\ pop_assum kall_tac
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
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
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ strip_assign
  \\ fs [lookup_insert]
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ fs []
  \\ `lookup p2 (insert p1 (ByteArray T [97w]) s.refs) = NONE` by
     (fs [lookup_insert]
     \\ rw [Abbr `p2`, least_from_def]
     >- (Cases_on `p1 = 0` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `wf (insert p1 (ByteArray T [97w]) s.refs)` by fs [wf_insert]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`b ++ c`,`LN`,`p2`,`y`,`n1''`,`refs1''`,`seen1''`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs []
     \\ (qpat_x_assum `wf (insert _ _ _)` kall_tac
        \\ drule size_of_insert
        \\ Cases_on `size_of (b ++ c) s.refs LN` \\ Cases_on `r`
        \\ qmatch_asmsub_rename_tac `size_of (b ++ c) s.refs LN = (n8,refs8,seen8)`
        \\ disch_then (qspecl_then [`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
        \\ impl_tac
        >- fs [closed_ptrs_APPEND]
        \\ rw [] \\ Cases_on `lookup ts seen1'` \\ fs [] \\ rveq
        \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
        \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
        \\ `n1' ≤ n''` suffices_by fs []
        \\ ho_match_mp_tac size_of_le_APPEND
        \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
        \\ asm_exists_tac \\ fs []))
  \\ simp[] \\ ntac 2 (pop_assum kall_tac) \\ fs []
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []` \\ fs [])
  >- (fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ rveq \\ fs []
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ Cases_on `size_of (b ++ c) s.refs LN` \\ Cases_on `r`
     \\ qmatch_asmsub_rename_tac `size_of (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then
          [`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ fs [closed_ptrs_APPEND]
     \\ rw [] \\ fs []
     \\ Q.UNABBREV_TAC `x` \\ fs [] \\ rveq
     \\ `n1 ≤ n'` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ Q.UNABBREV_TAC `rest_call`
  \\ rveq \\ fs [flush_state_def]
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
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
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
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`b ++ c`,`LN`,`p2`,`y`,`n1''`,`refs1''`,`seen1''`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs [size_of_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [size_of_Number_head]
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ qmatch_asmsub_rename_tac `size_of (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then [`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ impl_tac >- fs [closed_ptrs_APPEND]
     \\ rveq \\ rw [] \\ Cases_on `lookup ts _` \\ fs [] \\ rveq
     \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
     \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
     \\ `n' ≤ n''` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ fs [closed_ptrs_def])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [closed_ptrs_def])
   \\ ONCE_REWRITE_TAC [closed_ptrs_cons]
   \\ conj_tac >- fs [closed_ptrs_APPEND,stack_to_vs_def]
   \\ fs [closed_ptrs_def,closed_ptrs_list_def]
  end
QED

Theorem data_safe_cyes_code_shallow[local] =
  data_safe_cyes_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_cyes_code_abort:
 ∀s ts.
   (lookup 0 s.locals = SOME (Number 97)) ∧
   2 ≤ s.limits.length_limit ∧
   (s.stack_frame_sizes = cyes_config.word_conf.stack_frame_size) ∧
   s.limits.arch_64_bit ∧
   (s.tstamps = SOME ts) ∧
   (s.code = fromAList cyes_data_prog)
   ⇒ ∃s' e. evaluate ((SND o SND) ^f21, s) =
       (SOME (Rerr (Rabort e)),s')
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
  measureInduct_on `^s.clock`
  \\ rw [to_shallow_def,to_shallow_thm]
  \\ strip_call
  \\ `(inter s.locals (LS ())) = LS (Number 97)`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def])
  \\ strip_makespace
  \\ ntac 6 strip_assign
  \\ strip_call
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call_1 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  (* open_call *)
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , lookup_insert, flush_state_def
          , size_of_stack_frame_def]
  \\ IF_CASES_TAC >- simp []
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup,lookup_inter]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp[LET_THM]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac [] >- metis_tac [] >- metis_tac [] >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw [] >- metis_tac []
        \\ CCONTR_TAC \\ fs [lookup_insert])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
        \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
        \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
        \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
     \\ CCONTR_TAC \\ fs [lookup_insert])
  \\ strip_assign \\ fs [lookup_insert]
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []`) >- simp []
  \\ strip_assign \\ strip_assign
  \\ rw [return_def,lookup_def]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_call`
  (*  make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter
          ,frame_lookup]
  \\ IF_CASES_TAC
  >- simp []
  \\ eval_goalsub_tac ``dataSem$call_env _ _``
  \\ qmatch_goalsub_abbrev_tac `evaluate (p0,s0)`
  \\ `s0.clock < s.clock` by fs [Abbr `s0`,dec_clock_def]
  \\ first_x_assum (drule_then (qspec_then `ts + 1` mp_tac))
  \\ impl_tac >- (fs [Abbr `s0`] \\ EVAL_TAC \\ fs [])
  \\ rw [] \\ fs []
  end
QED

Theorem data_safe_cyes_code_abort_shallow[local] =
  data_safe_cyes_code_abort |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_cyes:
 ∀ffi.
  backend_config_ok (^((rand o rator o lhs o concl) cyes_thm))
  ⇒ is_safe_for_space ffi
      (^((rand o rator o lhs o concl) cyes_thm))
      ^cyes
      (1000,1000)
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ assume_tac cyes_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac cyes_to_data_updated_thm
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
 \\ ntac 4
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
  \\ strip_call
  \\ ntac 9 strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ntac 5
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
  \\ strip_assign
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr (Rabort e')),s')`
     by (UNABBREV_ALL_TAC
        \\ ho_match_mp_tac data_safe_cyes_code_abort_shallow
        \\ fs [] \\ EVAL_TAC)
  \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac data_safe_cyes_code_shallow
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  \\ qexists_tac `10` \\ fs []
  end
QED

val _ = export_theory();
