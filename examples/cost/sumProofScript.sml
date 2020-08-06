(* Prove of sum space consumption *)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;
open sumProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "sumProof"

val _ = ParseExtras.temp_tight_equality ()

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val sum_x64_conf = (rand o rator o lhs o concl) sum_thm

val _ = install_naming_overloads "sumProg";
val _ = write_to_file sum_data_prog_def;

val foldl_body = ``lookup_foldl (fromAList sum_data_prog)``
           |> (REWRITE_CONV [sum_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

Definition foldl_body_def:
  foldl_body = ^foldl_body
End

val Int_plus_clos_body = ``lookup_Int_+_clos (fromAList sum_data_prog)``
           |> (REWRITE_CONV [sum_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

Definition Int_plus_clos_body_def:
  Int_plus_clos_body = ^Int_plus_clos_body
End

val Int_plus_body = ``lookup_Int_+ (fromAList sum_data_prog)``
           |> (REWRITE_CONV [sum_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

Definition Int_plus_body_def:
  Int_plus_body = ^Int_plus_body
End

(* integer list of length l and with timestamps strictly bounded by tsb *)
Definition repint_list_def:
  (* cons *)
  repint_list (Block ts _ [Number i; rest]) (l:num) (tsb:num) =
     (ts < tsb ∧ l > 0 ∧ repint_list rest (l-1) tsb) ∧
  (* nil *)
  repint_list (Block _ tag []) (l:num) tsb = (tag = 0 ∧ l = 0) ∧
  (* everything else *)
  repint_list _ _ _ = F
End

Theorem repint_list_cases:
  ∀vl n ts. repint_list vl n ts
   ⇒ (∃ts0 tag0 i rest. vl = Block ts0 tag0 [Number i; rest] ∧ repint_list rest (n-1) ts ∧ ts0 < ts) ∨
     (∃ts0. vl = Block ts0 0 [])
Proof
  ho_match_mp_tac repint_list_ind \\ rw [repint_list_def]
QED

(* The maximum amount of heap space that will be consumed by the accumulator (e) when
   adding all number in the list
 *)
Definition sum_heap_size_def:
  sum_heap_size s e []      = 0 ∧
  sum_heap_size s e (x::xs) = MAX (space_consumed s Add [Number e; Number x])
                                  (sum_heap_size s (e+x) xs)
End

(* The maximum amount of stack space that will be consumed by the accumulator (e) when
   adding all number in the list
 *)
Definition sum_stack_size_def:
  sum_stack_size sfs lims e []      = SOME 0 ∧
  sum_stack_size sfs lims e (x::xs) = OPTION_MAP2 MAX (stack_consumed sfs lims (Add) [Number e; Number x])
                                                      (sum_stack_size sfs lims (e+x) xs)
End

(* Turns a ‘v’ value into a ‘int list’; returns NONE if something goes wrong *)
Definition repint_to_list_def:
  repint_to_list (Block _ _ [Number i; rest]) = OPTION_MAP (CONS i) (repint_to_list rest) ∧
  repint_to_list (Block _ 0 []) = SOME [] ∧
  repint_to_list _ = NONE
End

(* If ‘l : v’ represents a list of integer, it is safe to turn it into
   an actual list of integers
*)
Theorem repint_list_to_list_SOME:
  ∀l n ts. repint_list l n ts ⇒ ∃il. repint_to_list l = SOME il
Proof
  ho_match_mp_tac repint_list_ind \\ rw [repint_to_list_def,repint_list_def]
QED

Theorem repint_list_to_list_LENGTH:
  ∀l n ts il. repint_list l n ts ∧ repint_to_list l = SOME il ⇒ LENGTH il = n
Proof
  ho_match_mp_tac repint_list_ind \\ rw [repint_to_list_def,repint_list_def]
  \\ fs [repint_to_list_def]
QED

Theorem sum_heap_size_eq:
  ∀s1 s2 l e.
   s1.limits = s2.limits ⇒ sum_heap_size s2 e l = sum_heap_size s1 e l
Proof
  ntac 2 strip_tac
  \\ Induct \\ rw [sum_heap_size_def,space_consumed_def]
QED

Theorem Int_plus_evaluate:
  ∀s i1 i2 sstack smax ssum.
    (* Sizes *)
    size_of_stack s.stack = SOME sstack ∧
    s.locals_size = SOME 4 ∧
    s.stack_max = SOME smax ∧
    (* Arguments *)
    s.locals = fromList [Number i2; Number i1] ∧
    (* Stack frames *)
    s.stack_frame_sizes = sum_config.word_conf.stack_frame_size ∧
    (* Limits *)
    stack_consumed s.stack_frame_sizes s.limits Add [Number i1; Number i2] = SOME ssum ∧
    smax < s.limits.stack_limit ∧
    sstack + 4 + ssum < s.limits.stack_limit ∧
    size_of_heap s + space_consumed s Add [Number i1; Number i2] ≤ s.limits.heap_limit ∧
    lim_safe s.limits Add [Number i1; Number i2] ∧
    (* Code *)
    (* Invariants *)
    s.safe_for_space ∧
    s.limits.arch_64_bit
    (* s.tstamps = SOME ts ∧ *)
    (* 1 < s.limits.length_limit *)
    ⇒
    ∃pkheap0.
     evaluate (Int_plus_body,s) =
       (SOME (Rval (Number (i1+i2))), s with <| locals := LN;
                                                locals_size := SOME 0;
                                                space := 0;
                                                stack_max := SOME (MAX smax (sstack + 4 + ssum));
                                                peak_heap_length := pkheap0
                            |>)
Proof
  rw[Int_plus_body_def]
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def]
  \\ qpat_x_assum ‘s.locals = _’ (assume_tac o EVAL_RULE)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ simp [bind_def,assign_def,cut_state_opt_def,
           cut_state_def,cut_env_def]
  \\ eval_goalsub_tac ``dataSem$get_vars    _ _`` \\ simp []
  \\ simp[do_app_def,do_app_aux_def,do_space_def,
          op_space_reset_def,set_var_def,do_stack_def]
  \\ qunabbrev_tac ‘rest_ass’
  \\ simp [return_def,flush_state_def,state_component_equality]
  \\ fs [size_of_stack_def] \\ rfs []
  \\ (conj_tac
      >- (eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
          \\ qmatch_goalsub_abbrev_tac ‘size_of_heap ss’
          \\ ‘ss = s’ suffices_by rw []
          \\ UNABBREV_ALL_TAC \\ rw [state_component_equality])
      \\ EVAL_TAC)
QED

(* Every addition performed stays within the length_limit *)
Definition foldadd_limit_ok_def:
  foldadd_limit_ok lims acc il =
  ((*(small_num lims.arch_64_bit acc ∨
   bignum_size lims.arch_64_bit acc ≤ 2 ** lims.length_limit) ∧  *)
   (∀n.
      n < LENGTH il ⇒
      let i1 = acc + FOLDR $+ 0 (TAKE n il);
          i2 = EL n il
      in
        lim_safe lims Add [Number i1; Number i2]))
End

Theorem foldadd_limits_ok_step:
  foldadd_limit_ok lims acc (n::l) ⇒
  foldadd_limit_ok lims (acc + n) l
Proof
  rw[foldadd_limit_ok_def] >>
  rename1 ‘m < LENGTH l’ >>
  first_x_assum(qspec_then ‘SUC m’ mp_tac) >>
  rw[] >>
  fs[AC integerTheory.INT_ADD_SYM integerTheory.INT_ADD_ASSOC]
QED

Theorem foldl_evaluate:
  ∀n s vl il acc ts_f tag_f sstack lsize ssum smax acc ts.
    (* Sizes *)
    size_of_stack s.stack = SOME sstack ∧
    s.locals_size = SOME lsize ∧
    lookup_foldl s.stack_frame_sizes = SOME lsize ∧
    s.stack_max = SOME smax ∧
    s.space = 0 ∧
    (* Arguments *)
    s.locals = fromList [vl ; Number acc; Block ts_f tag_f [CodePtr_Int_+_clos;Number 1]] ∧
    repint_list vl n ts ∧
    repint_to_list vl = SOME il ∧
    (* Stack frames *)
    s.stack_frame_sizes = sum_config.word_conf.stack_frame_size ∧
    sum_stack_size s.stack_frame_sizes s.limits acc il = SOME ssum ∧
    (* Limits *)
    smax < s.limits.stack_limit ∧
    sstack + lsize + ssum + 4 < s.limits.stack_limit ∧
    size_of_heap s + sum_heap_size s acc il ≤ s.limits.heap_limit ∧
    foldadd_limit_ok s.limits acc il ∧
    (* Code *)
    lookup_foldl s.code      = SOME (3,foldl_body) ∧
    lookup_Int_+_clos s.code = SOME (3,Int_plus_clos_body) ∧
    lookup_Int_+ s.code      = SOME (2,Int_plus_body) ∧
    (* Invariants *)
    s.safe_for_space ∧
    s.limits.arch_64_bit ∧
    s.tstamps = SOME ts ∧
    1 < s.limits.length_limit
    ⇒
    ∃res lcls0 lsz0 smax0 clk0 ts0 pkheap0 stk.
     evaluate (foldl_body,s) =
       (SOME res, s with <| locals := lcls0;
                            locals_size := lsz0;
                            stack_max := SOME smax0;
                            clock := clk0;
                            tstamps := SOME ts0;
                            peak_heap_length := pkheap0;
                            stack := stk;
                            space := 0
                            |>) ∧
     clk0 ≤ s.clock ∧
     (res = (Rerr(Rabort Rtimeout_error)) ∨
      ∃sumi. res = Rval (Number sumi) ∧ (stk = s.stack) ∧
             smax0 = MAX smax (lsize + sstack + (if n = 0 then 0 else 4) + ssum))
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
  fun max_is t =
    qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _` >>
    subgoal ‘max0 = SOME (^(Term t))’
    THENL
    [(Q.UNABBREV_TAC ‘max0’ \\ fs [small_num_def,size_of_stack_def]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
in
  completeInduct_on`n`
  \\ rw[foldl_body_def,Int_plus_body_def,Int_plus_clos_body_def]
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def]
  \\ qpat_x_assum ‘s.locals = _’ (assume_tac o EVAL_RULE)
  \\ drule repint_list_cases \\ reverse (rw [])
  \\ fs [repint_list_def]
  >- (strip_assign \\ make_if
     \\ rw [state_component_equality]
     \\ fs [repint_to_list_def] \\ rveq
     \\ fs [sum_stack_size_def] \\ rveq
     \\ fs [])
  \\ strip_assign
  \\ make_if
  \\ rename1`repint_to_list (Block ts_vl tag_vl _)`
  \\ ntac 4 strip_assign
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ make_if
  \\ strip_assign
  \\ max_is ‘MAX smax (lsize + sstack)’
  >- fs [MAX_DEF]
  \\ strip_call
  \\ open_tailcall
  \\ max_is ‘MAX smax (lsize + sstack + 4)’
  >- fs [MAX_DEF]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ ‘safe’ by
     (qunabbrev_tac ‘safe’ \\ fs [size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  \\ fs [repint_to_list_def] \\ rveq
  \\ fs [sum_stack_size_def]
  \\ qmatch_goalsub_abbrev_tac ‘bind _ _ s'’
  \\ qspecl_then [‘s'’,‘acc’,‘i’] mp_tac Int_plus_evaluate
  \\ disch_then (qspecl_then [‘THE (size_of_stack s'.stack)’,
                              ‘THE (s'.stack_max)’,
                              ‘x1’] mp_tac)
  \\ impl_tac
  >- (qunabbrev_tac ‘s'’ \\ rw []
     >- fs [size_of_stack_def,size_of_stack_frame_def]
     >- EVAL_TAC
     >- rfs []
     >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF,size_of_stack_frame_def,size_of_stack_def])
     >- (fs[space_consumed_def,sum_heap_size_def]
         \\ qmatch_goalsub_abbrev_tac ‘size_of_heap s0 + s_consumed’
         \\ ‘size_of_heap s0 ≤ size_of_heap s’ suffices_by
           (Cases_on ‘s_consumed ≤ sum_heap_size s (acc + i) z’ \\ fs [MAX_DEF])
         \\ qunabbrev_tac ‘s0’
         \\ simp [size_of_heap_def,stack_to_vs_def,toList_def,toListA_def,extract_stack_def]
         \\ qmatch_goalsub_abbrev_tac ‘rest::rest_v’
         (* TODO: this should be true, however one needs to move some values around to show it *)
         \\ cheat)
     \\ qhdtm_x_assum ‘foldadd_limit_ok’ mp_tac
     \\ simp[foldadd_limit_ok_def]
     \\ disch_then(qspec_then ‘0’ mp_tac) \\ simp[])
  \\ REWRITE_TAC [Int_plus_body_def,to_shallow_thm,to_shallow_def]
  \\ rw [] \\ simp []
  \\ qunabbrev_tac ‘s'’
  \\ simp [pop_env_def,set_var_def]
  \\ qunabbrev_tac ‘rest_call’
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ max_is ‘MAX smax (lsize + sstack + x1 + 4)’
  >- fs [MAX_DEF]
  \\ simp [move_def,lookup_def,set_var_def,lookup_insert]
  \\ IF_CASES_TAC >- rw [state_component_equality]
  \\ first_x_assum (qspec_then ‘n - 1’ mp_tac)
  \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘to_shallow _ s'’
  \\ disch_then (qspecl_then [‘s'’,‘rest’,‘z’,‘ts_f’,‘tag_f’] mp_tac)
  \\ disch_then (qspecl_then [‘THE (size_of_stack s'.stack)’,‘THE s'.locals_size’] mp_tac)
  \\ disch_then (qspecl_then [‘x2’,‘THE s'.stack_max’,‘acc + i’,‘ts’] mp_tac)
  \\ impl_tac
  >- (qunabbrev_tac ‘s'’
     \\ rw [frame_lookup,foldl_body_def,Int_plus_body_def,Int_plus_clos_body_def]
     \\ rfs []
     >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF])
     >- (rfs [frame_lookup] \\ rveq \\ fs []
         \\ Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF])
     >- (qmatch_goalsub_abbrev_tac ‘sum_heap_size s'’
         \\ qspecl_then [‘s’,‘s'’,‘z’,‘acc + i’] mp_tac sum_heap_size_eq
         \\ impl_tac >- (UNABBREV_ALL_TAC \\ rw []) \\ rw []
         \\ fs[space_consumed_def,sum_heap_size_def]
         \\ qmatch_asmsub_abbrev_tac ‘size_of_heap s + MAX s_consumed _’
         \\ ‘size_of_heap s' ≤ size_of_heap s’ suffices_by
            (Cases_on ‘s_consumed ≤ sum_heap_size s (acc + i) z’ \\ fs [MAX_DEF])
         \\ qunabbrev_tac ‘s'’
         \\ simp [size_of_heap_def,stack_to_vs_def,extract_stack_def]
         \\ eval_goalsub_tac “sptree$toList _”
         \\ eval_goalsub_tac “sptree$toList _”
         \\ qmatch_goalsub_abbrev_tac ‘_ ++ v1 ++ v2’
         (* TODO: again a matter of moving things around inside size_of *)
         \\ cheat)
      >- (imp_res_tac foldadd_limits_ok_step)
     \\ fs [GREATER_DEF] \\ Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def,foldl_body_def]
  \\ rw [] \\ qunabbrev_tac ‘s'’ \\ simp []
  \\ simp [state_component_equality,GREATER_DEF] \\ fs []
  >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
  >- (reverse conj_tac
     >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
     \\ ‘n = 1’ by fs [] \\ rveq \\ fs []
     \\ drule repint_list_cases \\ rw []
     \\ fs [repint_list_def,repint_to_list_def]
     \\ rveq \\ fs [sum_stack_size_def] \\ rveq
     \\ rw [MAX_DEF])
  >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
  \\ rw [MAX_DEF]
  \\ Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC
end
QED

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
  \\ strip_call
  \\ ntac 4 strip_assign
  \\ open_tailcall
  (* TODO: plug foldl_evaluate in *)
  \\ cheat
end
QED

val _ = export_theory();
