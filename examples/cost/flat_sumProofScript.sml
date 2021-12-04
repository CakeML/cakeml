(*
  Prove of sum space consumption
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory flat_size_ofPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;
open sumProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "flat_sumProof"

val _ = ParseExtras.temp_tight_equality ()

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val sum_x64_conf = (rand o rator o lhs o concl) sum_thm

val _ = install_naming_overloads "sumProg";
val _ = write_to_file sum_data_prog_def;

val fields = TypeBase.fields_of “:('c,'ffi) dataSem$state”;

Overload state_refs_fupd = (fields |> assoc "refs" |> #fupd);
Overload state_locals_fupd = (fields |> assoc "locals" |> #fupd);
Overload state_stack_max_fupd = (fields |> assoc "stack_max" |> #fupd);
Overload state_safe_for_space_fupd = (fields |> assoc "safe_for_space" |> #fupd);
Overload state_peak_heap_length_fupd = (fields |> assoc "peak_heap_length" |> #fupd);

val foldl_body = ``lookup_List_foldl (fromAList sum_data_prog)``
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

(* The only part of the state that affects the list's heap usage is ‘limits’ *)
Theorem sum_heap_size_eq:
  ∀s1 s2 l e.
   s1.limits = s2.limits ⇒ sum_heap_size s2 e l = sum_heap_size s1 e l
Proof
  ntac 2 strip_tac
  \\ Induct \\ rw [sum_heap_size_def,space_consumed_def]
QED

(* The size of the biggest number in the list *)
Definition bigest_num_size_def:
  bigest_num_size lims [] = 0
∧ bigest_num_size lims (x::xs) =
    MAX (FST (size_of lims [Number x] LN LN))
             (bigest_num_size lims xs)
End

(* How big the accumulator will ever get *)
Definition bigest_acc_size_def:
  bigest_acc_size lims acc [] = 0
∧ bigest_acc_size lims acc (x::xs) =
    (FST (size_of lims [Number (acc+x)] LN LN) - FST (size_of lims [Number acc] LN LN)) +
    (bigest_acc_size lims (acc+x) xs)
End

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
      >- (eval_goalsub_tac ``state_locals_fupd _ _``
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

Theorem le_right_add:
  a ≤ b ⇒ a ≤ b + (c:num)
Proof
  intLib.ARITH_TAC
QED

Theorem bignum_digits_LESS_EQ:
  ∀b m n. n ≤ m ⇒ bignum_digits b n ≤ bignum_digits b m
Proof
  ho_match_mp_tac bignum_digits_ind \\ rw []
  \\ once_rewrite_tac [bignum_digits_def] \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac
  \\ fs [X_LE_DIV]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  THENL [‘0 < 18446744073709551616n’ by fs [], ‘0 < 4294967296n’ by fs []]
  \\ drule DIVISION
  \\ disch_then (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ fs []
QED

Theorem bignum_digits_LESS_EQ_ADD:
  k ≤ bignum_digits f (n + n') ⇒
  k ≤ SUC (bignum_digits f n + bignum_digits f n')
Proof
  rw [] \\ match_mp_tac LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs []
  \\ pop_assum kall_tac
  \\ completeInduct_on ‘n+n'’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ once_rewrite_tac [bignum_digits_def] \\ rw [] \\ fs []
  \\ rewrite_tac [DECIDE “2 = SUC (SUC 0n) ∧ 1 = SUC 0”,ADD_CLAUSES,LESS_EQ_MONO]
  \\ simp [Once bignum_digits_def]
  \\ rw []
  \\ rewrite_tac [DECIDE “2 = SUC (SUC 0n) ∧ 1 = SUC 0”,ADD_CLAUSES,LESS_EQ_MONO]
  \\ qmatch_goalsub_abbrev_tac ‘_ DIV k’
  \\ first_x_assum (qspecl_then [‘n DIV k’,‘n' DIV k’] mp_tac)
  \\ (impl_tac THEN1
   (match_mp_tac (DECIDE “m < n ∧ m' < n' ⇒ m + m' < n + n':num”)
    \\ fs [Abbr‘k’,DIV_LT_X]))
  \\ rw [] \\ match_mp_tac LESS_EQ_TRANS
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ match_mp_tac bignum_digits_LESS_EQ
  \\ ‘0 < k’ by fs [Abbr‘k’]
  \\ fs [DIV_LE_X,DIV_LT_X]
  \\ fs [LEFT_ADD_DISTRIB]
  \\ drule DIVISION
  \\ disch_then (fn th =>
       strip_assume_tac (Q.SPEC ‘n’ th) THEN
       strip_assume_tac (Q.SPEC ‘n'’ th))
  \\ unabbrev_all_tac
  \\ full_simp_tac bool_ss [EVAL “18446744073709551616n²”]
  \\ full_simp_tac bool_ss [EVAL “4294967296n²”]
  \\ decide_tac
QED

Theorem bignum_size_plus:
  bignum_size f (a+b) ≤ bignum_size f a + bignum_size f b
Proof
  fs [bignum_size_def]
  \\ Cases_on ‘a’ \\ fs [] \\ Cases_on ‘b’ \\ fs []
  \\ fs [integerRingTheory.int_calculate] \\ rw []
  \\ rewrite_tac [DECIDE “2 = SUC (SUC 0n) ∧ 1 = SUC 0”,ADD_CLAUSES,LESS_EQ_MONO]
  \\ match_mp_tac bignum_digits_LESS_EQ_ADD \\ fs []
  \\ match_mp_tac bignum_digits_LESS_EQ \\ fs []
QED

Theorem foldl_evaluate:
  ∀vl il s acc ts_f tag_f sstack lsize ssum smax.
    (* Sizes *)
    size_of_stack s.stack = SOME sstack ∧
    s.locals_size = SOME lsize ∧
    lookup_List_foldl s.stack_frame_sizes = SOME lsize ∧
    s.stack_max = SOME smax ∧
    s.space = 0 ∧
    (* Arguments *)
    s.locals = fromList [vl ; Number acc; Block ts_f tag_f [CodePtr_Int_+_clos;Number 1]] ∧
    repint_to_list vl = SOME il ∧
    (* Stack frames *)
    s.stack_frame_sizes = sum_config.word_conf.stack_frame_size ∧
    sum_stack_size s.stack_frame_sizes s.limits acc il = SOME ssum ∧
    (* Limits *)
    smax < s.limits.stack_limit ∧
    sstack + lsize + ssum + 4 < s.limits.stack_limit ∧
    flat_size_of_heap s + bigest_acc_size s.limits acc il +
    bigest_num_size s.limits il + sum_heap_size s acc il ≤ s.limits.heap_limit ∧
    foldadd_limit_ok s.limits acc il ∧
    (* Code *)
    lookup_List_foldl s.code = SOME (3,foldl_body) ∧
    lookup_Int_+_clos s.code = SOME (3,Int_plus_clos_body) ∧
    lookup_Int_+ s.code      = SOME (2,Int_plus_body) ∧
    (* Invariants *)
    size_inv s ∧ (* Needed, since there is no heap allocation in the function *)
    s.safe_for_space ∧
    s.limits.arch_64_bit ∧
    1 < s.limits.length_limit
    ⇒
    ∃res lcls0 lsz0 smax0 clk0 ts0 pkheap0 stk.
     evaluate (foldl_body,s) =
       (SOME res, s with <| locals := lcls0;
                            locals_size := lsz0;
                            stack_max := SOME smax0;
                            clock := clk0;
                            tstamps := ts0;
                            peak_heap_length := pkheap0;
                            stack := stk;
                            space := 0
                            |>) ∧
     clk0 ≤ s.clock ∧
     (res = (Rerr(Rabort Rtimeout_error)) ∨
      ∃sumi. res = Rval (Number sumi) ∧ (stk = s.stack) ∧
             smax0 = MAX smax (lsize + sstack + (if il = [] then 0 else 4) + ssum))
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
  ho_match_mp_tac repint_to_list_ind
  \\ rw[foldl_body_def,Int_plus_body_def,Int_plus_clos_body_def,repint_to_list_def]
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def]
  \\ qpat_x_assum ‘s.locals = _’ (assume_tac o EVAL_RULE)
  >~ [‘Block v2 0 []’]
  >- (strip_assign \\ make_if
     \\ rw [state_component_equality]
     \\ fs [repint_to_list_def] \\ rveq
     \\ fs [sum_stack_size_def] \\ rveq
     \\ fs [])
  \\ strip_assign
  \\ make_if
  \\ rename1`Block ts_vl tag_vl [Number i; vl]`
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
         \\ ‘size_inv s0’ by
           (qpat_x_assum ‘size_inv _’ mp_tac
            \\ gs[Abbr‘s0’,size_inv_def,all_blocks_inv_def,stack_to_vs_def]
            \\ eval_goalsub_tac ``sptree$toList _``
            \\ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
            \\ qmatch_goalsub_abbrev_tac ‘_ ++ rest’
            \\ eval_goalsub_tac ``sptree$toList _``
            \\ rw[all_blocks_roots_inv_def]
            >- (gs[all_blocks_blocks_inv_def]
                \\ qmatch_asmsub_abbrev_tac ‘Block ts_vl _ ll’
                \\ first_x_assum (qspecl_then [‘ts_vl’,‘tag_vl’,‘ll’] mp_tac)
                \\ impl_tac >- (first_x_assum (irule_at Any) \\ simp[Abbr‘ll’])
                \\ simp[Abbr‘ll’]
                \\ qpat_x_assum ‘MEM _ _’ mp_tac
                \\ eval_goalsub_tac “MEM (Block _ _ _) _”
                \\ simp[IN_DEF] \\ rw[]
                >- (first_x_assum (irule_at Any) \\ simp[])
                \\ pop_assum mp_tac
                \\ rw[all_blocks_roots_inv_def]
                \\ first_x_assum irule
                \\ simp[])
          >- (first_x_assum (irule_at Any) \\ simp[]))
         \\ drule size_of_heap_eq_flat_size_of_heap
         \\ pop_assum (simp o single)
         \\ ‘flat_size_of_heap s0 ≤ flat_size_of_heap s + bigest_num_size s.limits (i::z)’ suffices_by
             (Cases_on ‘s_consumed ≤ sum_heap_size s (acc + i) z’ \\ fs [MAX_DEF])
         \\ qunabbrev_tac ‘s0’
         \\ simp [flat_size_of_heap_def,stack_to_vs_def,
                  toList_def,toListA_def,extract_stack_def]
         \\ qmatch_goalsub_abbrev_tac ‘Number acc::rest_v’
         \\ simp[flat_size_of_def]
         \\ qmatch_goalsub_abbrev_tac ‘a + c ≤ b + d’
         \\ ‘c ≤ d ∧ a ≤ b’ suffices_by simp[]
         \\ conj_tac
         >- (UNABBREV_ALL_TAC
             \\ simp[flat_measure_def]
             \\ Cases_on ‘vl’ \\ gs[repint_to_list_def,flat_measure_def]
             \\ qmatch_goalsub_abbrev_tac ‘a + b ≤ c + _’
             \\ ‘b ≤ c’ suffices_by simp[]
             \\ rw[Abbr‘b’,Abbr‘c’,bigest_num_size_def,bignum_size_def,size_of_def])
         \\ simp[Abbr‘a’,Abbr‘b’]
         \\ irule SUM_IMAGE_SUBSET_LE
         \\ conj_tac >- simp[FINITE_reachable_v,FINITE_to_addrs]
         \\ simp[to_addrs_def] \\ simp[Once to_addrs_cons]
         \\ rw[reachable_v_def,SUBSET_DEF,FUN_EQ_THM]
         >- (first_x_assum (irule_at Any) \\ simp[])
         >- (qexists_tac ‘BlockAddr ts_vl’ \\ simp[]
             \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
             \\ disj2_tac \\ first_x_assum (irule_at Any)
             \\ simp[next_def,block_to_addrs_def,IN_DEF]
             \\ gs[size_inv_def,all_blocks_inv_def,all_blocks_roots_inv_def]
             \\ first_x_assum (qspecl_then [‘ts_vl’,‘tag_vl’,‘[Number i; vl]’] mp_tac)
             \\ impl_tac
             >- (simp[stack_to_vs_def,toListA_def,toList_def])
             \\ gs[to_addrs_def,IN_DEF])
         >- (first_x_assum (irule_at Any) \\ simp[]))
     \\ qhdtm_x_assum ‘foldadd_limit_ok’ mp_tac
     \\ simp[foldadd_limit_ok_def]
     \\ disch_then(qspec_then ‘0’ mp_tac) \\ simp[])
  \\ REWRITE_TAC [Int_plus_body_def,to_shallow_thm,to_shallow_def]
  \\ rw [] \\ simp []
  \\ qunabbrev_tac ‘s'’
  \\ simp [pop_env_def,set_var_def]
  \\ qunabbrev_tac ‘rest_call’
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ max_is ‘MAX smax (lsize + sstack + x1 + 4)’
  >- fs [MAX_DEF]
  \\ simp [move_def,lookup_def,set_var_def,lookup_insert]
  \\ IF_CASES_TAC >- rw [state_component_equality]
  \\ qmatch_goalsub_abbrev_tac ‘to_shallow _ s'’
  \\ first_x_assum (qspec_then ‘s'’ mp_tac)
  \\ rveq \\ fs []
  \\ disch_then (qspecl_then [‘acc + i’,‘ts_f’,‘tag_f’] mp_tac)
  \\ disch_then (qspecl_then [‘THE (size_of_stack s'.stack)’,‘THE s'.locals_size’] mp_tac)
  \\ disch_then (qspecl_then [‘x2’,‘THE s'.stack_max’] mp_tac)
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
         \\ pop_assum kall_tac
         \\ qmatch_asmsub_abbrev_tac ‘flat_size_of_heap s  + (cc + (bb + ss))’
         \\ qmatch_goalsub_abbrev_tac ‘flat_size_of_heap s' + (cc' + (bb' + ss'))’
         \\ `ss' ≤ ss` by
            (unabbrev_all_tac \\ simp[sum_heap_size_def])
         \\ ‘cc' ≤ cc’ by
            (unabbrev_all_tac \\ simp[bigest_num_size_def])
         \\ `flat_size_of_heap s' + bb' ≤ flat_size_of_heap s + bb` suffices_by fs[]
         \\ pop_assum kall_tac \\ pop_assum kall_tac
         \\ qunabbrev_tac ‘s'’
         \\ eval_goalsub_tac ``state_locals_fupd _ _``
         \\ simp [flat_size_of_heap_def,stack_to_vs_def,
                  toList_def,toListA_def,extract_stack_def]
         \\ qmatch_goalsub_abbrev_tac ‘Number acc::rest_v’
         \\ simp[flat_size_of_def]
         \\ ONCE_REWRITE_TAC [ADD_ASSOC]
         \\ ONCE_REWRITE_TAC [ADD_ASSOC]
         \\ qmatch_goalsub_abbrev_tac ‘_ + r + a + b ≤ _ + _ + c + d’
         \\ ‘bb' + r + b ≤ bb + r + d ∧ a ≤ c’ suffices_by simp[]
         \\ conj_tac
         >- (UNABBREV_ALL_TAC
             \\ simp[flat_measure_def]
             \\ Cases_on ‘vl’ \\ gs[repint_to_list_def,flat_measure_def]
             \\ simp [size_of_def,sum_heap_size_def,
                      space_consumed_def,bigest_acc_size_def]
             \\ rw [])
         \\ simp[Abbr‘a’,Abbr‘c’]
         \\ irule SUM_IMAGE_SUBSET_LE
         \\ conj_tac >- simp[FINITE_to_addrs,FINITE_reachable_v]
         \\ simp[to_addrs_def] \\ simp[Once to_addrs_cons]
         \\ rw[reachable_v_def,SUBSET_DEF,FUN_EQ_THM]
         >- (first_x_assum (irule_at Any) \\ simp[])
         >- (qexists_tac ‘BlockAddr ts_vl’ \\ simp[]
             \\ irule ((snd o EQ_IMP_RULE o SPEC_ALL) RTC_CASES1)
             \\ disj2_tac \\ first_x_assum (irule_at Any)
             \\ simp[next_def,block_to_addrs_def,IN_DEF]
             \\ gs[size_inv_def,all_blocks_inv_def,all_blocks_roots_inv_def]
             \\ first_x_assum (qspecl_then [‘ts_vl’,‘tag_vl’,‘[Number i; vl]’] mp_tac)
             \\ impl_tac
             >- (simp[stack_to_vs_def,toListA_def,toList_def])
             \\ gs[to_addrs_def,IN_DEF])
         >- (first_x_assum (irule_at Any) \\ gs[to_addrs_def] \\ simp[]))
      >- (imp_res_tac foldadd_limits_ok_step)
      >- (qpat_x_assum ‘size_inv _’ mp_tac
          \\ gs[size_inv_def,all_blocks_inv_def,stack_to_vs_def]
          \\ eval_goalsub_tac ``sptree$toList _``
          \\ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
          \\ qmatch_goalsub_abbrev_tac ‘_ ++ rest’
          \\ eval_goalsub_tac ``sptree$toList _``
          \\ rw[all_blocks_roots_inv_def]
          >- (first_x_assum (irule_at Any) \\ simp[])
          >- (gs[all_blocks_blocks_inv_def]
              \\ qmatch_asmsub_abbrev_tac ‘Block ts_vl _ ll’
              \\ first_x_assum (qspecl_then [‘ts_vl’,‘tag_vl’,‘ll’] mp_tac)
              \\ impl_tac >- (first_x_assum (irule_at Any) \\ simp[Abbr‘ll’])
              \\ rw[all_blocks_roots_inv_def]
              \\ first_x_assum irule
              \\ simp[Abbr‘ll’])
          >- (first_x_assum (irule_at Any) \\ simp[]))
      >- (fs [GREATER_DEF] \\ Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC))
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def,foldl_body_def]
  \\ rw [] \\ qunabbrev_tac ‘s'’ \\ simp []
  \\ simp [state_component_equality,GREATER_DEF] \\ fs []
  >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
  >- (reverse conj_tac
     >- (Cases_on ‘x1 ≤ x2’ \\ fs [MAX_DEF] \\ EVAL_TAC)
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
       (56,112)
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
 \\ ntac 47 strip_assign
 \\ make_tailcall
 \\ ntac 4
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
     \\ UNABBREV_ALL_TAC)
  \\ ntac 6 strip_assign
  \\ ntac 4
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
  \\ strip_makespace
  \\ ntac 3 strip_assign
  \\ make_tailcall
  \\ ntac 3
     (strip_makespace
     \\ ntac 4 strip_assign
     \\ make_tailcall)
  \\ ntac 31 strip_assign
  \\ strip_makespace
  \\ ntac 9 strip_assign
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ irule data_safe_res
  \\ conj_tac >- (Cases \\ simp [] \\ IF_CASES_TAC \\ simp [])
  \\ UNABBREV_ALL_TAC
  \\ strip_call
  \\ ntac 2 strip_assign
  \\ open_tailcall
  \\ qmatch_goalsub_abbrev_tac ‘(bind _ _) st’
  \\ qabbrev_tac ‘vl = THE(sptree$lookup (0:num) st.locals)’
  \\ qabbrev_tac ‘il = THE(repint_to_list vl)’
  \\ qabbrev_tac ‘ssum = THE(sum_stack_size st.stack_frame_sizes st.limits 0 il)’
  \\ qspecl_then [‘vl’,‘il’,‘st’,‘0’,‘1’,‘30’] mp_tac foldl_evaluate
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspecl_then [‘THE(st.stack_max)’,‘ssum’,
                             ‘THE(st.locals_size)’,
                             ‘THE(size_of_stack st.stack)’] mp_tac)
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  (* Prove that the preconditions of foldl_evaluate are satisfied *)
  >- (‘size_inv st’ by
       (simp[Abbr‘st’,size_inv_def,all_blocks_inv_def] \\ EVAL_TAC)
      \\ drule size_of_heap_eq_flat_size_of_heap
      \\ disch_then (simp o single o GSYM)
      \\ unabbrev_all_tac \\ simp[]
      \\ simp[size_of_stack_def,size_of_stack_frame_def]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(SIMP_CONV std_ss [code_lookup,frame_lookup])))
      \\ simp[]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV EVAL))
      \\ simp[]
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac
      >- (simp [sum_stack_size_def,repint_to_list_def,lookup_def,stack_consumed_def,small_num_def,
                word_depthTheory.max_depth_def,data_to_wordTheory.AnyArith_call_tree_def]
          \\ (fn (asm, goal) => let
               val pat   = ``sptree$lookup _ _``
               val terms = find_terms (can (match_term pat)) goal
               val simps = map (PATH_CONV "lr" EVAL) terms
              in ONCE_REWRITE_TAC simps (asm,goal) end)
          \\ simp [frame_lookup])
      \\ conj_tac
      >- (simp [sum_stack_size_def,repint_to_list_def,lookup_def,stack_consumed_def,small_num_def,
                word_depthTheory.max_depth_def,data_to_wordTheory.AnyArith_call_tree_def]
          \\ (fn (asm, goal) => let
               val pat   = ``sptree$lookup _ _``
               val terms = find_terms (can (match_term pat)) goal
               val simps = map (PATH_CONV "lr" EVAL) terms
              in ONCE_REWRITE_TAC simps (asm,goal) end)
          \\ simp [frame_lookup])
      \\ conj_tac
      >- (simp [sum_heap_size_def,repint_to_list_def,lookup_def,
                stack_consumed_def,small_num_def,size_of_heap_def,
                word_depthTheory.max_depth_def,data_to_wordTheory.AnyArith_call_tree_def,
                bignum_size_def,bigest_acc_size_def,bigest_num_size_def,
                foldadd_limit_ok_def,space_consumed_def,size_of_def]
          \\ EVAL_TAC)
      \\ conj_tac
      >- ((* TODO: currently hard-coded to n=5 for no good reason *)
          EVAL_TAC >>
          Cases >- EVAL_TAC >>
          ntac 4 (simp[ADD1] >>
                  rename1 ‘n + _’ >>
                  Cases_on ‘n’ >- EVAL_TAC >>
                  rename1 ‘SUC n’) >>
          simp[] >> EVAL_TAC)
      >- simp[frame_lookup,code_lookup,foldl_body_def,
              Int_plus_clos_body_def,Int_plus_body_def])
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

(* 23% less proof code *)
val _ = export_theory();
