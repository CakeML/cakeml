(*
  Prove of sum space consumption
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory size_ofPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;
open allProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "allProof"

val _ = ParseExtras.temp_tight_equality ()

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val all_x64_conf = (rand o rator o lhs o concl) all_thm

val _ = install_naming_overloads "allProg";
val _ = write_to_file all_data_prog_def;

val foldl_body = ``lookup_List_foldl (fromAList all_data_prog)``
           |> (REWRITE_CONV [all_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand


Definition foldl_body_def:
  foldl_body = ^foldl_body
End

val all_clos_0_body = ``lookup_all_clos_0 (fromAList all_data_prog)``
           |> (REWRITE_CONV [all_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

Definition all_clos_0_body_def:
  all_clos_0_body = ^all_clos_0_body
End

val all_0_body = ``lookup_all_0 (fromAList all_data_prog)``
           |> (REWRITE_CONV [all_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

Definition all_0_body_def:
  all_0_body = ^all_0_body
End

(* boolean list of length l and with timestamps strictly bounded by tsb *)
Definition repbool_list_def:
  (* cons *)
  repbool_list (Block ts _ [Block b_ts b_tag []; rest]) (l:num) (tsb:num) =
     (ts < tsb ∧ l > 0 ∧ (∃b. isBool b (Block b_ts b_tag [])) ∧
      b_ts = 0 ∧ repbool_list rest (l-1) ts) ∧
  (* nil *)
  repbool_list (Block ts tag []) (l:num) tsb = (tag = 0 ∧ l = 0 ∧ ts < tsb) ∧
  (* everything else *)
  repbool_list _ _ _ = F
End

Theorem repbool_list_cases:
  ∀vl n ts. repbool_list vl n ts
   ⇒ (∃ts0 tag0 b b_tag rest. vl = Block ts0 tag0 [Block 0 b_tag []; rest] ∧
                        repbool_list rest (n-1) ts0 ∧
                        isBool b (Block 0 b_tag [])∧
                        ts0 < ts) ∨
     (∃ts0. vl = Block ts0 0 [])
Proof
  ho_match_mp_tac repbool_list_ind
  \\ rw [repbool_list_def,isBool_def]
  \\ Cases_on ‘vb’ \\ fs [isBool_def]
  \\ Cases_on ‘n0’ \\ fs [isBool_def]
  \\ Cases_on ‘l’ \\ fs [isBool_def]
  \\ Cases_on ‘b’ \\ fs [backend_commonTheory.bool_to_tag_def]
QED

Theorem repbool_list_gt:
  ∀v n ts0 ts1.
   ts0 < ts1 ∧ repbool_list v n ts0
   ⇒ repbool_list v n ts1
Proof
 ho_match_mp_tac repbool_list_ind
 \\ rw[repbool_list_def]
QED

Theorem repbool_list_insert_ts:
  ∀xs m ts_vl ts refs1 seen1 lims.
    repbool_list xs m ts_vl ∧ ts_vl ≤ ts
  ⇒ size_of lims [xs] refs1 (insert ts () seen1) =
     (λ(x,y,z). (x,y,insert ts () z)) (size_of lims [xs] refs1 seen1)
Proof
  ho_match_mp_tac repbool_list_ind >> rw[] >> fs[repbool_list_def] >>
  fs[size_of_def] >>
  simp[lookup_insert] >>
  IF_CASES_TAC >- simp[] >>
  rpt(pairarg_tac >> fs[] >> rveq) >>
  rw[Once insert_insert]
QED

Definition repbool_to_tsl_def:
  repbool_to_tsl (Block ts _ [Block 0 b []; rest]) = OPTION_MAP (CONS ts) (repbool_to_tsl rest) ∧
  repbool_to_tsl (Block _ 0 []) = SOME [] ∧
  repbool_to_tsl _ = NONE
End

Theorem repbool_list_to_tsl_SOME:
  ∀l n ts. repbool_list l n ts ⇒ ∃tsl. repbool_to_tsl l = SOME tsl
Proof
  ho_match_mp_tac repbool_list_ind \\ rw [repbool_to_tsl_def,repbool_list_def]
QED

Definition repbool_list_safe_def:
  repbool_list_safe seen [] = T
∧ repbool_list_safe seen (ts::tsl) =
   ((∀ts0. MEM ts0 tsl ∧ IS_SOME (sptree$lookup ts seen) ⇒ IS_SOME (lookup ts0 seen)) ∧
      repbool_list_safe seen tsl)
End

Definition repbool_safe_heap_def:
  repbool_safe_heap s ivl =
     let (_,_,seen) = size_of s.limits (FLAT (MAP extract_stack s.stack) ++
                               global_to_vs s.global) s.refs LN
     in repbool_list_safe seen ivl
End

Theorem repbool_list_size_of_rm:
∀tsl ivl n ts limits refs seen.
  repbool_list ivl n ts ∧
  repbool_to_tsl ivl = SOME tsl ∧
  (∀ts0. MEM ts0 tsl ⇒ IS_SOME (lookup ts0 seen))
  ⇒ ∃refs1 seen1. size_of limits [ivl] refs seen = (0,refs1,seen1)
Proof
  Induct \\ rw []
  >- (Cases_on ‘ivl’ \\ fs [repbool_list_def]
      \\ Cases_on ‘l’ \\ fs [repbool_list_def]
      >- fs [size_of_def]
      \\ rveq \\ rfs [repbool_to_tsl_def,size_of_def]
      \\ Cases_on ‘h’  \\ fs [repbool_list_def]
      \\ Cases_on ‘t’  \\ fs [repbool_list_def]
      \\ Cases_on ‘t'’ \\ fs [repbool_list_def]
      \\ Cases_on ‘l’  \\ fs [repbool_list_def]
      \\ rveq \\ fs [repbool_to_tsl_def])
  \\ Cases_on ‘ivl’ \\ fs [repbool_list_def]
  \\ Cases_on ‘l’ \\ fs [repbool_list_def]
  >- fs [size_of_def]
  \\ rveq \\ rfs [repbool_to_tsl_def,size_of_def]
  \\ Cases_on ‘t’  \\ fs [repbool_list_def]
  \\ Cases_on ‘h'’  \\ fs [repbool_list_def]
  \\ Cases_on ‘t'’ \\ fs [repbool_list_def]
  \\ Cases_on ‘l’  \\ fs [repbool_list_def]
  \\ rveq \\ fs [repbool_to_tsl_def]
QED

Theorem repbool_list_seen_MEM:
∀tsl ivl n0 ts0 ts lims refs seen n refs0 seen0.
  repbool_list ivl n0 ts0 ∧
  repbool_to_tsl ivl = SOME tsl ∧
  ¬ MEM ts tsl ∧
  size_of lims [ivl] refs seen = (n,refs0,seen0)
  ⇒ lookup ts seen = lookup ts seen0
Proof
  Induct \\ rw []
  >- (Cases_on ‘ivl’ \\ fs [repbool_list_def]
      \\ Cases_on ‘l’ \\ fs [repbool_list_def]
      >- fs [size_of_def]
      \\ rveq \\ rfs [repbool_to_tsl_def,size_of_def]
      \\ Cases_on ‘t’  \\ fs [repbool_list_def]
      \\ Cases_on ‘h’  \\ fs [repbool_list_def]
      \\ Cases_on ‘t'’ \\ fs [repbool_list_def]
      \\ Cases_on ‘l’  \\ fs [repbool_list_def]
      \\ rveq \\ fs [repbool_to_tsl_def])
  \\ Cases_on ‘ivl’ \\ fs [repbool_list_def]
  \\ Cases_on ‘l’ \\ fs [repbool_list_def]
  >- fs [size_of_def]
  \\ rveq \\ rfs [repbool_to_tsl_def,size_of_def]
  \\ Cases_on ‘t’  \\ fs [repbool_list_def]
  \\ Cases_on ‘h'’  \\ fs [repbool_list_def]
  \\ Cases_on ‘t'’ \\ fs [repbool_list_def]
  \\ Cases_on ‘l’  \\ fs [repbool_list_def]
  \\ rveq \\ fs [repbool_to_tsl_def]
  \\ Cases_on ‘IS_SOME (lookup n0' seen)’ \\ fs [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ first_x_assum drule_all
  \\ fs [lookup_insert] \\ rfs []
QED

val fields = TypeBase.fields_of “:('c,'ffi) dataSem$state”;

Overload state_locals_fupd = (fields |> assoc "locals" |> #fupd);
Overload state_stack_max_fupd = (fields |> assoc "stack_max" |> #fupd);
Overload state_safe_for_space_fupd = (fields |> assoc "safe_for_space" |> #fupd);

Theorem foldl_evaluate:
  ∀n s vl ts_f tag_f tag_acc tsl sstack lsize smax ts.
    (* Sizes *)
    size_of_stack s.stack = SOME sstack ∧
    s.locals_size = SOME lsize ∧
    lookup_List_foldl s.stack_frame_sizes = SOME lsize ∧
    s.stack_max = SOME smax ∧
    s.space = 0 ∧
    (* Arguments *)
    s.locals = fromList [vl ; Block 0 tag_acc []; Block ts_f tag_f [CodePtr_all_clos_0;Number 1]] ∧
    (∃b. isBool b (Block 0 tag_acc [])) ∧
    repbool_list vl n ts ∧
    repbool_to_tsl vl = SOME tsl ∧
    ¬ MEM ts_f tsl ∧
    repbool_safe_heap s tsl ∧
    (* Stack frames *)
    s.stack_frame_sizes = all_config.word_conf.stack_frame_size ∧
    (* Limits *)
    smax < s.limits.stack_limit ∧
    sstack + lsize < s.limits.stack_limit ∧
    size_of_heap s ≤ s.limits.heap_limit ∧
    (* Code *)
    lookup_List_foldl s.code      = SOME (3,foldl_body) ∧
    lookup_all_clos_0 s.code = SOME (3,all_clos_0_body) ∧
    lookup_all_0 s.code      = SOME (2,all_0_body) ∧
    (* Invariants *)
    s.safe_for_space ∧
    s.limits.arch_64_bit ∧
    s.tstamps = SOME ts ∧
    1 < s.limits.length_limit
    ⇒
    ∃res lcls0 lsz0 smax0 clk0 ts0 stk.
     evaluate (foldl_body,s) =
       (SOME res, s with <| locals := lcls0;
                            locals_size := lsz0;
                            stack_max := SOME smax0;
                            clock := clk0;
                            stack := stk;
                            |>) ∧
     clk0 ≤ s.clock ∧
     (res = (Rerr(Rabort Rtimeout_error)) ∨
      ∃sumi b b_tag. res = Rval (Block 0 b_tag []) ∧
                   (isBool b (Block 0 b_tag [])) ∧
                   (stk = s.stack) ∧
                   smax0 = MAX smax (lsize + sstack))
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
  fun max_is t =
    qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _` >>
    subgoal ‘max0 = SOME (^(Term t))’
    THENL
    [(Q.UNABBREV_TAC ‘max0’ \\ fs [small_num_def,size_of_stack_def]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
in
  completeInduct_on`n`
  \\ rw[foldl_body_def,all_clos_0_body_def,all_0_body_def]
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def]
  \\ qpat_x_assum ‘s.locals = _’ (assume_tac o EVAL_RULE)
  \\ drule repbool_list_cases \\ reverse (rw [])
  \\ fs [repbool_list_def]
  >- (strip_assign \\ make_if
      \\ rw [state_component_equality]
      \\ Cases_on ‘b’ \\ fs [isBool_def,backend_commonTheory.bool_to_tag_def]
      \\ rveq \\ rw [backend_commonTheory.true_tag_def,backend_commonTheory.false_tag_def]
      \\ metis_tac [])
  \\ strip_assign
  \\ make_if
  \\ ntac 4 strip_assign
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ make_if
  \\ strip_assign
  \\ max_is ‘MAX smax (lsize + sstack)’
  >- fs [MAX_DEF]
  \\ strip_call
  \\ open_tailcall
  \\ max_is ‘MAX smax (lsize + sstack)’
  >- fs [MAX_DEF]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ ‘safe’ by
     (qunabbrev_tac ‘safe’ \\ fs [size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  \\ make_if
  \\ simp [pop_env_def,set_var_def]
  \\ reverse (Cases_on ‘tag_acc = 0 ∨ tag_acc = 1’)
  >- (fs [isBool_def] \\ Cases_on ‘b’
      \\ fs [backend_commonTheory.true_tag_def,
             backend_commonTheory.false_tag_def,
             backend_commonTheory.bool_to_tag_def])
  \\ rw []
  \\ TRY (strip_assign \\ simp [return_def,lookup_def,flush_state_def])
  \\ max_is ‘MAX smax (lsize + sstack)’
  \\ TRY (fs [MAX_DEF] \\ NO_TAC)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ ‘safe’ by
     (qunabbrev_tac ‘safe’ \\ fs [size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  \\ eval_goalsub_tac ``state_locals_fupd _ _``
  \\ qunabbrev_tac ‘rest_call’
  \\ simp [move_def,lookup_def,set_var_def,lookup_insert]
  \\ IF_CASES_TAC
  \\ TRY (rw [state_component_equality] \\ NO_TAC)
  \\ first_x_assum (qspec_then ‘n - 1’ mp_tac)
  \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘to_shallow _ s'’
  \\ fs [repbool_to_tsl_def] \\ rveq
  >- (disch_then (qspecl_then [‘s'’,‘rest’,‘ts_f’,‘tag_f’,‘b_tag’,‘z’] mp_tac)
      \\ disch_then (qspecl_then [‘THE (size_of_stack s'.stack)’,‘THE s'.locals_size’] mp_tac)
      \\ disch_then (qspecl_then [‘THE s'.stack_max’,‘ts’] mp_tac)
      \\ impl_tac
      >- (qunabbrev_tac ‘s'’
          \\ rw [frame_lookup,foldl_body_def,all_clos_0_body_def,all_0_body_def]
          \\ rfs []
          >- metis_tac []
          >- (irule repbool_list_gt \\ asm_exists_tac \\ fs [])
          >- (fs [repbool_safe_heap_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [repbool_list_safe_def])
          >- (qmatch_goalsub_abbrev_tac ‘size_of_heap s'’
              \\ ‘size_of_heap s' ≤ size_of_heap s’ suffices_by fs []
              \\ qunabbrev_tac ‘s'’
              \\ eval_goalsub_tac ``state_locals_fupd _ _``
              \\ simp [size_of_heap_def,stack_to_vs_def,toList_def,toListA_def]
              \\ qmatch_goalsub_abbrev_tac ‘f1::f2::Block 0 1 []::rest_v’
              \\ qmatch_goalsub_abbrev_tac ‘f1::rest::f3::rest_v’
              \\ qmatch_goalsub_abbrev_tac ‘_ (size_of _ ff1 _ _) ≤ _ (size_of _ ff2 _ _)’
              \\ ‘ff1 = [f1;rest;f3] ++ rest_v’ by rw [Abbr‘ff1’]
              \\ rveq \\ pop_assum kall_tac
              \\ ‘ff2 = [f1;f2;Block 0 1 []] ++ rest_v’ by rw [Abbr‘ff2’]
              \\ rveq \\ pop_assum kall_tac
              \\ simp [size_of_append]
              \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
              \\ fs [Abbr ‘f3’,size_of_def]
              \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
              \\ qpat_x_assum ‘size_of _ (_::rest_v) _ _ = _’ mp_tac
              \\ simp[Once size_of_cons,size_of_def] \\ rw[] \\ gs[] \\ rveq
              \\ qpat_x_assum ‘size_of _ (_::rest_v) _ _ = _’ mp_tac
              \\ simp[Once size_of_cons,size_of_def] \\ rw[] \\ gs[] \\ rveq
              \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
              \\ rename1 ‘a1 + b1 ≤ a2 + b2’
              \\ ‘a1 ≤ a2 ∧ b1 ≤ b2’ suffices_by rw []
              \\ conj_tac
              >- (qunabbrev_tac ‘f2’
                  \\ fs [repbool_to_tsl_def,repbool_safe_heap_def] \\ rveq
                  \\ fs [repbool_list_safe_def] \\ rveq
                  \\ fs [size_of_def]
                  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
                  \\ Cases_on ‘IS_SOME (lookup ts0 seen1')’
                  \\ fs [] \\ rveq \\ fs []
                  >- (drule_all repbool_list_size_of_rm
                      \\ disch_then (qspecl_then [‘s.limits’,‘refs1’] mp_tac)
                      \\ rw [])
                  \\ drule repbool_list_insert_ts
                  \\ disch_then (qspecl_then [‘ts0’,‘refs1'’,‘seen1'’,‘s.limits’] mp_tac)
                  \\ fs [])
              \\ qunabbrev_tac ‘f1’ \\ fs [size_of_def]
              \\ ‘lookup ts_f seen1' = lookup ts_f seen1''’
                 by metis_tac [repbool_list_seen_MEM]
              \\ ‘lookup ts_f seen1' = lookup ts_f seen1’
                 by (irule repbool_list_seen_MEM
                     \\ ‘¬ MEM ts_f (ts0::z)’ by fs []
                     \\ asm_exists_tac \\ fs []
                     \\ qexists_tac ‘f2’
                     \\ qunabbrev_tac ‘f2’
                     \\ fs [repbool_to_tsl_def,repbool_list_def]
                     \\ metis_tac [])
              \\ ntac 2 (pop_assum mp_tac)
              \\ ntac 2 (disch_then (assume_tac o GSYM))
              \\ fs [] \\ Cases_on ‘IS_SOME (lookup ts_f seen1')’
              \\ fs [])
          \\ fs [MAX_DEF,libTheory.the_def])
      \\ REWRITE_TAC[to_shallow_thm,to_shallow_def,foldl_body_def]
      \\ rw [] \\ qunabbrev_tac ‘s'’ \\ simp []
      \\ simp [state_component_equality,GREATER_DEF,libTheory.the_def]
      \\ fs [MAX_DEF]
      \\ fs [isBool_def] \\ Cases_on ‘b'''’
      \\ fs [backend_commonTheory.true_tag_def,
             backend_commonTheory.false_tag_def,
             backend_commonTheory.bool_to_tag_def]
      \\ metis_tac [])
  \\ disch_then (qspecl_then [‘s'’,‘rest’,‘ts_f’,‘tag_f’,‘0’,‘z’] mp_tac)
  \\ disch_then (qspecl_then [‘THE (size_of_stack s'.stack)’,‘THE s'.locals_size’] mp_tac)
  \\ disch_then (qspecl_then [‘THE s'.stack_max’,‘ts’] mp_tac)
  \\ impl_tac
  >- (qunabbrev_tac ‘s'’
      \\ rw [frame_lookup,foldl_body_def,all_clos_0_body_def,all_0_body_def]
      \\ rfs []
      \\ fs [size_of_stack_def] (* Extra *)
      >- (fs [isBool_def,backend_commonTheory.bool_to_tag_def,
              backend_commonTheory.true_tag_def,
              backend_commonTheory.false_tag_def]
          \\ metis_tac []) (* Extra/maybe not *)
      >- (irule repbool_list_gt \\ asm_exists_tac \\ fs [])
      >- (fs [repbool_safe_heap_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [repbool_list_safe_def])
      >- (qmatch_goalsub_abbrev_tac ‘size_of_heap s'’
          \\ ‘size_of_heap s' ≤ size_of_heap s’ suffices_by fs []
          \\ qunabbrev_tac ‘s'’
          \\ eval_goalsub_tac ``state_locals_fupd _ _``
          \\ simp [size_of_heap_def,stack_to_vs_def,toList_def,toListA_def]
          \\ qmatch_goalsub_abbrev_tac ‘_ (size_of _ (f1::rest::_::rest_v) _ _) ≤
                                        _ (size_of _ (_::f2::_) _ _)’
          \\ qmatch_goalsub_abbrev_tac ‘_ (size_of _ ff1 _ _) ≤ _ (size_of _ ff2 _ _)’
          \\ ‘ff1 = [f1;rest;Block 0 0 []] ++ rest_v’ by rw [Abbr‘ff1’]
          \\ rveq \\ pop_assum kall_tac
          \\ ‘ff2 = [f1;f2;Block 0 0 []] ++ rest_v’ by rw [Abbr‘ff2’]
          \\ rveq \\ pop_assum kall_tac
          \\ simp [size_of_append]
          \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
          \\ fs [size_of_def]
          \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
          \\ qpat_x_assum ‘size_of _ (_::rest_v) _ _ = _’ mp_tac
          \\ simp[Once size_of_cons,size_of_def] \\ rw[] \\ gs[] \\ rveq
          \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
          \\ rename1 ‘a1 + b1 ≤ a2 + b2’
          \\ ‘a1 ≤ a2 ∧ b1 ≤ b2’ suffices_by rw []
          \\ conj_tac
          >- (qunabbrev_tac ‘f2’
              \\ fs [repbool_to_tsl_def,repbool_safe_heap_def] \\ rveq
              \\ fs [repbool_list_safe_def] \\ rveq
              \\ fs [size_of_def]
              \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs []
              \\ Cases_on ‘IS_SOME (lookup ts0 seen1')’
              \\ fs [] \\ rveq \\ fs []
              >- (drule_all repbool_list_size_of_rm
                  \\ disch_then (qspecl_then [‘s.limits’,‘refs1’] mp_tac)
                  \\ rw [])
              \\ drule repbool_list_insert_ts
              \\ disch_then (qspecl_then [‘ts0’,‘refs1'’,‘seen1'’,‘s.limits’] mp_tac)
              \\ fs [])
          \\ qunabbrev_tac ‘f1’ \\ fs [size_of_def]
          \\ ‘lookup ts_f seen1' = lookup ts_f seen1''’
            by metis_tac [repbool_list_seen_MEM]
          \\ ‘lookup ts_f seen1' = lookup ts_f seen1’
            by (irule repbool_list_seen_MEM
                \\ ‘¬ MEM ts_f (ts0::z)’ by fs []
                \\ asm_exists_tac \\ fs []
                \\ qexists_tac ‘f2’
                \\ qunabbrev_tac ‘f2’
                \\ fs [repbool_to_tsl_def,repbool_list_def]
                \\ metis_tac [])
          \\ ntac 2 (pop_assum mp_tac)
          \\ ntac 2 (disch_then (assume_tac o GSYM))
          \\ fs [] \\ Cases_on ‘IS_SOME (lookup ts_f seen1')’
          \\ fs [])
      \\ fs [MAX_DEF,libTheory.the_def,size_of_stack_def])
  \\ REWRITE_TAC[to_shallow_thm,to_shallow_def,foldl_body_def]
  \\ rw [] \\ qunabbrev_tac ‘s'’ \\ simp [] \\ fs [size_of_stack_def]
  \\ simp [state_component_equality,GREATER_DEF,libTheory.the_def]
  \\ fs [MAX_DEF]
  \\ fs [isBool_def] \\ Cases_on ‘b'''’
  \\ fs [backend_commonTheory.true_tag_def,
         backend_commonTheory.false_tag_def,
         backend_commonTheory.bool_to_tag_def]
  \\ metis_tac []
end
QED

Theorem data_safe_all:
  ∀ffi.
  backend_config_ok ^all_x64_conf
  ⇒ is_safe_for_space ffi
       all_x64_conf
       all_prog
       (* (s_size,h_size) *)
       (56,103) (* Tightest values *)
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
 \\ ntac 47 strip_assign
 \\ make_tailcall
 \\ ntac 14
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
 \\ ntac 6 strip_assign
 \\ ntac 14
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
  \\ ntac 13
     (TRY strip_makespace
     \\ ntac 4 (TRY strip_assign)
     \\ make_tailcall)
  \\ strip_assign
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ irule data_safe_res
  \\ conj_tac >- (Cases \\ simp [] \\ IF_CASES_TAC \\ simp [])
  \\ UNABBREV_ALL_TAC
  \\ strip_call
  \\ strip_makespace
  \\ ntac 4 strip_assign
  \\ open_tailcall
  \\ qmatch_goalsub_abbrev_tac ‘(bind _ _) st’
  \\ qabbrev_tac ‘vl = THE(sptree$lookup (0:num) st.locals)’
  \\ qabbrev_tac ‘tsl = THE(repbool_to_tsl vl)’
  \\ qspecl_then [‘LENGTH tsl’,‘st’,‘vl’,‘8’,‘30’,‘true_tag’,‘tsl’] mp_tac foldl_evaluate
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspecl_then [‘THE(st.stack_max)’,
                             ‘THE(st.locals_size)’,
                             ‘THE(size_of_stack st.stack)’] mp_tac)
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (unabbrev_all_tac \\ simp []
      \\ simp[size_of_stack_def,size_of_stack_frame_def]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(SIMP_CONV std_ss [code_lookup,frame_lookup])))
      \\ simp[]
      \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV EVAL))
      \\ simp[]
      \\ conj_tac >- (qexists_tac ‘T’ \\ EVAL_TAC)
      \\ conj_tac
      >- (EVAL_TAC
          \\  metis_tac[backend_commonTheory.true_tag_def,
                        backend_commonTheory.false_tag_def,
                        backend_commonTheory.bool_to_tag_def])
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- (EVAL_TAC \\ rw[] \\ rw[lookup_def])
      \\ conj_tac >- EVAL_TAC
      \\ simp[frame_lookup,code_lookup,foldl_body_def,all_clos_0_body_def,all_0_body_def])
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
