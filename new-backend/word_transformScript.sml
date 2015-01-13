open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory rich_listTheory alistTheory
open BasicProvers
open word_procTheory word_langTheory word_liveTheory
open reg_allocTheory 
open word_ssaTheory

val _ = new_theory "word_transform"

(*This should describe the full theorems resulting 
  from linking up everything and define the full transform

  The theorems that need to be linked can be divided into
  correctness and conventions

  Correctness
  ---
  1) SSA converted program preserves semantics for all? permutes
  2) Calling register allocation produces correct code
  3) Linking up SSA + register allocation into 1 pass

  Conventions
  ---
  1) SSA program has the special conventions on stack variables
  2) Register allocation produces an is_phy_var coloring

  Everything after allocation should be is_phy_var, and
  the stack variables should be ≥ 2*k

*)

val get_spg_def = Define`
  get_spg prog live =
    let (hd,clash_sets) = get_clash_sets prog live in
      (clash_sets_to_sp_g (hd::clash_sets))`

(*Instantiates the register allocator to wordLang liveness analysis*)
val word_alloc_def = Define`
  word_alloc k prog =
  let clash_graph = get_spg prog LN in (*No live after set*)
  let moves = get_prefs prog [] in (*Get the moves in the graph*) 
  let col = reg_alloc clash_graph k moves in (*Get the register allocation function*)
    apply_color (total_color col) prog`

(*word_trans is the combination that does SSA/CC then Register Allocation*)
val word_trans_def = Define`
  word_trans k prog =
  let (ssa_prog,na,ns) = ssa_cc_trans prog LN 101 103 in (*numbers are placeholders*)
    word_alloc k ssa_prog`

(*
Simple evaluation to use while coding:
open sptreeSyntax
open monadsyntax state_transformerTheory

sptreeSyntax.temp_add_sptree_printer();
sptreeSyntax.remove_sptree_printer();

val _ = computeLib.add_funs[MWHILE_DEF]
val rhsThm = rhs o concl;
val reval = rhsThm o EVAL;
val _ = Globals.max_print_depth := 100

val prog = ``
Seq
(Assign 21 (Const 5w))
(Seq
(Move [1,21])
(Seq
(Move [21,1])
(Seq
(Move [1,21])
(Seq
(Move [23,15])
(Seq
(Move [7,11;13,17;19,23])
(Seq (Move [1,2;5,4;3,6])
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)
  ))))))``

val cg = reval ``get_spg ^(prog) LN``;
val moves = reval ``get_prefs ^(prog) []``;
val st = reval ``init_ra_state ^(cg) 5 ^(moves)``

val st = reval``SND(rpt_do_step ^(st))``


EVAL ``word_alloc 5 ^(prog)``

val prog2 = reval ``ssa_cc_trans ^(prog) LN 101 103``

EVAL``word_trans 5 ^(prog)``

val st = reval``SND(do_step ^(st))``
val st = reval ``init_ra_state ^(graph) 50 ^(moves)``

fun println st = (print st;print"\n");

fun repeat st n = 
  let val clock = reval``^(st).clock``
      val ls = reval``LENGTH (let st = ^(st) in FILTER (\x. lookup x (st.coalesced) = NONE) (st.simp_worklist++st.freeze_worklist++st.spill_worklist))``
      val st = reval``SND(do_step ^(st))`` in
      (println (term_to_string clock);println (term_to_string ls);
      if n=0 then st else repeat st (n-1)) end

fun repeat2 st =
  let val clock = reval``^(st).clock``
      val movs = reval``let st = ^(st) in LENGTH st.avail_moves,LENGTH st.unavail_moves``
      val st = reval``SND(do_step ^(st))`` in
      (println (term_to_string movs);
      if (term_to_string clock) ="0" then () else repeat2 st) end

repeat st 100;

val st = reval``rpt_do_step st``

*)

val coloring_satisfactory_coloring_ok_alt = prove(``
  ∀prog f live.
  let spg = get_spg prog live in
  coloring_satisfactory (f:num->num) spg
  ⇒
  coloring_ok_alt f prog live``,
  rpt strip_tac>>
  fs[LET_THM,coloring_ok_alt_def,coloring_satisfactory_def,get_spg_def]>>
  Cases_on`get_clash_sets prog live`>>fs[]>>
  strip_tac>>
  qabbrev_tac `ls = q::r`>>
  qsuff_tac `EVERY (λs. INJ f (domain s) UNIV) ls`
  >-
    fs[Abbr`ls`]
  >>
  rw[EVERY_MEM]>>
  imp_res_tac clash_sets_clique>>
  imp_res_tac coloring_satisfactory_cliques>>
  pop_assum(qspec_then`f`mp_tac)>>
  discharge_hyps
  >- fs[coloring_satisfactory_def,LET_THM]>>
  discharge_hyps
  >- fs[ALL_DISTINCT_MAP_FST_toAList]>>
  fs[INJ_DEF]>>rw[]>>
  fs[domain_lookup]>>
  `MEM x (MAP FST (toAList s)) ∧
   MEM y (MAP FST (toAList s))` by
    (fs[MEM_MAP,EXISTS_PROD]>>
    metis_tac[domain_lookup,MEM_MAP,EXISTS_PROD,MEM_toAList])>>
  `ALL_DISTINCT (MAP FST (toAList s))` by
    metis_tac[ALL_DISTINCT_MAP_FST_toAList]>>
  fs[EL_ALL_DISTINCT_EL_EQ]>>
  fs[MEM_EL]>>rfs[EL_MAP]>>
  metis_tac[])

val call_arg_convention_preservation = prove(``
  ∀prog f.
  every_var (λx. is_phy_var x ⇒ f x = x) prog ∧ 
  call_arg_convention prog ⇒ 
  call_arg_convention (apply_color f prog)``,
  ho_match_mp_tac call_arg_convention_ind>>
  rw[call_arg_convention_def,every_var_def]>>
  EVERY_CASE_TAC>>unabbrev_all_tac>>
  fs[call_arg_convention_def]>>
  `EVERY is_phy_var args` by
    (qpat_assum`args=A` SUBST_ALL_TAC>>
    fs[EVERY_GENLIST,is_phy_var_def]>>
    rw[]>>
    `0<2:num` by DECIDE_TAC>>
    `(2:num)*x=x*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0])>>
 qpat_assum`args = A` (SUBST_ALL_TAC o SYM)>>
 fs[EVERY_MEM,miscTheory.MAP_EQ_ID])

val pre_post_conventions_word_alloc = prove(``
  ∀prog k.
  pre_alloc_conventions prog ⇒ (*this is generated by ssa form*) 
  post_alloc_conventions k (word_alloc k prog)``,
  fs[pre_alloc_conventions_def,post_alloc_conventions_def,word_alloc_def,get_spg_def]>>
  rw[]>>
  `undir_graph clash_graph` by
    metis_tac[clash_sets_to_sp_g_undir]>>
  imp_res_tac reg_alloc_conventional>>
  pop_assum(qspecl_then[`moves`,`k`] assume_tac)>>rfs[LET_THM]>>
  `every_var (in_clash_sets (hd::clash_sets)) prog` by 
     (Q.ISPECL_THEN [`prog`,`LN:num_set`] assume_tac 
       every_var_in_get_clash_set>>
     rfs[LET_THM])>>
  `every_var (λx. x ∈ domain clash_graph) prog` by   
    (match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>rw[]>>
    metis_tac[clash_sets_to_sp_g_domain])>>
  fs[coloring_conventional_def,LET_THM]
  >-
    (match_mp_tac every_var_apply_color>>
    HINT_EXISTS_TAC>>fs[]>>
    rw[]>>
    metis_tac[])
  >-
    (match_mp_tac every_stack_var_apply_color>>
    imp_res_tac every_var_imp_every_stack_var>>
    qexists_tac `λx. (x ∈ domain clash_graph ∧ is_stack_var x)` >>rw[]
    >-
      metis_tac[every_stack_var_conj]
    >>
    metis_tac[convention_partitions])
  >>
  match_mp_tac call_arg_convention_preservation>>
  rw[]>>match_mp_tac every_var_mono>>
  HINT_EXISTS_TAC>>
  metis_tac[])

val _ = export_theory();
