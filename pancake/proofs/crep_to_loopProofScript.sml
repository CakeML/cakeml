(*
  Correctness proof for ---
*)

open preamble
     crepSemTheory crepPropsTheory
     loopLangTheory loopSemTheory loopPropsTheory
     pan_commonTheory pan_commonPropsTheory
     listRangeTheory rich_listTheory
     loop_liveProofTheory crep_to_loopTheory

val _ = new_theory "crep_to_loopProof";

val _ = set_grammar_ancestry
        ["listRange", "rich_list", "crepProps",
         "loopProps", "pan_commonProps",
         "loop_liveProof", "crep_to_loop"];

val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"];

Theorem evaluate_nested_seq_append_first =
evaluate_nested_seq_cases |> CONJUNCT1
Theorem evaluate_none_nested_seq_append =
      evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT1
Theorem evaluate_not_none_nested_seq_append =
      evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT2

(* state relation *)

val s = ``(s:('a,'ffi) crepSem$state)``

Definition state_rel_def:
  state_rel (s:('a,'ffi) crepSem$state) (t:('a,'ffi) loopSem$state) <=>
   s.memaddrs = t.mdomain ∧
   s.clock = t.clock ∧
   s.be = t.be ∧
   s.ffi = t.ffi ∧
   s.base_addr = t.base_addr
End

(*
  Loc encodes label of a function, e.g:
  Loc n1 n2 represents the label n2
  inside the function n1
*)

Definition wlab_wloc_def:
  (wlab_wloc _ (Word w) = Word w) /\
  (wlab_wloc funcs (Label fname) =
   case FLOOKUP funcs fname of
    | SOME (n, _) =>  Loc n 0
    | NONE =>  Loc 0 0)  (* impossible *)
End

Definition mem_rel_def:
  mem_rel funcs smem tmem <=>
  !ad. wlab_wloc funcs (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n m. FLOOKUP funcs f = SOME (n, m)
End

Definition globals_rel_def:
  globals_rel funcs sglobals tglobals <=>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc funcs v) /\
     !f. v = Label f ==>
      ?n m. FLOOKUP funcs f = SOME (n, m)
End

Definition distinct_funcs_def:
  distinct_funcs fm <=>
    !x y n m rm rm'. FLOOKUP fm x = SOME (n, rm) /\
       FLOOKUP fm y = SOME (m, rm') /\ n = m ==> x = y
End

(* could have been stated differently *)
Definition ctxt_fc_def:
  ctxt_fc cvs ns args =
    <|vars := FEMPTY |++ ZIP (ns, args);
      funcs := cvs;
      vmax := list_max args|>
End

Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
   distinct_funcs ctxt.funcs /\
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc len. FLOOKUP ctxt.funcs f = SOME (loc, len) /\
       LENGTH ns = len /\
       let args = GENLIST I len;
           nctxt = ctxt_fc ctxt.funcs ns args in
       lookup loc t_code =
          SOME (args,
                ocompile nctxt (list_to_num_set args) prog)
End

Definition ctxt_max_def:
  ctxt_max (n:num) fm <=>
   !v m. FLOOKUP fm v = SOME m ==> m <= n
End

Definition distinct_vars_def:
  distinct_vars fm <=>
    (!x y n m. FLOOKUP fm x = SOME n /\
               FLOOKUP fm y = SOME m /\ n = m ==> x = y)
End

Definition locals_rel_def:
  locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals <=>
  distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc ctxt.funcs v) /\
    !f. v = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ mem_rel ctxt.funcs s.memory t.memory ∧
      globals_rel ctxt.funcs s.globals t.globals ∧
      code_rel ctxt s.code t.code ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃ck res1 t1. evaluate (compile ctxt l prog,
                             t with clock := t.clock + ck) = (res1,t1) /\
      state_rel s1 t1 ∧ mem_rel ctxt.funcs s1.memory t1.memory ∧
      globals_rel ctxt.funcs s1.globals t1.globals ∧
      code_rel ctxt s1.code t1.code ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt l s1.locals t1.locals

       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt l s1.locals t1.locals
        | SOME Continue => res1 = SOME Continue /\
                           locals_rel ctxt l s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt.funcs v)) /\
                            (!f. v = Label f ==> f ∈ FDOM ctxt.funcs)
       | SOME (Exception eid) => res1 = SOME (Exception (Word eid))
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | SOME Error => F``

local
  val ind_thm = crepSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_prog_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem state_rel_intro:
  state_rel ^s (t:('a,'ffi) loopSem$state) <=>
  s.memaddrs = t.mdomain ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  s.base_addr = t.base_addr
Proof
  rw [state_rel_def]
QED

Theorem locals_rel_intro:
  locals_rel ctxt l (s_locals:num |-> 'a word_lab) t_locals ==>
   distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
   ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc ctxt.funcs v) /\
    !f. v = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
Proof
  rw [locals_rel_def]
QED

Theorem code_rel_intro:
  code_rel ctxt s_code t_code ==>
  distinct_funcs ctxt.funcs /\
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc len. FLOOKUP ctxt.funcs f = SOME (loc, len) /\
       LENGTH ns = len /\
       let args = GENLIST I len;
           nctxt = ctxt_fc ctxt.funcs ns args in
       lookup loc t_code =
          SOME (args,
                ocompile nctxt (list_to_num_set args) prog)
Proof
  rw [code_rel_def]
QED

Theorem mem_rel_intro:
  mem_rel funcs smem tmem ==>
   !ad. wlab_wloc funcs (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n m. FLOOKUP funcs f = SOME (n, m)
Proof
  rw [mem_rel_def] >>
  metis_tac []
QED

Theorem globals_rel_intro:
  globals_rel funcs sglobals tglobals ==>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc funcs v) /\
     !f. v = Label f ==>
      ?n m. FLOOKUP funcs f = SOME (n, m)
Proof
  rw [globals_rel_def] >> metis_tac []
QED

Theorem state_rel_clock_add_zero:
  !s t. state_rel s t ==>
   ?ck. state_rel s (t with clock := ck + t.clock)
Proof
  rw [] >>
  qexists_tac ‘0’ >>
  fs [state_rel_def, state_component_equality]
QED

Theorem locals_rel_insert_gt_vmax:
  !ct cset lcl lcl' n w.
   locals_rel ct cset lcl lcl' /\ ct.vmax < n ==>
    locals_rel ct cset lcl (insert n w lcl')
Proof
  rw [] >>
  fs [locals_rel_def, SUBSET_INSERT_RIGHT, AllCaseEqs(),
      lookup_insert, ctxt_max_def] >>
  rw [] >> rpt (res_tac >> fs [])
QED

Theorem locals_rel_cutset_prop:
  !ct cset lcl lcl' cset' lcl''.
   locals_rel ct cset lcl lcl' /\
   locals_rel ct cset' lcl lcl'' /\
   subspt cset cset' ==>
    locals_rel ct cset lcl lcl''
Proof
  rw [locals_rel_def]
  >- metis_tac [subspt_domain, SUBSET_TRANS] >>
  res_tac >> fs [] >> rveq >> fs []
QED

Theorem write_bytearray_mem_rel:
  !nb funcs sm tm w dm be.
   mem_rel funcs sm tm ==>
   mem_rel funcs (write_bytearray w nb sm dm be)
   (write_bytearray w nb tm dm be)
Proof
  Induct >>
  rw [panSemTheory.write_bytearray_def,
      wordSemTheory.write_bytearray_def] >>
  TOP_CASE_TAC >> fs []
  >- (
   ‘mem_store_byte_aux (write_bytearray (w + 1w) nb tm dm be) dm be
    w h = NONE’ suffices_by fs [] >>
   fs [panSemTheory.mem_store_byte_def,
       wordSemTheory.mem_store_byte_aux_def,
       CaseEq "word_lab", CaseEq "option"]
   >- (TOP_CASE_TAC >> fs []) >>
   first_x_assum drule >>
   disch_then (qspecl_then [‘w+1w’, ‘dm’, ‘be’] mp_tac) >>
   strip_tac >> fs [] >>
   last_x_assum kall_tac >>
   fs [mem_rel_def] >>
   first_x_assum (qspec_then ‘byte_align w’ mp_tac) >>
   strip_tac >>
   rfs [] >> pop_assum mp_tac >>
   pop_assum (mp_tac o GSYM) >>
   rw [] >> fs [wlab_wloc_def]) >>
  fs [panSemTheory.mem_store_byte_def,
      wordSemTheory.mem_store_byte_aux_def,
      CaseEq "word_lab", CaseEq "option"] >>
  rveq >>
  first_x_assum drule >>
  disch_then (qspecl_then [‘w+1w’, ‘dm’, ‘be’] mp_tac) >>
  strip_tac >> fs [] >>
  fs [mem_rel_def] >>
  rw []
  >- (
   fs [APPLY_UPDATE_THM] >>
   TOP_CASE_TAC >> fs []
   >- (
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    rfs [] >> pop_assum (assume_tac o GSYM) >>
    fs [] >>
    fs [wlab_wloc_def] >>
    fs [APPLY_UPDATE_THM]) >>
   TOP_CASE_TAC >> fs [CaseEq "word_loc", CaseEq "option"]
   >- (
    first_x_assum (qspec_then ‘byte_align w’ assume_tac) >>
    rfs [wlab_wloc_def]) >>
   rveq >> fs [APPLY_UPDATE_THM]) >>
  fs [APPLY_UPDATE_THM] >>
  FULL_CASE_TAC >> fs [] >>
  res_tac >> fs []
QED

(*
Theorem mem_rel_ctxt_vmax_preserve:
  mem_rel (ctxt with vmax := m) s.memory t.memory ==>
  mem_rel ctxt s.memory t.memory
Proof
  rw [mem_rel_def] >>
  fs [] >>
  first_x_assum (qspec_then ‘ad’ assume_tac) >>
  fs [] >>
  cases_on ‘s.memory ad’ >>
  cases_on ‘t.memory ad’ >>
  fs [wlab_wloc_def]
QED


Theorem globals_rel_ctxt_vmax_preserve:
  globals_rel (ctxt with vmax := m) s.globals t.globals ==>
  globals_rel ctxt s.globals t.globals
Proof
  rw [globals_rel_def] >>
  fs [] >>
  TRY (cases_on ‘v’) >>
  fs [wlab_wloc_def] >>
  res_tac >> fs [wlab_wloc_def]
QED
*)

Theorem evaluate_comb_seq:
  !p s t q r.
    loopSem$evaluate (p,s) = (NONE, t) /\ loopSem$evaluate (q,t) = (NONE,r) ==>
    loopSem$evaluate (Seq p q,s) = (NONE,r)
Proof
  rw [] >>
  fs [evaluate_def]
QED


Theorem compile_exp_out_rel_cases:
  (!ct tmp l (e:'a crepLang$exp) p le ntmp nl.
    compile_exp ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p)) /\
  (!ct tmp l (e:'a crepLang$exp list) p le ntmp nl.
    compile_exps ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p) /\
    LENGTH le = LENGTH e)
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  fs [Once compile_exp_def] >> rveq >>
  TRY (pairarg_tac >> fs [] >> rveq >> NO_TAC) >>
  fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def] >> NO_TAC)
  >- (
   rename [‘compile_exp _ _ _ (Label f)’] >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, cut_sets_def] >>
   match_mp_tac comp_syn_ok_seq2 >>
   fs [comp_syn_ok_basic_cases])
  >- (
   rename [‘compile_exp _ _ _ (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   conj_asm1_tac
   >- (
    fs [compile_exp_def] >>
    pairarg_tac >> fs [] >> rveq >> fs [] >>
    match_mp_tac comp_syn_ok_nested_seq >>
    fs [] >>
    fs [nested_seq_def] >>
    rpt (
    match_mp_tac comp_syn_ok_seq2 >>
    fs [comp_syn_ok_basic_cases])) >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   res_tac >> fs [] >>
   imp_res_tac comp_syn_ok_nested_seq2 >>
   last_x_assum assume_tac >>
   qmatch_goalsub_abbrev_tac ‘p' ++ np’ >>
   fs [cut_sets_nested_seq] >>
   fs [Abbr ‘np’] >> pop_assum kall_tac >>
   fs [nested_seq_def, cut_sets_def, Once insert_insert])
  >- (
   rename [‘compile_exp _ _ _ (Op _ _)’] >>
   fs [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   cases_on ‘e’
   >- fs [compile_exp_def] >>
   fs [] >>
   fs [Once compile_exp_def])
  >- (
   rename [‘compile_exp _ _ _ (Cmp _ _ _)’] >>
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   conj_tac
   >- (
    fs [prog_if_def] >>
    match_mp_tac comp_syn_ok_nested_seq >>
    conj_tac
    >- (
     match_mp_tac comp_syn_ok_nested_seq >>
     fs []) >>
    fs [list_insert_def, nested_seq_def, cut_sets_def] >>
    rpt (match_mp_tac comp_syn_ok_seq2 >>
         fs [comp_syn_ok_basic_cases]) >>
    fs [cut_sets_def] >>
    rw [Once comp_syntax_ok_def, list_insert_def] >>
    fs [cut_sets_nested_seq] >>
    qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
    match_mp_tac EQ_SYM >>
    ‘insert t1 () (insert t2 () (insert t1 () cc)) = insert t2 () (insert t1 () cc)’ by (
      ‘insert t2 () (insert t1 () cc) = insert t1 () (insert t2 () cc)’
        by (fs [Abbr ‘t1’, Abbr ‘t2’] >> match_mp_tac insert_swap >> fs []) >>
      fs [Abbr ‘t1’, Abbr ‘t2’] >> fs [Once insert_insert]) >>
    fs [] >> pop_assum kall_tac >>
    fs [Once insert_insert]) >>
   conj_tac >- (res_tac >> fs []) >>
   res_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘list_insert _ ll’ >>
   fs [prog_if_def] >>
   qmatch_goalsub_abbrev_tac ‘p' ++ p'' ++ np’ >>
   ‘comp_syntax_ok l (nested_seq (p' ++ p''))’ by (
     match_mp_tac comp_syn_ok_nested_seq >>
     fs []) >>
   ‘comp_syntax_ok (cut_sets l (nested_seq (p' ++ p''))) (nested_seq np)’ by (
     fs [Abbr ‘np’, nested_seq_def] >>
     ntac 3 (rw [Once comp_syntax_ok_def]) >>
     rw [Once comp_syntax_ok_def, cut_sets_def, Abbr ‘l''’, list_insert_def] >>
     fs [cut_sets_nested_seq] >>
     qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
     match_mp_tac EQ_SYM >>
     ‘insert t1 () (insert t2 () (insert t1 () cc)) = insert t2 () (insert t1 () cc)’ by (
       ‘insert t2 () (insert t1 () cc) = insert t1 () (insert t2 () cc)’
         by (fs [Abbr ‘t1’, Abbr ‘t2’] >> match_mp_tac insert_swap >> fs []) >>
       fs [Abbr ‘t1’, Abbr ‘t2’] >> fs [Once insert_insert]) >>
     fs [] >> pop_assum kall_tac >>
     fs [Once insert_insert]) >>
   qpat_x_assum ‘comp_syntax_ok l (nested_seq (p' ++ p''))’ assume_tac >>
   fs [cut_sets_nested_seq] >>
   fs [Abbr ‘np’, nested_seq_def, cut_sets_def]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >>
   rveq >> fs [] >>
   fs [nested_seq_def, Once comp_syntax_ok_def, every_prog_def, cut_sets_def]) >>
  pop_assum mp_tac >>
  once_rewrite_tac [compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘t’
  >- (
   fs [compile_exp_def] >>
   strip_tac >> rveq >> fs []) >>
  strip_tac >> fs [] >> rveq >>
  conj_tac >- metis_tac [subspt_trans, comp_syn_ok_nested_seq] >>
  fs [cut_sets_nested_seq]
QED

Theorem compile_exp_out_rel = compile_exp_out_rel_cases |> CONJUNCT1
Theorem compile_exps_out_rel = compile_exp_out_rel_cases |> CONJUNCT2


Theorem comp_exp_assigned_vars_tmp_bound_cases:
  (!ct tmp l (e :α crepLang$exp) p le ntmp nl n.
    compile_exp ct tmp l e = (p,le,ntmp,nl) /\ MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp) /\
  (!ct tmp l (e :α crepLang$exp list) p le ntmp nl n.
    compile_exps ct tmp l e = (p,le,ntmp,nl) /\ MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp)
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  fs [Once compile_exp_def] >> TRY (pairarg_tac >> fs []) >>
  rveq >> fs [nested_seq_def, assigned_vars_def] >> NO_TAC)
  >- (
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   drule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   fs [assigned_vars_nested_seq_split]
   >- (res_tac >> fs []) >>
   fs [nested_seq_def, assigned_vars_def])
  >- (
   once_rewrite_tac [compile_exp_def] >> fs [] >> strip_tac >>
   pairarg_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [compile_exp_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [prog_if_def] >>
   ‘tmp <= tmp' /\ tmp' <= tmp''’ by metis_tac [compile_exp_out_rel_cases] >>
   dxrule compile_exp_out_rel >>
   dxrule compile_exp_out_rel >>
   strip_tac >> fs [] >>
   fs [assigned_vars_nested_seq_split]
   >- (res_tac >> fs [])
   >- (res_tac >> fs []) >>
   fs [nested_seq_def] >>
   fs [assigned_vars_seq_split, assigned_vars_def]) >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> fs [] >>
  once_rewrite_tac [compile_exp_def] >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def]) >>
  pop_assum mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> rveq >> fs [] >>
  strip_tac >>
  ‘tmp <= tmp' /\ tmp' <= ntmp’ by metis_tac [compile_exp_out_rel_cases] >>
  fs [assigned_vars_nested_seq_split] >>
  res_tac >> fs []
QED

Theorem comp_exp_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT1
Theorem comp_exps_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT2

Theorem compile_exp_le_tmp_domain_cases:
  (!ct tmp l (e:'a crepLang$exp) p le tmp' l' n.
    ctxt_max ct.vmax ct.vars /\
    compile_exp ct tmp l e = (p,le,tmp', l') /\ ct.vmax < tmp /\
    (!n. MEM n (var_cexp e) ==> ?m. FLOOKUP ct.vars n = SOME m /\ m ∈ domain l) /\
    MEM n (locals_touched le) ==> n < tmp' /\ n ∈ domain l') /\
  (!ct tmp l (es:'a crepLang$exp list) p les tmp' l' n.
    ctxt_max ct.vmax ct.vars /\
    compile_exps ct tmp l es = (p,les,tmp', l') /\ ct.vmax < tmp /\
    (!n. MEM n (FLAT (MAP var_cexp es)) ==> ?m. FLOOKUP ct.vars n = SOME m /\ m ∈ domain l) /\
    MEM n (FLAT (MAP locals_touched les)) ==> n < tmp' /\ n ∈ domain l')
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  rename [‘Op bop es’] >>
  rpt gen_tac >>
  strip_tac >>
  qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  strip_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [locals_touched_def, crepLangTheory.var_cexp_def, ETA_AX]) >>
  TRY (
  rename [‘compile_exps’] >>
  rpt gen_tac >>
  strip_tac >>
  qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  cases_on ‘es’ >> fs [] >> rveq
  >- (
   strip_tac >> rveq >>
   fs [MAP]) >>
  strip_tac >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  ‘tmp <= tmp'' /\ tmp'' <= tmp' /\ l'' = cut_sets l (nested_seq p') /\
     l' = cut_sets l'' (nested_seq p1)’ by
    metis_tac [compile_exp_out_rel_cases] >>
  fs [MAP]
  >- (
   res_tac >> fs [subspt_domain] >>
   drule compile_exps_out_rel >>
   strip_tac >>
   drule cut_sets_union_domain_union >>
   strip_tac >> fs []) >>
  last_x_assum match_mp_tac >>
  fs [] >>
  rw [] >>
  res_tac >> fs [subspt_domain] >>
  drule compile_exp_out_rel >>
  strip_tac >>
  drule cut_sets_union_domain_union >>
  strip_tac >> fs [] >> NO_TAC) >>
  fs [compile_exp_def] >>
  TRY (pairarg_tac >> fs []) >> rveq >>
  TRY (pairarg_tac >> fs []) >> rveq >>
  fs [locals_touched_def, find_var_def, crepLangTheory.var_cexp_def,
      ctxt_max_def, list_insert_def] >>
  rfs [] >> rveq >> res_tac >> fs []
QED

Theorem compile_exp_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT1
Theorem compile_exps_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT2


Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) ctxt tmp l p le ntmp nl.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt.funcs s.memory t.memory /\
  globals_rel ctxt.funcs s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exp ctxt tmp l e = (p,le, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt.funcs v) /\
     state_rel s st /\ mem_rel ctxt.funcs s.memory st.memory /\
     globals_rel ctxt.funcs s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt nl s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
  rename [‘eval s (Op op es)’] >>
  rw [] >>
  fs [Once compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
  fs [loopSemTheory.eval_def, wlab_wloc_def] >>
  qsuff_tac ‘∃ck st.
    evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) ∧
    the_words (MAP (λa. eval st a) les) =
    SOME ((MAP (λw. case w of Word n =>  n | Label v1 => ARB) ws)) /\
    state_rel s st ∧ mem_rel ctxt.funcs s.memory st.memory ∧
    globals_rel ctxt.funcs s.globals st.globals ∧
    code_rel ctxt s.code st.code ∧ locals_rel ctxt l' s.locals st.locals’
  >- (
   strip_tac >>
   qexists_tac ‘ck’ >>
   fs [wlab_wloc_def]) >>
  qpat_x_assum ‘word_op _ _ = _’ kall_tac >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘t’, ‘p’, ‘les’ , ‘tmp’, ‘l’,‘ws’, ‘es’] >>
  Induct
  >- (
   rw [] >>
   fs [OPT_MMAP_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, loopSemTheory.evaluate_def,
       wordSemTheory.the_words_def, state_rel_clock_add_zero]) >>
  rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘compile_exps _ _ _ (h::_) = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >>
  fs [] >> pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> rveq >>
  fs [OPT_MMAP_def] >> rveq >>
  last_x_assum (qspec_then ‘h’ mp_tac) >>
  fs [] >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ h = (p,le,itmp,il)’ >>
  qmatch_asmsub_rename_tac ‘compile_exps _ _ _ _ = (fp,les,ntmp,nl)’ >>
  last_x_assum (qspecl_then
                [‘t'’, ‘il’, ‘itmp’, ‘les’, ‘fp’, ‘st’] mp_tac) >>
  fs [] >>
  imp_res_tac compile_exp_out_rel >>
  fs [] >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq p, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  qexists_tac ‘ck + ck'’ >>
  qexists_tac ‘st'’ >>
  fs [] >>
  cases_on ‘h'’ >> fs [] >>
  fs [wordSemTheory.the_words_def] >>
  ‘eval st' le = eval st le’ suffices_by fs [wlab_wloc_def] >>
  imp_res_tac compile_exps_out_rel >>
  qpat_x_assum ‘evaluate (nested_seq fp, _) = _’ assume_tac >>
  drule comp_syn_ok_upd_local_clock >>
  disch_then drule >>
  fs [] >> strip_tac >>
  qpat_x_assum ‘evaluate (nested_seq p,_) = _’ mp_tac >>
  once_rewrite_tac [ADD_ASSOC] >>
  strip_tac >>
  fs [wlab_wloc_def] >>
  assume_tac nested_seq_pure_evaluation >>
  pop_assum (qspecl_then [‘p’, ‘fp’, ‘t’, ‘st'’, ‘st with clock := ck' + st.clock’, ‘l’,
                          ‘itmp’, ‘le’, ‘Word c’, ‘ck + ck'’, ‘0’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   fs [eval_upd_clock_eq] >>
   drule comp_exp_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   drule comp_exps_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   gen_tac >>
   strip_tac >> fs [] >>
   imp_res_tac locals_rel_intro >>
   drule compile_exp_le_tmp_domain >>
   disch_then (qspecl_then [‘tmp’, ‘l’, ‘h’, ‘p’, ‘le’,
                            ‘itmp’, ‘cut_sets l (nested_seq p)’, ‘n’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    rw [] >>
    drule eval_some_var_cexp_local_lookup >>
    disch_then drule >>
    strip_tac >> res_tac >> fs []) >>
   fs []) >>
  fs []) >>
  TRY (
  rename [‘Const w’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, evaluate_def, eval_def,
      wlab_wloc_def, state_rel_clock_add_zero]) >>
  TRY (
  rename [‘eval s (Var vname)’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, evaluate_def, find_var_def] >>
  imp_res_tac locals_rel_intro >>
  fs [eval_def, state_rel_clock_add_zero]) >>
  TRY (
   rename [‘eval s (Label fname)’] >>
   fs [crepSemTheory.eval_def, compile_exp_def, CaseEq "option"] >>
   rveq >>
   qexists_tac ‘0’ >> fs [] >>
   ‘t with clock := t.clock = t’ by fs [state_component_equality] >>
   fs [] >> pop_assum kall_tac >>
   fs [nested_seq_def, evaluate_def, find_lab_def] >>
   cases_on ‘v1’ >> rveq >>
   imp_res_tac code_rel_intro >>
   fs [eval_def, set_var_def, domain_lookup, wlab_wloc_def,
       state_rel_def, locals_rel_def, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   first_x_assum drule >> fs [] >>
   strip_tac >> fs [] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   first_x_assum drule >> fs []) >>
  TRY (
  rename [‘eval s (Load e)’] >>
  fs [crepSemTheory.eval_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >>
  fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  last_x_assum drule_all >> fs [] >> rveq >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def] >>
  fs [crepSemTheory.mem_load_def, loopSemTheory.mem_load_def] >> rveq >>
  imp_res_tac state_rel_intro >>
  imp_res_tac mem_rel_intro >>
  last_x_assum (qspec_then ‘c’ mp_tac) >> fs []) >>
  TRY (
  rename [‘eval s (LoadByte e)’] >>
  fs [crepSemTheory.eval_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >>
  fs [compile_exp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  last_x_assum drule_all >>
  fs [] >> rveq >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign tmp' le'; LoadByte tmp' tmp']’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
  fs [nested_seq_def, loopSemTheory.evaluate_def] >>
  fs [set_var_def, wlab_wloc_def] >>
  fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
      wordSemTheory.mem_load_byte_aux_def] >>
  imp_res_tac mem_rel_intro >>
  last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
  strip_tac >> fs [] >>
  last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
  strip_tac >> fs [wlab_wloc_def] >>
  imp_res_tac state_rel_intro >>
  fs [eval_def, state_rel_def] >>
  imp_res_tac compile_exp_out_rel >>
  fs [locals_rel_def, SUBSET_INSERT_RIGHT] >> rw [] >>
  first_x_assum drule >> fs [] >>
  strip_tac >> fs [] >>
  fs [lookup_insert] >>
  TOP_CASE_TAC >> fs [] >>
  fs [ctxt_max_def] >>
  first_x_assum drule >> fs []) >>
  TRY (
  rename [‘eval s (LoadGlob gadr)’] >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, loopSemTheory.evaluate_def] >>
  fs [eval_def] >>
  imp_res_tac globals_rel_intro >>
  fs [] >>
  qexists_tac ‘0’ >> fs [] >>
  ‘t with clock := t.clock = t’ suffices_by fs [] >>
  fs [state_component_equality]) >>
  TRY (
  rename [‘Shift’] >>
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab",
      compile_exp_def] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [loopSemTheory.evaluate_def] >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  fs [loopSemTheory.eval_def, wlab_wloc_def])
  >-(
  rw [] >>
  fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> fs [compile_exp_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [prog_if_def] >>
   last_x_assum drule_all >>
   strip_tac >> fs [] >> rveq >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e = (p1,le1,tmp1,l1)’ >>
   qmatch_asmsub_rename_tac ‘compile_exp _ _ _ e' = (p2,le2,tmp2,l2)’ >>
   last_x_assum (qspecl_then [‘st’, ‘ctxt’, ‘tmp1’, ‘l1’] mp_tac) >>
   fs [] >>
   imp_res_tac compile_exp_out_rel >> fs [] >> rveq >>
   strip_tac >> fs [] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ _ ++ np)’ >>
   qpat_x_assum ‘evaluate (nested_seq p1,_) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'’ assume_tac) >>
   drule evaluate_comb_seq >>
   disch_then drule >>
   fs [evaluate_nested_seq_comb_seq] >>
   strip_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   fs [] >>
   qexists_tac ‘ck + ck' + 1’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘np’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [Abbr ‘np’, nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [eval_upd_clock_eq] >>
   ‘eval st' le1 = eval st le1’ by (
     qpat_x_assum ‘_ = (_, st)’ assume_tac >>
     drule nested_seq_pure_evaluation >>
     disch_then (qspecl_then [‘p2’, ‘st'’, ‘l’, ‘tmp1’, ‘le1’, ‘Word w1’, ‘ck'’] mp_tac) >>
     fs [wlab_wloc_def] >>
     impl_tac
     >- (
      imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
      gen_tac >>
      strip_tac >> fs [] >>
      imp_res_tac locals_rel_intro >>
      drule compile_exp_le_tmp_domain >>
      disch_then (qspecl_then [‘tmp’, ‘l’, ‘e’, ‘p1’, ‘le1’,
                               ‘tmp1’, ‘cut_sets l (nested_seq p1)’, ‘n’] mp_tac) >>
      fs [] >>
      impl_tac
      >- (
       rw [] >>
       imp_res_tac eval_some_var_cexp_local_lookup >>
       res_tac >> fs []) >>
      fs []) >>
     fs []) >>
   fs [] >> rfs [] >>
   pop_assum kall_tac >>
   rveq >>
   fs [wlab_wloc_def, loopSemTheory.set_var_def,
       loopSemTheory.eval_def] >>
   fs [Once eval_upd_locals_clock_eq] >>
   ‘eval (st' with locals := insert (tmp2 + 1) (Word w1) st'.locals) le2 =
    eval st' le2’ by (
     ho_match_mp_tac locals_touched_eq_eval_eq >>
     fs [] >> rw [] >> fs [lookup_insert] >>
     TOP_CASE_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then
                 [‘tmp1’, ‘cut_sets l (nested_seq p1)’, ‘e'’, ‘p2’, ‘le2’, ‘tmp2’,
                  ‘cut_sets (cut_sets l (nested_seq p1)) (nested_seq p2)’,
                  ‘n’] mp_tac) >>
     impl_tac
     >- (
      fs [] >>
      rw [] >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> res_tac >> fs [] >> rveq >> fs []) >>
     fs []) >>
   fs [] >>
   pop_assum kall_tac >>
   fs [] >> rfs [] >> rveq >>
   fs [lookup_insert] >>
   fs [get_var_imm_def, list_insert_def] >>
   cases_on ‘word_cmp cmp w1 w2’ >>
   fs [loopSemTheory.evaluate_def, loopSemTheory.eval_def,
       loopSemTheory.set_var_def] >> (
   fs [cut_res_def, list_insert_def] >>
   fs [cut_state_def] >>
   imp_res_tac locals_rel_intro >>
   fs [SUBSET_INSERT_RIGHT] >>
   rveq >> fs [dec_clock_def] >>
   fs [lookup_inter, lookup_insert] >>
   conj_tac >- EVAL_TAC >>
   conj_tac >- fs [state_rel_def] >>
   fs [list_insert_def, locals_rel_def, domain_inter, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   fs [lookup_inter, lookup_insert] >>
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <= tmp2’ by (fs [ctxt_max_def] >> res_tac >> fs []) >>
   fs [domain_lookup])) >>
  fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
  fs [nested_seq_def, evaluate_def, eval_def, wlab_wloc_def, state_rel_clock_add_zero]>>
  qexists_tac ‘0’ >>
  fs[state_rel_def, state_component_equality]
QED

Theorem comp_exps_preserves_eval:
  ∀es s vs (t :('a, 'b) state) ctxt tmp l p les ntmp nl.
  OPT_MMAP (eval s) es = SOME vs /\
  state_rel s t /\ mem_rel ctxt.funcs s.memory t.memory /\
  globals_rel ctxt.funcs s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exps ctxt tmp l es = (p,les, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     OPT_MMAP (eval st) les = SOME (MAP (wlab_wloc ctxt.funcs) vs) /\
     state_rel s st /\ mem_rel ctxt.funcs s.memory st.memory /\
     globals_rel ctxt.funcs s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt nl s.locals st.locals
Proof
  Induct >> rw []
  >- (
   fs [OPT_MMAP_def] >> rveq >>
   fs [Once compile_exp_def] >> rveq >>
   fs [nested_seq_def] >>
   fs [evaluate_def] >>
   fs [OPT_MMAP_def] >>
   qexists_tac ‘0’ >> fs [state_rel_def]) >>
  fs [OPT_MMAP_def] >> rveq >> fs [] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once compile_exp_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  strip_tac >> strip_tac >> fs [] >> rveq >>
  fs [OPT_MMAP_def] >>
  drule_all comp_exp_preserves_eval >>
  strip_tac >> fs [] >>
  first_x_assum drule >>
  disch_then (qspecl_then [‘st’, ‘ctxt’, ‘tmp'’ , ‘l'’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel_cases >> fs []) >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck + ck'’ >> fs [] >>
  qpat_x_assum ‘evaluate (_,_) = (NONE,st)’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘p1’ mp_tac) >>
  strip_tac >> fs [] >>
  assume_tac nested_seq_pure_evaluation >>
  pop_assum (qspecl_then [‘p'’, ‘p1’, ‘t’, ‘st'’, ‘st’, ‘l’,
                          ‘tmp'’, ‘le’, ‘wlab_wloc ctxt.funcs h'’, ‘ck’, ‘ck'’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel_cases >>
   fs [] >> rveq >> fs [] >>
   drule comp_exp_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   drule comp_exps_assigned_vars_tmp_bound >> fs [] >>
   strip_tac >>
   gen_tac >>
   strip_tac >> fs [] >>
   imp_res_tac locals_rel_intro >>
   drule compile_exp_le_tmp_domain >>
   disch_then (qspecl_then [‘tmp’, ‘l’, ‘h’, ‘p'’, ‘le’,
                            ‘tmp'’, ‘cut_sets l (nested_seq p')’, ‘n’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    rw [] >>
    drule eval_some_var_cexp_local_lookup >>
    disch_then drule >>
    strip_tac >> res_tac >> fs []) >>
   fs []) >>
  fs []
QED


Theorem member_cutset_survives_comp_exp_cases:
  (!ct tmp l (e:'a crepLang$exp) p le ntmp nl n.
   n ∈ domain l /\
   compile_exp ct tmp l e = (p,le,ntmp,nl) ==>
     survives n (nested_seq p)) /\
  (!ct tmp l (e:'a crepLang$exp list) p le ntmp nl n.
   n ∈ domain l /\
   compile_exps ct tmp l e = (p,le,ntmp,nl) ==>
     survives n (nested_seq p))
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
   fs [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   fs [nested_seq_def, survives_def] >> NO_TAC)
  >- (
   fs [compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [])
  >- (
   rw [] >>
   fs [compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   match_mp_tac survives_nested_seq_intro >>
   fs [nested_seq_def, survives_def])
  >- (
   rw [] >>
   pop_assum mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [])
  >- (
   rw [] >>
   pop_assum mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [prog_if_def] >>
   match_mp_tac survives_nested_seq_intro >>
   conj_tac
   >- (
    match_mp_tac survives_nested_seq_intro >>
    fs [] >>
    pop_assum mp_tac >>
    drule compile_exp_out_rel >>
    strip_tac >> fs [] >> rveq >>
    drule cut_sets_union_domain_subset >>
    rpt strip_tac >>
    ‘n ∈ domain (cut_sets l (nested_seq p'))’ by
      fs [SUBSET_DEF] >>
    fs []) >>
   fs [nested_seq_def, survives_def] >>
   fs [list_insert_def] >>
   imp_res_tac compile_exp_out_rel >> rveq >>
   fs [] >>
   imp_res_tac cut_sets_union_domain_subset >>
   fs [SUBSET_DEF])
  >- (
   rw [] >>
   pop_assum mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs []) >>
  rpt gen_tac >> strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, survives_def]) >>
  pop_assum mp_tac >>
  once_rewrite_tac [compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘t’
  >- (
   fs [compile_exp_def] >>
   strip_tac >> rveq >> fs []) >>
  strip_tac >> fs [] >> rveq >>
  match_mp_tac survives_nested_seq_intro >>
  imp_res_tac compile_exp_out_rel >> rveq >>
  fs [] >>
  imp_res_tac cut_sets_union_domain_subset >>
  fs [SUBSET_DEF]
QED


Theorem member_cutset_survives_comp_exp =
     member_cutset_survives_comp_exp_cases |> CONJUNCT1
Theorem member_cutset_survives_comp_exps =
     member_cutset_survives_comp_exp_cases |> CONJUNCT2


Theorem member_cutset_survives_comp_prog:
  !ctxt l p n.
   n ∈ domain l ==>
   survives n (compile ctxt l p)
Proof
  ho_match_mp_tac compile_ind >>
  rw [] >> fs [] >>
  TRY (
  fs [compile_def, survives_def, AllCaseEqs()] >>
  TRY (rpt TOP_CASE_TAC) >>
  TRY (pairarg_tac) >> fs [survives_def] >>
  rveq >> fs [] >>
  TRY (match_mp_tac survives_nested_seq_intro) >>
  fs [nested_seq_def, survives_def] >>
  metis_tac [member_cutset_survives_comp_exp] >> NO_TAC) >>
  TRY (
  fs [compile_def, survives_def, AllCaseEqs()] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  match_mp_tac survives_nested_seq_intro >>
  fs [nested_seq_def, survives_def] >>
  match_mp_tac survives_nested_seq_intro >>
  conj_tac >- metis_tac [member_cutset_survives_comp_exp] >>
  pop_assum mp_tac >>
  drule compile_exp_out_rel >>
  strip_tac >> fs [] >> rveq >>
  drule cut_sets_union_domain_subset >>
  rpt strip_tac >>
  ‘n ∈ domain (cut_sets l (nested_seq p))’ by
    fs [SUBSET_DEF] >>
  metis_tac [member_cutset_survives_comp_exp] >> NO_TAC)
  >- (
   fs [compile_def, survives_def, AllCaseEqs()] >>
   pairarg_tac >> fs [] >>
   match_mp_tac survives_nested_seq_intro >>
   fs [nested_seq_def, survives_def] >>
   match_mp_tac survives_nested_seq_intro >>
   conj_tac >- metis_tac [member_cutset_survives_comp_exps] >>
   match_mp_tac nested_assigns_survives >>
   fs [gen_temps_def]) >>
  fs [compile_def, survives_def, AllCaseEqs()] >>
  pairarg_tac >> fs [] >>
  match_mp_tac survives_nested_seq_intro >>
  conj_tac
  >- (
   match_mp_tac survives_nested_seq_intro >>
   conj_tac >- metis_tac [member_cutset_survives_comp_exps] >>
   match_mp_tac nested_assigns_survives >>
   fs [gen_temps_def]) >>
  fs [nested_seq_def, survives_def] >>
  TRY (rpt TOP_CASE_TAC) >>
  fs [survives_def]
QED


Theorem not_mem_assigned_mem_gt_comp_exp_cases:
  (!ctxt tmp l (e:'a crepLang$exp) p le ntmp nl n.
    compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
    ctxt_max ctxt.vmax ctxt.vars /\
    (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧ n < tmp ==>
      ~MEM n (assigned_vars (nested_seq p))) /\
  (!ctxt tmp l (e:'a crepLang$exp list) p le ntmp nl n.
    compile_exps ctxt tmp l e = (p,le,ntmp,nl) /\
     ctxt_max ctxt.vmax ctxt.vars /\
     (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧ n < tmp ==>
      ~MEM n (assigned_vars (nested_seq p)))
Proof
  ho_match_mp_tac compile_exp_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
   fs [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   fs [nested_seq_def, assigned_vars_def] >> NO_TAC)
  >- (
   fs [compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [])
  >- (
   rw [] >>
   fs [compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   fs [assigned_vars_nested_seq_split] >>
   fs [nested_seq_def, assigned_vars_def] >>
   drule compile_exp_out_rel >>
   strip_tac >> fs [])
  >- (
   rw [] >>
   qpat_x_assum ‘compile_exp _ _ _ (Op _ _) = _’ mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [])
  >- (
   rw [] >>
   qpat_x_assum ‘compile_exp _ _ _ (Cmp _ _ _) = _’ mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   fs [prog_if_def] >>
   fs [assigned_vars_nested_seq_split] >>
   fs [nested_seq_def, assigned_vars_def] >>
   imp_res_tac compile_exp_out_rel >>
   fs [])
  >- (
   rw [] >>
   qpat_x_assum ‘compile_exp _ _ _ (Shift _ _ _) = _’ mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs()] >> rveq >>
   pairarg_tac >> fs []) >>
  rpt gen_tac >> strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
   fs [compile_exp_def] >> rveq >>
   fs [nested_seq_def, assigned_vars_def]) >>
  qpat_x_assum ‘compile_exps _ _ _ _ = _’ mp_tac >>
  once_rewrite_tac [compile_exp_def] >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘t’
  >- (
   fs [compile_exp_def] >>
   strip_tac >> rveq >> fs []) >>
  strip_tac >> fs [] >> rveq >>
  fs [assigned_vars_nested_seq_split] >>
  imp_res_tac compile_exp_out_rel >>
  fs []
QED

Theorem not_mem_assigned_mem_gt_comp_exp =
      not_mem_assigned_mem_gt_comp_exp_cases |> CONJUNCT1
Theorem not_mem_assigned_mem_gt_comp_exps =
      not_mem_assigned_mem_gt_comp_exp_cases |> CONJUNCT2

Theorem not_mem_context_assigned_mem_gt:
  !ctxt l p n.
   ctxt_max ctxt.vmax ctxt.vars /\
   (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧
   n <= ctxt.vmax ==>
   ~MEM n (assigned_vars (compile ctxt l p))
Proof
  ho_match_mp_tac compile_ind >> rw [] >>
  TRY (
  fs [compile_def, assigned_vars_def] >> NO_TAC) >>
  TRY (
  fs [compile_def, assigned_vars_def] >>
  pairarg_tac >> fs [] >>
  fs [assigned_vars_nested_seq_split] >>
  conj_tac
  >- (drule not_mem_assigned_mem_gt_comp_exp >> strip_tac >>
      res_tac >> fs []) >>
  imp_res_tac compile_exp_out_rel >>
  fs [nested_seq_def, assigned_vars_def] >> NO_TAC) >>
  TRY (
  fs [compile_def, assigned_vars_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  fs [assigned_vars_nested_seq_split] >>
  imp_res_tac compile_exp_out_rel >> rveq >>
  conj_tac
  >- (
   conj_tac >>
   imp_res_tac not_mem_assigned_mem_gt_comp_exp >>
   res_tac >> fs []) >>
  fs [nested_seq_def, assigned_vars_def] >> NO_TAC)
  >- (
   fs [compile_def, assigned_vars_def] >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   fs [assigned_vars_nested_seq_split] >>
   drule compile_exp_out_rel >> strip_tac >>
   fs [] >> rveq >>
   drule not_mem_assigned_mem_gt_comp_exp >> strip_tac >>
   fs [nested_seq_def, assigned_vars_def] >>
   CCONTR_TAC >> fs [] >>
   fs [ctxt_max_def] >>
   res_tac >> rfs [])
  >- (
   fs [compile_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   fs [assigned_vars_def] >>
   conj_tac
   >- (
    imp_res_tac not_mem_assigned_mem_gt_comp_exp >>
    res_tac >> fs []) >>
   conj_tac
   >- (drule compile_exp_out_rel >> strip_tac >> fs []) >>
   drule compile_exp_out_rel >>
   strip_tac >> rveq >> fs [] >>
   last_x_assum match_mp_tac >> fs [] >>
   conj_tac
   >- (
    fs [ctxt_max_def] >>
    rw [FLOOKUP_UPDATE] >>
    res_tac >> fs []) >>
   rw [FLOOKUP_UPDATE] >>
   res_tac >> fs [])
  >- (
   fs [compile_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   drule compile_exp_out_rel >>
   strip_tac >> rveq >> fs [] >>
   fs [assigned_vars_def,
       assigned_vars_nested_seq_split, nested_seq_def] >>
   drule not_mem_assigned_mem_gt_comp_exp >>
   res_tac >> fs [])
  >- (
   fs [compile_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   drule compile_exps_out_rel >>
   strip_tac >> rveq >> fs [] >>
   fs [assigned_vars_def,
       assigned_vars_nested_seq_split, nested_seq_def] >>
   conj_tac
   >- (
    imp_res_tac not_mem_assigned_mem_gt_comp_exps >>
    res_tac >> fs []) >>
   ‘assigned_vars
    (nested_seq (MAP2 Assign (gen_temps tmp (LENGTH es + 1)) les)) =
    gen_temps tmp (LENGTH es + 1)’ by (
     match_mp_tac assigned_vars_nested_assign >>
     fs [gen_temps_def]) >>
   fs [] >>
   fs [gen_temps_def] >>
   CCONTR_TAC >> fs [MEM_GENLIST])
  >- (
   fs [compile_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   drule compile_exps_out_rel >>
   strip_tac >> rveq >> fs [] >>
   fs [assigned_vars_def,
       assigned_vars_nested_seq_split, nested_seq_def] >>
   conj_tac
   >- (
    conj_tac
    >- (
     imp_res_tac not_mem_assigned_mem_gt_comp_exps >>
     res_tac >> fs []) >>
    ‘assigned_vars
     (nested_seq (MAP2 Assign (gen_temps tmp (LENGTH es + 1)) les)) =
     gen_temps tmp (LENGTH es + 1)’ by (
      match_mp_tac assigned_vars_nested_assign >>
      fs [gen_temps_def]) >>
    fs [] >>
    fs [gen_temps_def] >>
    CCONTR_TAC >> fs [MEM_GENLIST]) >>
   conj_tac
   >- (
    cases_on ‘rt’ >>
    fs [rt_var_def] >>
    TOP_CASE_TAC >> fs [] >>
    CCONTR_TAC >> fs [] >>
    fs [ctxt_max_def] >>
    res_tac >> rfs []) >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   TOP_CASE_TAC >> fs [assigned_vars_def]) >>
  fs [compile_def, assigned_vars_def] >>
  rpt (TOP_CASE_TAC) >> fs [] >> rveq >>
  fs [assigned_vars_def]
QED



Theorem compile_Skip_Break_Continue:
  ^(get_goal "compile _ _ crepLang$Skip") /\
  ^(get_goal "compile _ _ crepLang$Break") /\
  ^(get_goal "compile _ _ crepLang$Continue")
Proof
  rpt strip_tac >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def] >> rveq >>
  fs [state_rel_clock_add_zero]
QED

Theorem compile_Tick:
  ^(get_goal "compile _ _ crepLang$Tick")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  fs [state_rel_def, empty_locals_def,
      crepSemTheory.dec_clock_def, dec_clock_def] >>
  qexists_tac ‘0’ >> fs []
QED

Theorem compile_Seq:
  ^(get_goal "compile _ _ (crepLang$Seq _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def] >>
  pairarg_tac >> fs [] >>
  cases_on ‘res' = NONE’ >> fs [] >> rveq
  >- (
   fs [compile_def] >>
   fs [evaluate_def] >>
   first_x_assum drule_all >>
   strip_tac >> fs [] >>
   first_x_assum  drule_all >>
   strip_tac >> fs [] >>
   qexists_tac ‘ck + ck'’ >> rfs [] >>
   qpat_x_assum ‘_ (compile _ _ c1, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs []) >>
  fs [compile_def] >>
  fs [evaluate_def] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> rfs [] >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs []
QED


Theorem compile_Return:
  ^(get_goal "compile _ _ (crepLang$Return _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘ntmp’,‘nl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >> fs [] >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[Assign ntmp le; Return ntmp]’ mp_tac) >>
  strip_tac >> fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >>
  fs [set_var_def, lookup_insert, call_env_def] >>
  rveq >> fs [crepSemTheory.empty_locals_def, state_rel_def] >>
  cases_on ‘w’ >> fs [wlab_wloc_def] >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac globals_rel_intro >>
  imp_res_tac mem_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [FDOM_FLOOKUP] >> res_tac >> fs []
QED

Theorem compile_Raise:
  ^(get_goal "compile _ _ (crepLang$Raise _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, eval_def, set_var_def, lookup_insert,
      call_env_def, state_rel_def, crepSemTheory.empty_locals_def] >> rveq >>
  fs [] >>
  qexists_tac ‘0’ >>
  fs []
QED

Theorem compile_Store:
  ^(get_goal "compile _ _ (crepLang$Store _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ dst = (dp, dle,dtmp,dl)’ >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ src = (sp, sle, stmp, sl)’ >>
  qpat_x_assum ‘eval _ dst = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘dp’,‘dle’,‘dtmp’,‘dl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qpat_x_assum ‘eval _ src = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘st’, ‘ctxt’, ‘dtmp’, ‘dl’,
                           ‘sp’,‘sle’,‘stmp’,‘sl’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel >> fs []) >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck + ck'’ >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq dp, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ mp_tac) >>
  strip_tac >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign stmp sle; Store dle stmp]’ mp_tac) >>
  fs [] >>
  strip_tac >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def, set_var_def] >>
  fs [wlab_wloc_def] >>
  ‘eval (st' with locals := insert stmp (wlab_wloc ctxt.funcs w) st'.locals) dle =
   SOME (Word adr)’ by (
    qpat_x_assum ‘evaluate (nested_seq dp,_ with clock := ck + _) = _’ assume_tac >>
    drule nested_seq_pure_evaluation >>
    disch_then (qspecl_then [‘sp’, ‘st'’, ‘l’, ‘dtmp’, ‘dle’,
                             ‘Word adr’,‘ck'’] mp_tac) >> fs [] >>
    impl_tac
    >- (
     imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
     imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
     gen_tac >> strip_tac >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then [‘(ctxt.vmax + 1)’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                              ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘n’] mp_tac) >>
     fs [] >>
     impl_tac
     >- (
      rw [] >>
      imp_res_tac eval_some_var_cexp_local_lookup >>
      res_tac >> fs []) >>
     fs []) >>
    strip_tac >>
    pop_assum (assume_tac o GSYM) >>
    fs [] >>
    pop_assum kall_tac >>
    match_mp_tac locals_touched_eq_eval_eq >>
    fs [] >> rw [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >> rveq >>


    imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
    imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exp_le_tmp_domain >>
    disch_then (qspecl_then [‘(ctxt.vmax + 1)’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                             ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘n’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    imp_res_tac eval_some_var_cexp_local_lookup >>
    res_tac >> fs []) >>
  fs [] >> pop_assum kall_tac >>
  fs [mem_store_def, panSemTheory.mem_store_def] >>
  rveq >> fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l sl’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac mem_rel_intro >>
  rw [mem_rel_def] >>
  fs [APPLY_UPDATE_THM] >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs []) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac globals_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED


Theorem compile_StoreByte:
  ^(get_goal "compile _ _ (crepLang$StoreByte _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ dst = (dp, dle,dtmp,dl)’ >>
  qmatch_asmsub_rename_tac ‘compile_exp _ _ _ src = (sp, sle, stmp, sl)’ >>
  qpat_x_assum ‘eval _ dst = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘dp’,‘dle’,‘dtmp’,‘dl’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qpat_x_assum ‘eval _ src = _’ assume_tac >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘st’, ‘ctxt’, ‘dtmp’, ‘dl’,
                           ‘sp’,‘sle’,‘stmp’,‘sl’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   imp_res_tac compile_exp_out_rel >> fs []) >>
  strip_tac >> fs [] >>
  qexists_tac ‘ck + ck'’ >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq dp, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ mp_tac) >>
  strip_tac >>
  drule evaluate_comb_seq >>
  disch_then drule >>
  fs [evaluate_nested_seq_comb_seq] >>
  strip_tac >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign stmp dle; Assign (stmp + 1) sle;
                   StoreByte stmp (stmp + 1)]’ mp_tac) >>
  fs [] >>
  strip_tac >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def, set_var_def] >>
  fs [wlab_wloc_def] >>
  ‘eval st' dle = SOME (Word adr)’ by (
    qpat_x_assum ‘evaluate (nested_seq dp,_ with clock := ck + _) = _’ assume_tac >>
    drule nested_seq_pure_evaluation >>
    disch_then (qspecl_then [‘sp’, ‘st'’, ‘l’, ‘dtmp’, ‘dle’,
                             ‘Word adr’,‘ck'’] mp_tac) >> fs [] >>
    impl_tac
    >- (
     imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
     imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
     gen_tac >> strip_tac >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exp_le_tmp_domain >>
     disch_then (qspecl_then [‘ctxt.vmax + 1’, ‘l’, ‘dst’, ‘dp’, ‘dle’,
                              ‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘n’] mp_tac) >>
     fs [] >>
     impl_tac
     >- (
      rw [] >>
      imp_res_tac eval_some_var_cexp_local_lookup >>
      res_tac >> fs []) >>
     fs []) >>
    fs []) >>
  fs [] >> pop_assum kall_tac >>
  ‘eval (st' with locals := insert stmp (Word adr) st'.locals) sle =
   eval st' sle’ by (
    match_mp_tac locals_touched_eq_eval_eq >>
    fs [] >> rw [] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    imp_res_tac compile_exp_out_rel >> rveq >> fs [] >>
    imp_res_tac comp_exp_assigned_vars_tmp_bound >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exp_le_tmp_domain >>
    disch_then (qspecl_then [‘dtmp’, ‘cut_sets l (nested_seq dp)’, ‘src’,
                             ‘sp’, ‘sle’, ‘n’,
                             ‘cut_sets (cut_sets l (nested_seq dp)) (nested_seq sp)’,
                             ‘n’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    imp_res_tac eval_some_var_cexp_local_lookup >>
    res_tac >> fs [] >> rveq >> rfs []) >>
  fs [] >> pop_assum kall_tac >>
  fs [wordSemTheory.mem_store_byte_aux_def, panSemTheory.mem_store_byte_def,
      AllCaseEqs ()] >>
  rveq >> fs [lookup_insert] >>
  ‘st'.memory (byte_align adr) = Word v’ by (
    imp_res_tac mem_rel_intro >>
    last_x_assum (qspec_then ‘byte_align adr’ mp_tac) >>
    metis_tac [wlab_wloc_def]) >>
  fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l sl’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_insert_gt_vmax >>
   imp_res_tac compile_exp_out_rel >>
   fs [] >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac mem_rel_intro >>
  rw [mem_rel_def] >>
  fs [APPLY_UPDATE_THM] >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs [wlab_wloc_def]) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac globals_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem compile_StoreGlob:
  ^(get_goal "compile _ _ (crepLang$StoreGlob _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘tmp’,‘l'’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[SetGlobal dst le]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  fs [crepSemTheory.set_globals_def, set_globals_def] >>
  fs [state_rel_def] >>
  reverse conj_tac
  >- (
   ‘subspt l l'’ by (
     imp_res_tac compile_exp_out_rel >> fs [] >>
     imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
     rveq >> metis_tac [subspt_trans]) >>
   match_mp_tac locals_rel_cutset_prop >>
   metis_tac []) >>
  imp_res_tac globals_rel_intro >>
  rw [globals_rel_def, FLOOKUP_UPDATE]
  >- (TOP_CASE_TAC >> res_tac >> fs []) >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (res_tac >> fs []) >>
  imp_res_tac locals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac mem_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem compile_Assign:
  ^(get_goal "compile _ _ (crepLang$Assign _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  TOP_CASE_TAC >> fs []
  >- (imp_res_tac locals_rel_intro >> fs []) >>
  qmatch_goalsub_rename_tac ‘Assign n le’ >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’,‘le’,‘tmp’,‘l'’] mp_tac) >>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[Assign n le]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  fs [crepSemTheory.set_var_def, set_var_def] >>
  fs [state_rel_def] >>
  imp_res_tac compile_exp_out_rel >>
  rveq >>
  drule cut_sets_union_domain_subset >>
  strip_tac >>
  fs [locals_rel_def] >>
  rw []
  >- (
   match_mp_tac SUBSET_TRANS >>
   qexists_tac ‘domain (cut_sets l (nested_seq p))’ >> fs [] >>
   metis_tac [SUBSET_INSERT_RIGHT]) >>
  fs [FLOOKUP_UPDATE] >> reverse FULL_CASE_TAC >> rveq >> fs []
  >- (
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <> n'’ suffices_by fs [lookup_insert] >>
   CCONTR_TAC >>
   fs [distinct_vars_def] >>
   res_tac >> fs []) >>
  last_x_assum drule_all >>
  strip_tac >> rfs [] >> rveq >>
  rw [] >>
  imp_res_tac globals_rel_intro >>
  imp_res_tac code_rel_intro >>
  imp_res_tac mem_rel_intro >>
  drule eval_label_eq_state_contains_label >>
  rw [] >> res_tac >> fs []
QED

Theorem compile_Dec:
  ^(get_goal "compile _ _ (crepLang$Dec _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p’, ‘le’, ‘tmp’, ‘nl’] mp_tac) >>
  fs [] >>
  strip_tac >> fs [] >>
  last_x_assum (qspecl_then
                [‘st' with locals := insert tmp (wlab_wloc ctxt.funcs value) st'.locals’,
                 ‘ctxt with <|vars := ctxt.vars |+ (v,tmp); vmax := tmp|>’,
                 ‘insert tmp () l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   imp_res_tac compile_exp_out_rel >>
   conj_tac >- fs [code_rel_def] >>
   imp_res_tac locals_rel_intro >>
   rw [locals_rel_def]
   >- (
    fs [distinct_vars_def] >>
    rw [] >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs [] >>
    FULL_CASE_TAC >> fs [] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs [])
   >- (
    rw [ctxt_max_def] >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs [] >>
    fs [ctxt_max_def] >> res_tac >> rfs [])
   >- (
    drule cut_sets_union_domain_subset >>
    strip_tac >>
    metis_tac [SUBSET_TRANS, SUBSET_INSERT_RIGHT]) >>
   fs [FLOOKUP_UPDATE] >>
   TOP_CASE_TAC >> fs [] >> rveq
   >- (
    cases_on ‘v'’ >> fs [wlab_wloc_def] >>
    imp_res_tac globals_rel_intro >>
    imp_res_tac code_rel_intro >>
    imp_res_tac mem_rel_intro >>
    drule eval_label_eq_state_contains_label >>
    rw [] >> res_tac >> fs []) >>
   res_tac >> fs [] >> rveq >>
   fs [lookup_insert] >> TOP_CASE_TAC >> fs [] >> rveq
   >- (
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘evaluate (nested_seq p,_) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >> disch_then (qspec_then ‘ck'’ assume_tac) >>
  qexists_tac ‘ck + ck'’ >>
  fs [evaluate_def] >>
  fs [Once eval_upd_clock_eq] >>
  fs [set_var_def] >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac >- fs [code_rel_def] >>
  imp_res_tac compile_exp_out_rel_cases >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   imp_res_tac locals_rel_intro >>
   rw [locals_rel_def]
   >- fs [domain_insert] >>
  cases_on ‘vname = v’ >> rveq
   >- (
    cases_on ‘FLOOKUP s.locals v’ >>
    fs [crepSemTheory.res_var_def] >>
    fs [FLOOKUP_UPDATE] >> rveq >>
    qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME pv’ >>
    res_tac >> fs [] >> rveq >>
    qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.vars v = SOME pn’ >>
    qpat_x_assum ‘evaluate (compile _ _ _, _) = _’ assume_tac >>
    drule unassigned_vars_evaluate_same >>
    fs [] >>
    disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt.funcs pv’] mp_tac) >>
    impl_tac
    >- (
     conj_tac
     >- (
      ‘pn <> tmp’ suffices_by fs [lookup_insert] >>
      CCONTR_TAC >>
      fs [] >>
      imp_res_tac compile_exp_out_rel_cases >>
      fs [ctxt_max_def] >> res_tac >> fs []) >>
     conj_tac
     >- (
      match_mp_tac not_mem_context_assigned_mem_gt >>
      fs [] >>
      imp_res_tac compile_exp_out_rel_cases >>
      fs [ctxt_max_def] >> res_tac >> fs [] >>
      rw [FLOOKUP_UPDATE] >>
      CCONTR_TAC >>
      fs [distinct_vars_def] >>
      res_tac >> fs []) >>
     match_mp_tac member_cutset_survives_comp_prog >>
     fs [domain_insert]) >>
    fs []) >>
   cases_on ‘FLOOKUP s.locals v’ >>
   fs [crepSemTheory.res_var_def]
   >- (
    fs [DOMSUB_FLOOKUP_THM] >>
    last_x_assum drule >>
    strip_tac >> fs [] >> rveq
    >- (
     rfs [FLOOKUP_UPDATE] >> rveq >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
    rfs [FLOOKUP_UPDATE] >>
    cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
   qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME rv’ >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >> rveq
   >- (
    rfs [FLOOKUP_UPDATE] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   rfs [FLOOKUP_UPDATE] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  cases_on ‘x’ >> fs [] >> rveq >> (
  imp_res_tac locals_rel_intro >>
  rw [locals_rel_def]
  >- fs [domain_insert] >>
  cases_on ‘vname = v’ >> rveq
  >- (
   cases_on ‘FLOOKUP s.locals v’ >>
   fs [crepSemTheory.res_var_def] >>
   fs [FLOOKUP_UPDATE] >> rveq >>
   qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME pv’ >>
   res_tac >> fs [] >> rveq >>
   qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.vars v = SOME pn’ >>
   qpat_x_assum ‘evaluate (compile _ _ _, _) = _’ assume_tac >>
   drule unassigned_vars_evaluate_same >>
   fs [] >>
   disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt.funcs pv’] mp_tac) >>
   impl_tac
   >- (
    conj_tac
    >- (
     ‘pn <> tmp’ suffices_by fs [lookup_insert] >>
     CCONTR_TAC >>
     fs [] >>
     imp_res_tac compile_exp_out_rel_cases >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    conj_tac
    >- (
     match_mp_tac not_mem_context_assigned_mem_gt >>
     fs [] >>
     imp_res_tac compile_exp_out_rel_cases >>
     fs [ctxt_max_def] >> res_tac >> fs [] >>
     rw [FLOOKUP_UPDATE] >>
     CCONTR_TAC >>
     fs [distinct_vars_def] >>
     res_tac >> fs []) >>
    match_mp_tac member_cutset_survives_comp_prog >>
    fs [domain_insert]) >>
   fs []) >>
  cases_on ‘FLOOKUP s.locals v’ >>
  fs [crepSemTheory.res_var_def]
  >- (
   fs [DOMSUB_FLOOKUP_THM] >>
   last_x_assum drule >>
   strip_tac >> fs [] >> rveq
   >- (
    rfs [FLOOKUP_UPDATE] >> rveq >>
    fs [ctxt_max_def] >> res_tac >> rfs []) >>
   rfs [FLOOKUP_UPDATE] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  qmatch_asmsub_rename_tac ‘FLOOKUP s.locals v = SOME rv’ >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >> rveq
  >- (
   rfs [FLOOKUP_UPDATE] >> rveq >>
   fs [ctxt_max_def] >> res_tac >> rfs []) >>
  rfs [FLOOKUP_UPDATE] >>
  cases_on ‘v'’ >> fs [wlab_wloc_def])
QED

Theorem compile_If:
  ^(get_goal "compile _ _ (crepLang$If _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t’, ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘np’,‘le’,‘tmp’,‘nl’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [wlab_wloc_def] >>
  last_x_assum mp_tac >>
  disch_then (qspecl_then
              [‘st with locals := insert tmp (Word w) st.locals’,
               ‘ctxt’, ‘l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   imp_res_tac locals_rel_intro >>
   imp_res_tac compile_exp_out_rel >>
   rveq >>
   drule cut_sets_union_domain_subset >>
   strip_tac >>
   rw [locals_rel_def]
   >- (
    drule cut_sets_union_domain_subset >>
    strip_tac >>
    ‘domain l ⊆ domain st.locals’
    suffices_by fs [SUBSET_INSERT_RIGHT] >>
    match_mp_tac SUBSET_TRANS >>
    qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
    fs []) >>
   res_tac >> fs [] >> rveq >>
   ‘n <> tmp’ suffices_by fs [lookup_insert] >>
   CCONTR_TAC >> fs [] >> rveq >>
   fs [ctxt_max_def] >> res_tac >> rfs []) >>
  strip_tac >> fs [] >>
  cases_on ‘res’ >> fs [] >> rveq
  >- (
   qpat_x_assum ‘evaluate (compile _ _ _, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + 1’ assume_tac) >>
   qexists_tac ‘ck + ck' + 1’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘[Assign tmp le;
                 If NotEqual tmp (Imm 0w) (compile ctxt l c1)
                 (compile ctxt l c2) l]’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [nested_seq_def] >>
   fs [evaluate_def, eval_upd_clock_eq, set_var_def] >>
   fs [get_var_imm_def] >>
   cases_on ‘w <> 0w’ >>
   fs [asmTheory.word_cmp_def, cut_res_def, cut_state_def] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   TRY (imp_res_tac locals_rel_intro >> fs [] >> NO_TAC) >>
   fs [dec_clock_def] >> conj_tac >>
   TRY (fs [state_rel_def] >> NO_TAC) >>
   imp_res_tac locals_rel_intro >>
   imp_res_tac compile_exp_out_rel >>
   rveq >>
   drule cut_sets_union_domain_subset >>
   strip_tac >>
   rw [locals_rel_def] >>
   TRY (
   fs [domain_inter] >>
   match_mp_tac SUBSET_TRANS >>
   qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
   fs [] >> NO_TAC) >>
   res_tac >> rfs [] >>
   fs [lookup_inter, domain_lookup]) >>
  qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  qexists_tac ‘ck + ck'’ >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then
              ‘[Assign tmp le;
                If NotEqual tmp (Imm 0w) (compile ctxt l c1)
                 (compile ctxt l c2) l]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def] >>
  fs [evaluate_def, eval_upd_clock_eq, set_var_def] >>
  fs [get_var_imm_def] >>
  cases_on ‘x’ >> fs [] >> rveq >>
  cases_on ‘w <> 0w’ >>
  fs [asmTheory.word_cmp_def, cut_res_def]
QED


Theorem compile_FFI:
  ^(get_goal "compile _ _ (crepLang$ExtCall _ _ _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, AllCaseEqs ()] >> rveq >> fs [] >>
  imp_res_tac locals_rel_intro >>
  res_tac >> rfs [] >>
  fs [evaluate_def, wlab_wloc_def] >>
  fs [cut_state_def] >>
  ‘mem_load_byte_aux t.memory t.mdomain t.be =
   mem_load_byte s.memory s.memaddrs s.be’ by (
    match_mp_tac EQ_EXT >>
    rw [] >>
    fs [state_rel_def, panSemTheory.mem_load_byte_def,
        wordSemTheory.mem_load_byte_aux_def] >>
    fs [mem_rel_def] >>
    first_x_assum (qspec_then ‘byte_align x’ assume_tac) >>
    TOP_CASE_TAC >> fs [wlab_wloc_def] >>
    cases_on ‘s.memory (byte_align x)’ >>
    fs [wlab_wloc_def, AllCaseEqs ()]) >>
  fs [state_rel_def]
  >- (
   qexists_tac ‘0’ >> fs [] >>
   reverse conj_tac
   >- (
    fs [locals_rel_def] >>
    fs [domain_inter] >>
    rw [] >>
    res_tac >> fs [] >> rveq >>
    rfs [lookup_inter, domain_lookup]) >>
   match_mp_tac write_bytearray_mem_rel >>
   fs []) >>
  fs [call_env_def] >>
  qexists_tac ‘0’ >> fs []
QED


Theorem compile_While:
  ^(get_goal "compile _ _ (crepLang$While _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum ‘evaluate (While e c,s) = (res,s1)’ mp_tac >>
  once_rewrite_tac [crepSemTheory.evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  reverse TOP_CASE_TAC >> fs []
  >- (
   (* False case *)
   strip_tac >> fs [] >> rveq >>
   rw [compile_def] >>
   pairarg_tac >> fs [] >>
   drule comp_exp_preserves_eval >>
   disch_then (qspecl_then [‘t with locals := inter t.locals l’,
                            ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                            ‘np’,‘le’,‘tmp’,‘nl’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    conj_tac >- fs [state_rel_def] >>
    fs [locals_rel_def] >>
    fs [domain_inter] >>
    rw [] >>
    res_tac >> fs [] >>
    fs [lookup_inter, domain_lookup]) >>
   strip_tac >>
   fs [wlab_wloc_def] >>
   qexists_tac ‘ck + 2’ >>
   fs [Once evaluate_def] >>
   fs [cut_res_def, cut_state_def] >>
   ‘domain l ⊆ domain t.locals’ by (
     fs [locals_rel_def]) >>
   fs [dec_clock_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ pp)’ >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pp’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   (* to avoid looping *)
   ‘evaluate (Assign tmp le, st with clock := st.clock + 1) =
    (NONE, st with <|locals := insert tmp (Word 0w) st.locals;
                     clock := st.clock + 1|>)’ by (
     rw [evaluate_def, set_var_def, eval_upd_clock_eq]) >>
   fs [Abbr ‘pp’, nested_seq_def] >>
   rw [Once evaluate_def] >>
   pop_assum kall_tac >>
   rw [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   rw [Once evaluate_def] >>
   fs [Once evaluate_def]
   >- (
    fs [get_var_imm_def, asmTheory.word_cmp_def] >>
    fs [Once evaluate_def] >>
    fs [cut_res_def]) >>
   fs [get_var_imm_def] >>
   fs [asmTheory.word_cmp_def] >>
   fs [Once evaluate_def] >>
   fs [cut_res_def] >> rveq >>
   fs [] >>
   ‘domain l ⊆ tmp INSERT domain st.locals’ by (
     imp_res_tac compile_exp_out_rel >>
     rveq >>
     imp_res_tac locals_rel_intro >>
     drule cut_sets_union_domain_subset >>
     strip_tac >>
     match_mp_tac SUBSET_TRANS >>
     qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
     fs [] >>
     fs [SUBSET_INSERT_RIGHT]) >>
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   fs [domain_inter, domain_insert, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <> tmp’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     imp_res_tac compile_exp_out_rel >>
     rveq >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   fs [lookup_inter, lookup_insert, domain_lookup]) >>
  TOP_CASE_TAC >> fs [] >> rveq >> rfs []
  >- (
   (* Timeout case *)
   strip_tac >> rveq >> fs [] >>
   fs [Once compile_def] >>
   pairarg_tac >> fs [] >>
   ‘t.clock = 0’ by fs [state_rel_def] >>
   ‘domain l ⊆ domain t.locals’ by fs [locals_rel_def] >>
   qexists_tac ‘0’ >>
   fs [Once evaluate_def] >>
   fs [cut_res_def, cut_state_def] >>
   fs [state_rel_def, crepSemTheory.empty_locals_def]) >>
  pairarg_tac >> fs [] >>
  ‘t.clock <> 0’ by fs [state_rel_def] >>
  ‘domain l ⊆ domain t.locals’ by fs [locals_rel_def] >>
  ‘eval (dec_clock s) e = SOME (Word c')’ by (
    fs [crepSemTheory.dec_clock_def] >>
    fs [crepPropsTheory.eval_upd_clock_eq]) >>
  fs [compile_def] >>
  pairarg_tac >> fs [] >>
  drule comp_exp_preserves_eval >>
  disch_then (qspecl_then [‘t with <|locals := inter t.locals l; clock := t.clock - 1|>’,
                           ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘np’,‘le’,‘tmp’,‘nl’] mp_tac) >>
  fs [crepSemTheory.dec_clock_def] >>
  impl_tac
  >- (
   conj_tac >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   fs [domain_inter] >>
   rw [] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   fs [lookup_inter, domain_lookup]) >>
  strip_tac >> fs [] >>
  fs [wlab_wloc_def] >>
  rfs [] >>
  reverse TOP_CASE_TAC >> fs [] >> rveq
  (* first iteration non-NONE results *)
  >- (
   cases_on ‘x = Error’ >> fs [] >>
   last_x_assum (qspecl_then
                  [‘st with locals := insert tmp (Word c') st.locals’,
                   ‘ctxt’, ‘l’] mp_tac) >>
   impl_tac
   >- (
    fs [state_rel_def] >>
    imp_res_tac compile_exp_out_rel >>
    rveq >>
    fs [locals_rel_def] >>
    conj_tac
    >- (
     drule cut_sets_union_domain_subset >>
     strip_tac >>
     match_mp_tac SUBSET_TRANS >>
     qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
     fs [] >>
     fs [SUBSET_INSERT_RIGHT]) >>
    rw [] >> res_tac >> fs [] >>
    rveq >> fs [] >>
    ‘n <> tmp’ by (
      CCONTR_TAC >> fs [] >> rveq >>
      imp_res_tac compile_exp_out_rel >>
      rveq >>
      fs [ctxt_max_def] >> res_tac >> rfs []) >>
    fs [lookup_insert, domain_lookup]) >>
   strip_tac >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   strip_tac >> rveq >> fs [] >>
   TRY (
   rename [‘evaluate _ = (SOME Break,_)’] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ pp)’ >>
   qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + 1’ assume_tac) >>
   qpat_x_assum ‘evaluate _ = (SOME Break,t1)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   disch_then (qspec_then ‘1’ assume_tac) >>
   qexists_tac ‘ck + ck' + 1’ >>
   simp [Once evaluate_def] >>
   fs [cut_res_def, cut_state_def, dec_clock_def] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pp’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   ‘evaluate (Assign tmp le, st with clock := ck' + 1 + st.clock) =
    (NONE, st with <|locals := insert tmp (Word c') st.locals;
              clock := ck' + 1 + st.clock|>)’ by (
     rw [evaluate_def, set_var_def, eval_upd_clock_eq]) >>
   fs [Abbr ‘pp’, nested_seq_def] >>
   simp [Once evaluate_def] >>
   pop_assum kall_tac >>
   simp [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [get_var_imm_def] >>
   rfs [asmTheory.word_cmp_def] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [] >>
   strip_tac >> fs [] >>
   strip_tac >> fs [] >>
   rveq >> fs [cut_res_def] >>
   rveq >> fs [] >>
   ‘domain l ⊆ domain t1.locals’ by
     fs [locals_rel_def] >>
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   fs [domain_inter, domain_insert, SUBSET_INSERT_RIGHT] >>
   rw [] >>
   res_tac >> fs [] >> rveq >> fs [] >>
   ‘n <> tmp’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     imp_res_tac compile_exp_out_rel >>
     rveq >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   fs [lookup_inter, lookup_insert, domain_lookup]) >>
   TRY (
   rename [‘evaluate _ = (SOME Continue,_)’] >>
   (* instantiating IH *)
   first_x_assum (qspecl_then [‘t1’, ‘ctxt’ , ‘l’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >> fs [] >>
   fs [Once compile_def] >>
   pairarg_tac >> fs [] >>
   rveq >> rfs [] >>
   qpat_x_assum ‘evaluate _ = (SOME Continue,t1)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck''’ assume_tac) >>
   cases_on ‘res’ >> fs [] >> rveq >>
   TRY ( cases_on ‘x’ >> fs [] >> rveq) >>
   qexists_tac ‘ck + ck' + ck''’ >>
   simp [Once evaluate_def] >>
   fs [cut_res_def, cut_state_def] >>
   fs [dec_clock_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ pp)’ >>
   qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + ck''’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pp’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   ‘evaluate (Assign tmp le, st with clock := ck' + (ck'' + st.clock)) =
    (NONE, st with <|locals := insert tmp (Word c') st.locals;
              clock := ck' + (ck'' + st.clock)|>)’ by (
     rw [evaluate_def, set_var_def, eval_upd_clock_eq]) >>
   fs [Abbr ‘pp’, nested_seq_def] >>
   simp [Once evaluate_def] >>
   pop_assum kall_tac >>
   simp [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [get_var_imm_def] >>
   rfs [asmTheory.word_cmp_def] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [] >>
   strip_tac >> fs [] >>
   strip_tac >> fs [] >>
   rveq >> fs [cut_res_def] >>
   rveq >> fs []) >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ pp)’ >>
   qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'’ assume_tac) >>
   qexists_tac ‘ck + ck'’ >>
   simp [Once evaluate_def] >>
   fs [cut_res_def, cut_state_def, dec_clock_def] >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pp’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   ‘evaluate (Assign tmp le, st with clock := ck' + st.clock) =
    (NONE, st with <|locals := insert tmp (Word c') st.locals;
              clock := ck' + st.clock|>)’ by (
     rw [evaluate_def, set_var_def, eval_upd_clock_eq]) >>
   fs [Abbr ‘pp’, nested_seq_def] >>
   simp [Once evaluate_def] >>
   pop_assum kall_tac >>
   simp [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [get_var_imm_def] >>
   rfs [asmTheory.word_cmp_def] >>
   pop_assum mp_tac >>
   simp [Once evaluate_def] >>
   fs [] >>
   strip_tac >> fs [] >>
   strip_tac >> fs [] >>
   rveq >> fs [cut_res_def] >>
   rveq >> fs []) >>
  strip_tac >>
  fs [] >> rfs [] >>
  last_x_assum (qspecl_then
                [‘st with locals := insert tmp (Word c') st.locals’,
                 ‘ctxt’, ‘l’] mp_tac) >>
  impl_tac
  >- (
   fs [state_rel_def] >>
   imp_res_tac compile_exp_out_rel >>
   rveq >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    drule cut_sets_union_domain_subset >>
    strip_tac >>
    match_mp_tac SUBSET_TRANS >>
    qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
    fs [] >>
    fs [SUBSET_INSERT_RIGHT]) >>
   rw [] >> res_tac >> fs [] >>
   rveq >> fs [] >>
   ‘n <> tmp’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     imp_res_tac compile_exp_out_rel >>
     rveq >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   fs [lookup_insert, domain_lookup]) >>
  strip_tac >> fs [] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qpat_x_assum ‘evaluate _ = (NONE,t1)’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck''’ assume_tac) >>

  qexists_tac ‘ck + ck' + ck''’ >>
  simp [Once evaluate_def] >>
  fs [cut_res_def, cut_state_def] >>
  fs [dec_clock_def] >>
  qmatch_goalsub_abbrev_tac ‘nested_seq (_ ++ pp)’ >>
  qpat_x_assum ‘evaluate (nested_seq np, _) = _’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck' + ck''’ assume_tac) >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘pp’ assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  ‘evaluate (Assign tmp le, st with clock := ck' + (ck'' + st.clock)) =
   (NONE, st with <|locals := insert tmp (Word c') st.locals;
             clock := ck' + (ck'' + st.clock)|>)’ by (
    rw [evaluate_def, set_var_def, eval_upd_clock_eq]) >>
  fs [Abbr ‘pp’, nested_seq_def] >>
  simp [Once evaluate_def] >>
  pop_assum kall_tac >>
  simp [Once evaluate_def] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  simp [Once evaluate_def] >>
  fs [get_var_imm_def] >>
  rfs [asmTheory.word_cmp_def] >>
  simp [Once evaluate_def] >>
  simp [Once evaluate_def] >>
  fs [cut_res_def] >>
  strip_tac >> fs [] >> rveq >>
  fs []
QED


Theorem call_preserve_state_code_locals_rel:
  !ns lns args s st ctxt nl fname argexps prog loc.
   ALL_DISTINCT ns /\ ALL_DISTINCT lns /\
   LENGTH ns = LENGTH lns /\
   LENGTH args = LENGTH lns /\
   state_rel s st /\
   mem_rel ctxt.funcs s.memory st.memory /\
   globals_rel ctxt.funcs s.globals st.globals /\
   code_rel ctxt s.code st.code /\
   locals_rel ctxt nl s.locals st.locals /\
   FLOOKUP s.code fname = SOME (ns,prog) /\
   FLOOKUP ctxt.funcs fname = SOME (loc,LENGTH lns) /\
   MAP (eval s) argexps = MAP SOME args ==>
   let nctxt = ctxt_fc ctxt.funcs ns lns in
        state_rel
          (s with
           <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock − 1|>)
          (st with
           <|locals :=
               fromAList
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])));
             clock := st.clock − 1|>) ∧
        code_rel nctxt s.code st.code ∧
        locals_rel nctxt (list_to_num_set lns)
          (FEMPTY |++ ZIP (ns,args))
          (fromAList
             (ZIP (lns,FRONT (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0]))))
Proof
  rw [] >>
  fs [ctxt_fc_def]
  >- fs [state_rel_def]
  >- fs [code_rel_def] >>
  fs [locals_rel_def] >>
  conj_tac
  >- (
   fs [distinct_vars_def] >>
   rw [] >>
   qpat_x_assum ‘LENGTH ns = LENGTH lns’ assume_tac >>
   drule fm_empty_zip_flookup >>
   fs [] >>
   disch_then (qspecl_then [‘x’ ,‘m’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   drule fm_empty_zip_flookup >>
   fs [] >>
   disch_then (qspecl_then [‘y’ ,‘m’] mp_tac) >>
   fs [] >> strip_tac >> fs [] >>
   ‘EL n (ZIP (ns,lns)) = (EL n ns,EL n lns)’ by metis_tac [EL_ZIP] >>
   ‘EL n' (ZIP (ns,lns)) = (EL n' ns,EL n' lns)’ by metis_tac [EL_ZIP] >>
   fs [] >> rveq >> metis_tac [ALL_DISTINCT_EL_IMP]) >>
  conj_tac
  >- (
   fs [ctxt_max_def] >>
   rw [] >>
   ‘MEM m lns’ by (
     qpat_x_assum ‘LENGTH ns = LENGTH lns’ assume_tac >>
     drule fm_empty_zip_flookup >>
     fs [] >>
     disch_then (qspecl_then [‘v’ ,‘m’] mp_tac) >>
     fs [] >>
     strip_tac >> fs [] >>
     fs [MEM_EL] >>
     qexists_tac ‘n’ >> fs [] >>
     drule EL_ZIP >>
     disch_then (qspec_then ‘n’ mp_tac) >> fs []) >>
   assume_tac list_max_max >>
   pop_assum (qspec_then ‘lns’ assume_tac) >>
   fs [EVERY_MEM]) >>
  ‘FRONT (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0]) =
   MAP (wlab_wloc ctxt.funcs) args’ by (
    cases_on ‘[Loc loc 0]’ >- fs [] >>
    rewrite_tac  [FRONT_APPEND, FRONT_DEF] >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  conj_tac
  >- (
   fs [domain_fromAList] >>
   ‘LENGTH lns = LENGTH (MAP (wlab_wloc ctxt.funcs) args)’ by
     fs [LENGTH_MAP] >>
   drule MAP_ZIP >>
   fs [GSYM PULL_FORALL] >>
   strip_tac >> fs [] >>
   fs [SUBSET_DEF] >> rw [] >>
   fs [domain_list_to_num_set]) >>
  rw [] >>
  ‘LENGTH ns = LENGTH args’ by fs [] >>
  drule fm_empty_zip_flookup >>
  disch_then (qspecl_then [‘vname’, ‘v’] mp_tac) >>
  fs [] >>
  drule EL_ZIP >>
  strip_tac >>
  strip_tac >> fs [] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  strip_tac >> rveq >> fs [] >>
  qexists_tac ‘EL n lns’ >>
  conj_tac
  >- (
   match_mp_tac update_eq_zip_flookup >>
   fs [])>>
  conj_tac
  >- (
   fs [domain_list_to_num_set] >>
   metis_tac [EL_MEM]) >>
  ‘lookup (EL n lns) (fromAList (ZIP (lns,MAP (wlab_wloc ctxt.funcs) args))) =
   SOME (EL n (MAP (wlab_wloc ctxt.funcs) args))’ by (
    fs [lookup_fromAList] >>
    ‘n < LENGTH (ZIP (lns,MAP (wlab_wloc ctxt.funcs) args))’ by
      fs [LENGTH_MAP, LENGTH_ZIP] >>
    drule ALOOKUP_ALL_DISTINCT_EL >>
    impl_tac
    >- metis_tac [MAP_ZIP, LENGTH_MAP] >>
    strip_tac >>
    metis_tac [EL_ZIP, FST, SND, LENGTH_MAP]) >>
  fs [] >> pop_assum kall_tac >>
  ‘n < LENGTH args’ by fs [] >>
  drule (INST_TYPE [``:'a``|->``:'a word_lab``,
                    ``:'b``|->``:'a word_loc``] EL_MAP) >>
  disch_then (qspec_then ‘wlab_wloc ctxt.funcs’ assume_tac) >>
  fs [] >>
  cases_on ‘EL n args’ >>
  fs [wlab_wloc_def] >>
  reverse FULL_CASE_TAC >> fs [] >> rveq
  >- (cases_on ‘x’ >> fs []) >>
  ‘eval s (EL n argexps) = SOME (Label m)’ by (
    ‘n < LENGTH argexps’ by metis_tac [LENGTH_MAP] >>
    metis_tac [EL_MAP]) >>
  drule eval_label_eq_state_contains_label >>
  disch_then (qspec_then ‘m’ assume_tac) >>
  fs []
  >- (
   imp_res_tac locals_rel_intro >>
   res_tac >> rfs [])
  >- (
   qpat_x_assum ‘code_rel ctxt s.code t.code’ assume_tac >>
   drule code_rel_intro >>
   strip_tac >> fs [] >>
   res_tac >> rfs [])
  >- (
   qpat_x_assum ‘mem_rel ctxt.funcs s.memory t.memory’ assume_tac >>
   drule mem_rel_intro >>
   strip_tac >> fs [] >>
   res_tac >> rfs []) >>
  qpat_x_assum ‘globals_rel ctxt.funcs s.globals st.globals’ assume_tac >>
  drule globals_rel_intro >>
  strip_tac >> fs [] >>
  res_tac >> rfs []
QED

val tail_case_tac =
   fs [crepSemTheory.evaluate_def,
       CaseEq "option", CaseEq "word_lab",CaseEq "prod" ] >>
   rveq >> fs [] >>
   fs [compile_def] >>
   pairarg_tac >> fs [] >>
   ‘OPT_MMAP (eval s) (argexps ++ [trgt]) =
    SOME (args ++ [Label fname])’ by fs [opt_mmap_eq_some] >>
   drule comp_exps_preserves_eval >>
   disch_then (qspecl_then [‘t’,
                            ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                            ‘p’,‘les’,‘tmp’,‘nl’] mp_tac) >>
   fs [] >>
   strip_tac >>
   fs [opt_mmap_eq_some] >>
   (* Keep progressing in crep's Call to estimate clock *)
   fs [lookup_code_def, CaseEq "option", CaseEq "prod"] >>
   rveq >> fs [] >>
   cases_on ‘evaluate
             (prog,dec_clock s with locals := FEMPTY |++ ZIP (ns,args))’ >>
   fs [] >>
   reverse (cases_on ‘s.clock = 0’) >> fs [] >> rveq >> fs []
   >- (
    ‘q ≠ SOME Error’ by fs [AllCaseEqs()] >>
    fs [] >>
    drule code_rel_intro >>
    strip_tac >>
    pop_assum mp_tac >>
    disch_then (qspecl_then [‘fname’, ‘ns’, ‘prog’] mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘lookup _ st.code = SOME (lns,_)’ >>
    ‘ALL_DISTINCT lns’ by fs [Abbr ‘lns’, ALL_DISTINCT_GENLIST] >>
    last_x_assum
    (qspecl_then [
     ‘dec_clock (st with locals := fromAList
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0]))))’,
     ‘(ctxt_fc ctxt.funcs ns lns)’, ‘list_to_num_set lns’] mp_tac) >>
    impl_tac
    >- (
    fs [crepSemTheory.dec_clock_def, dec_clock_def] >>
    ‘(ctxt_fc ctxt.funcs ns lns).funcs = ctxt.funcs’ by (
      fs [ctxt_fc_def]) >> fs [] >>
     match_mp_tac (call_preserve_state_code_locals_rel |> SIMP_RULE bool_ss [LET_THM]) >>
     fs [Abbr ‘lns’] >>
     metis_tac []) >>
    fs [Abbr ‘lns’] >>
    strip_tac >> fs [dec_clock_def] >>
    qexists_tac ‘ck + ck'’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then
                ‘MAP2 Assign (gen_temps tmp (LENGTH les)) les ++
                 [Call NONE NONE (gen_temps tmp (LENGTH les)) NONE]’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les = MAP (eval (st with clock := ck' + st.clock)) les’ by (
      ho_match_mp_tac MAP_CONG >>
      fs [] >> rw [] >>
      fs[eval_upd_clock_eq]) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval (st with clock := ck' + st.clock)) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
    drule loop_eval_nested_assign_distinct_eq >>
    disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
    impl_tac
    >- (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     rewrite_tac [distinct_lists_def] >>
     fs [EVERY_GENLIST] >>
     rw [] >>
     CCONTR_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exps_le_tmp_domain >>
     disch_then drule >>
     disch_then (qspec_then ‘tmp + x’ assume_tac) >>
     rfs [] >>
     fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
     >- (
      ‘?v. eval s y' = SOME v’ by (
        qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
        fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
    strip_tac >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘[Call NONE NONE (gen_temps tmp (LENGTH les)) NONE]’
                assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    fs [nested_seq_def] >>
    rewrite_tac [evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    fs [get_vars_local_clock_upd_eq] >>
    ‘get_vars (gen_temps tmp (LENGTH les))
     (st with locals :=
      alist_insert (gen_temps tmp (LENGTH les))
      (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    fs [] >> pop_assum kall_tac >>
    fs [find_code_def] >>
    pop_assum mp_tac >>
    rewrite_tac [wlab_wloc_def] >>
    rfs [] >>
    ‘st.clock <> 0’ by fs [state_rel_def] >>
    fs [] >>
    fs [dec_clock_def] >>
    strip_tac >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >>
    fs [] >> rveq >> fs [] >>
    TRY (
    fs [ocompile_def] >>
    qpat_x_assum ‘evaluate (compile _ _ _, _) = _’ assume_tac >>
    drule loop_liveProofTheory.optimise_correct >>
    fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    fs [state_rel_def, code_rel_def])) >>
   drule code_rel_intro >>
   strip_tac >>
   pop_assum mp_tac >>
   disch_then (qspecl_then [‘fname’, ‘ns’, ‘prog’] mp_tac) >>
   fs [] >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘lookup _ st.code = SOME (lns,_)’ >>
   ‘ALL_DISTINCT lns’ by fs [Abbr ‘lns’, ALL_DISTINCT_GENLIST] >>
   fs [Abbr ‘lns’] >>
   qexists_tac ‘ck’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then
               ‘MAP2 Assign (gen_temps tmp (LENGTH les)) les ++
                [Call NONE NONE (gen_temps tmp (LENGTH les)) NONE]’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   ‘MAP (eval st) les =
    MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
   drule loop_eval_nested_assign_distinct_eq >>
   disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
   impl_tac
   >- (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    rewrite_tac [distinct_lists_def] >>
    fs [EVERY_GENLIST] >>
    rw [] >>
    CCONTR_TAC >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exps_le_tmp_domain >>
    disch_then drule >>
    disch_then (qspec_then ‘tmp + x’ assume_tac) >>
    rfs [] >>
    fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
    >- (
     ‘?v. eval s y' = SOME v’ by (
       qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
   strip_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘[Call NONE NONE (gen_temps tmp (LENGTH les)) NONE]’
               assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [nested_seq_def] >>
   rewrite_tac [evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   ‘get_vars (gen_temps tmp (LENGTH les))
     (st with locals :=
      alist_insert (gen_temps tmp (LENGTH les))
      (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
   fs [] >> pop_assum kall_tac >>
   fs [find_code_def] >>
   pop_assum mp_tac >>
   rewrite_tac [wlab_wloc_def] >>
   rfs [] >>
   ‘st.clock = 0’ by fs [state_rel_def] >>
   fs [] >> strip_tac >> rveq >> fs [] >>
   fs [crepSemTheory.empty_locals_def] >>
   fs [state_rel_def];

val timed_out_before_call_tac =
   drule code_rel_intro >>
   strip_tac >>
   pop_assum mp_tac >>
   disch_then (qspecl_then [‘fname’, ‘ns’, ‘prog’] mp_tac) >>
   fs [] >>
   strip_tac >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘lookup _ st.code = SOME (lns,_)’ >>
   ‘ALL_DISTINCT lns’ by fs [Abbr ‘lns’, ALL_DISTINCT_GENLIST] >>
   qmatch_goalsub_abbrev_tac ‘nested_seq (p' ++ ptmp ++ pcal)’ >>
   qexists_tac ‘ck’ >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   ‘MAP (eval st) les =
    MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
   drule loop_eval_nested_assign_distinct_eq >>
   disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
   fs [Abbr ‘lns’] >>
   impl_tac
   >- (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    rewrite_tac [distinct_lists_def] >>
    fs [EVERY_GENLIST] >>
    rw [] >>
    CCONTR_TAC >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exps_le_tmp_domain >>
    disch_then drule >>
    disch_then (qspec_then ‘tmp + x’ assume_tac) >>
    rfs [] >>
    fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
    >- (
     ‘?v. eval s y' = SOME v’ by (
       qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
   strip_tac >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pcal’ assume_tac) >>
   fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
   fs [Abbr ‘pcal’, nested_seq_def] >>
   rewrite_tac [evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   ‘get_vars (gen_temps tmp (LENGTH les))
     (st with locals :=
      alist_insert (gen_temps tmp (LENGTH les))
      (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
   fs [] >> pop_assum kall_tac >>
   fs [find_code_def] >>
   pop_assum mp_tac >>
   rewrite_tac [wlab_wloc_def] >>
   rfs [] >>
   fs [cut_res_def, cut_state_def] >>
   ‘LENGTH ((gen_temps tmp (LENGTH les))) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule domain_alist_insert >>
   disch_then (qspec_then ‘st.locals’ mp_tac) >>
   strip_tac >>  fs [] >>
   ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
     qsuff_tac ‘domain l ⊆ domain st.locals’
     >- fs [SUBSET_DEF] >>
     imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
     imp_res_tac locals_rel_intro >>
     imp_res_tac cut_sets_union_domain_subset >>
     fs [SUBSET_DEF]) >>
   ‘st.clock = 0’ by fs [state_rel_def] >>
   fs [] >> strip_tac >> rveq >> fs [] >>
   fs [crepSemTheory.empty_locals_def] >>
   fs [state_rel_def];


val fcalled_timed_out_tac =
   (* Timeout case of the called function *)
   fs [Abbr ‘lns’] >>
   qexists_tac ‘ck + ck'’ >>
   qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   ‘MAP (eval st) les =
    MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
   drule loop_eval_nested_assign_distinct_eq >>
   disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
   impl_tac
   >- (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    rewrite_tac [distinct_lists_def] >>
    fs [EVERY_GENLIST] >>
    rw [] >>
    CCONTR_TAC >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exps_le_tmp_domain >>
    disch_then drule >>
    disch_then (qspec_then ‘tmp + x’ assume_tac) >>
    rfs [] >>
    fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
    >- (
     ‘?v. eval s y' = SOME v’ by (
       qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
   strip_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pcal’ assume_tac) >>
   fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
   fs [Abbr ‘pcal’, nested_seq_def] >>
   rewrite_tac [evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   fs [get_vars_local_clock_upd_eq] >>
   ‘get_vars (gen_temps tmp (LENGTH les))
     (st with locals :=
      alist_insert (gen_temps tmp (LENGTH les))
      (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
   fs [] >> pop_assum kall_tac >>
   fs [find_code_def] >>
   pop_assum mp_tac >>
   rewrite_tac [wlab_wloc_def] >>
   rfs [] >>
   fs [cut_res_def, cut_state_def] >>
   ‘LENGTH ((gen_temps tmp (LENGTH les))) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule domain_alist_insert >>
   disch_then (qspec_then ‘st.locals’ mp_tac) >>
   strip_tac >>  fs [] >>
   ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
     qsuff_tac ‘domain l ⊆ domain st.locals’
     >- fs [SUBSET_DEF] >>
     imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
     imp_res_tac locals_rel_intro >>
     imp_res_tac cut_sets_union_domain_subset >>
     fs [SUBSET_DEF]) >>
   fs [] >>
   ‘st.clock <> 0’ by fs [state_rel_def] >>
   fs [dec_clock_def] >>
   strip_tac >> rveq >> fs [] >>
   fs [ocompile_def] >>
   qpat_x_assum ‘evaluate (compile _ _ _, _) = _’ assume_tac >>
   drule loop_liveProofTheory.optimise_correct >>
   fs [] >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   fs [crepSemTheory.empty_locals_def] >>
   fs [state_rel_def] >>
   conj_tac
   >- (
    qpat_x_assum ‘mem_rel _ r.memory s1.memory’ assume_tac >>
    fs [mem_rel_def, ctxt_fc_def] >>
    rw [] >>
    cases_on ‘s1.memory ad’ >> fs [] >>
    cases_on ‘r.memory ad’ >> fs [] >>
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    rfs [wlab_wloc_def]) >>
   conj_tac
   >- (
    qpat_x_assum ‘globals_rel _ r.globals s1.globals’ assume_tac >>
    fs [globals_rel_def, ctxt_fc_def] >>
    rw [] >>
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    TRY (cases_on ‘v’) >>
    rfs [wlab_wloc_def]) >>
   fs [code_rel_def, ctxt_fc_def];


val fcalled_ffi_case_tac =
(* FFI case of the called function *)
  fs [Abbr ‘lns’] >>
  qexists_tac ‘ck + ck'’ >>
  qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  ‘MAP (eval st) les =
   MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
  drule loop_eval_nested_assign_distinct_eq >>
  disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
  impl_tac
  >- (
   fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
   rewrite_tac [distinct_lists_def] >>
   fs [EVERY_GENLIST] >>
   rw [] >>
   CCONTR_TAC >> fs [] >>
   imp_res_tac locals_rel_intro >>
   drule compile_exps_le_tmp_domain >>
   disch_then drule >>
   disch_then (qspec_then ‘tmp + x’ assume_tac) >>
   rfs [] >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
   >- (
    ‘?v. eval s y' = SOME v’ by (
      qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
   drule_all eval_some_var_cexp_local_lookup >>
   strip_tac >> res_tac >> rfs [] >> rveq >> fs []) >>
  strip_tac >>
  drule evaluate_add_clock_eq >>
  fs [] >>
  disch_then (qspec_then ‘ck'’ assume_tac) >>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘pcal’ assume_tac) >>
  fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
  fs [Abbr ‘pcal’, nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  fs [get_vars_local_clock_upd_eq] >>
  ‘get_vars (gen_temps tmp (LENGTH les))
   (st with locals :=
    alist_insert (gen_temps tmp (LENGTH les))
    (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
   SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
    ho_match_mp_tac get_vars_local_update_some_eq >>
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    imp_res_tac compile_exps_out_rel >> fs [] >>
    metis_tac [LENGTH_MAP]) >>
  fs [] >> pop_assum kall_tac >>
  fs [find_code_def] >>
  pop_assum mp_tac >>
  rewrite_tac [wlab_wloc_def] >>
  rfs [] >>
  fs [cut_res_def, cut_state_def] >>
  ‘LENGTH ((gen_temps tmp (LENGTH les))) =
   LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    imp_res_tac compile_exps_out_rel >> fs [] >>
    metis_tac [LENGTH_MAP]) >>
  drule domain_alist_insert >>
  disch_then (qspec_then ‘st.locals’ mp_tac) >>
  strip_tac >>  fs [] >>
  ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
    qsuff_tac ‘domain l ⊆ domain st.locals’
    >- fs [SUBSET_DEF] >>
    imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
    imp_res_tac locals_rel_intro >>
    imp_res_tac cut_sets_union_domain_subset >>
    fs [SUBSET_DEF]) >>
  fs [] >>
  ‘st.clock <> 0’ by fs [state_rel_def] >>
  fs [dec_clock_def] >>
  strip_tac >> rveq >> fs [] >>
  fs [crepSemTheory.empty_locals_def] >>
  fs [state_rel_def] >>
  conj_tac
  >- (
   qpat_x_assum ‘mem_rel _ r.memory s1.memory’ assume_tac >>
   fs [mem_rel_def, ctxt_fc_def] >>
   rw [] >>
   cases_on ‘s1.memory ad’ >> fs [] >>
   cases_on ‘r.memory ad’ >> fs [] >>
   first_x_assum (qspec_then ‘ad’ assume_tac) >>
   rfs [wlab_wloc_def]) >>
  conj_tac
  >- (
   qpat_x_assum ‘globals_rel _ r.globals s1.globals’ assume_tac >>
   fs [globals_rel_def, ctxt_fc_def] >>
   rw [] >>
   first_x_assum (qspec_then ‘ad’ assume_tac) >>
   TRY (cases_on ‘v’) >>
   rfs [wlab_wloc_def]) >>
  fs [code_rel_def, ctxt_fc_def];


Theorem compile_Call:
  ^(get_goal "compile _ _ (crepLang$Call _ _ _)")
Proof
  rw [] >>
  cases_on ‘caltyp’ >> fs []
  (* Tail case *)
  >- tail_case_tac >>
  (* Return case *)
  fs [crepSemTheory.evaluate_def,
      CaseEq "option", CaseEq "word_lab",CaseEq "prod"] >>
  rveq >> fs [] >>
  fs [compile_def] >>
  pairarg_tac >> fs [] >>
  ‘OPT_MMAP (eval s) (argexps ++ [trgt]) =
   SOME (args ++ [Label fname])’ by fs [opt_mmap_eq_some] >>
  drule comp_exps_preserves_eval >>
  disch_then (qspecl_then [‘t’,
                           ‘ctxt’, ‘ctxt.vmax + 1’, ‘l’,
                           ‘p'’,‘les’,‘tmp’,‘nl’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [opt_mmap_eq_some] >>
  (* Keep progressing in crep's Call to estimate clock *)
  fs [lookup_code_def, CaseEq "option", CaseEq "prod"] >>
  rveq >> fs [] >>
  cases_on ‘evaluate
            (prog,dec_clock s with locals := FEMPTY |++ ZIP (ns,args))’ >>
  fs [] >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq >> fs []
  (* time-out before the function call *)
  >- timed_out_before_call_tac >>
  ‘q ≠ SOME Error’ by fs [AllCaseEqs()] >>
  fs [] >>
  drule code_rel_intro >>
  strip_tac >>
  pop_assum mp_tac >>
  disch_then (qspecl_then [‘fname’, ‘ns’, ‘prog’] mp_tac) >>
  fs [] >>
  strip_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘lookup _ st.code = SOME (lns,_)’ >>
  qmatch_goalsub_abbrev_tac ‘nested_seq (p' ++ ptmp ++ pcal)’ >>
  ‘ALL_DISTINCT lns’ by fs [Abbr ‘lns’, ALL_DISTINCT_GENLIST] >>
  first_x_assum
  (qspecl_then [
     ‘dec_clock (st with locals := fromAList
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0]))))’,
     ‘(ctxt_fc ctxt.funcs ns lns)’, ‘list_to_num_set lns’] mp_tac) >>
  impl_tac
  >- (
   fs [crepSemTheory.dec_clock_def, dec_clock_def] >>
   ‘(ctxt_fc ctxt.funcs ns lns).funcs = ctxt.funcs’ by (
     fs [ctxt_fc_def]) >> fs [] >>
   match_mp_tac (call_preserve_state_code_locals_rel |> SIMP_RULE bool_ss [LET_THM]) >>
   fs [Abbr ‘lns’] >>
   metis_tac []) >>
  strip_tac >> fs [dec_clock_def] >>
  cases_on ‘q’ >> fs [] >> rveq >>
  cases_on ‘x’ >> fs [] >> rveq
  (* time-out in the called function *)
  >- fcalled_timed_out_tac
  (* return from called function *)
  >- (
   (* case split on return option variable *)
   fs [CaseEq "option"] >> rveq >>
   fs [rt_var_def] >>
   ‘(ctxt_fc ctxt.funcs ns lns).funcs = ctxt.funcs’ by (
     fs [ctxt_fc_def]) >>
   fs [] >> pop_assum kall_tac >>
   TRY (
   fs [rt_var_def] >>
   ‘IS_SOME (FLOOKUP ctxt.vars rt)’ by (
     imp_res_tac locals_rel_intro >>
     res_tac >> rfs [IS_SOME_DEF]) >>
   cases_on ‘FLOOKUP ctxt.vars rt’ >>
   fs [IS_SOME_DEF]) >>
   qmatch_asmsub_abbrev_tac ‘Call (SOME (rn,_))’ >>
   last_x_assum (qspecl_then
                 [‘t1 with locals :=
                   insert rn
                   (wlab_wloc ctxt.funcs w)
                   (inter (alist_insert (gen_temps tmp (LENGTH les))
                           (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])
                           st.locals) l)’,
                  ‘ctxt’, ‘l’] mp_tac) >>
   impl_tac >>
   TRY (
   fs [Abbr ‘lns’] >>
   fs [crepSemTheory.set_var_def, ctxt_fc_def] >>
   conj_tac >- fs [state_rel_def] >>
   conj_tac
   >- (
    FULL_CASE_TAC >> fs [] >> rveq >> fs [] >>
    fs [code_rel_def]) >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [domain_inter] >>
    ‘LENGTH (gen_temps tmp (LENGTH les)) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ assume_tac) >>
    fs [] >>
    qsuff_tac
    ‘(domain st.locals ∪ set (gen_temps tmp (LENGTH les))) ∩ domain l = domain l’
    >- fs [SUBSET_INSERT_RIGHT] >>
    fs [INTER_SUBSET_EQN |> CONJUNCT2] >>
    imp_res_tac compile_exps_out_rel >> fs [] >> rveq >> fs [] >>
    imp_res_tac cut_sets_union_domain_subset >>
    fs [SUBSET_DEF]) >>
   TRY (
   rename [‘rn = ctxt.vmax + 1’] >>
   rw [] >>
   res_tac >> rfs [] >>
   ‘n' <> rn’ by (
     fs [Abbr ‘rn’] >>
     fs [ctxt_max_def] >> res_tac >> rfs [])) >>
   TRY (
   rename [‘s.locals |+ (rt,w)’] >>
   rw [FLOOKUP_UPDATE] >>
   res_tac >> fs [] >> rveq >> fs []
   >- (
    cases_on ‘v’ >> fs [wlab_wloc_def] >>
    rfs [FDOM_FLOOKUP] >>
    cases_on ‘v’ >> fs []) >>
   ‘n <> n'’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     fs [distinct_vars_def] >> res_tac >> rfs [])) >>
   qmatch_goalsub_rename_tac ‘lookup nn _’ >>
   qmatch_goalsub_rename_tac ‘insert rn _ _’ >>
   fs [lookup_insert, lookup_inter] >>
   ‘LENGTH (gen_temps tmp (LENGTH les)) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule MEM_ZIP >>
   strip_tac >>
   drule lookup_alist_insert >>
   disch_then (qspec_then ‘st.locals’ assume_tac) >>
   fs [] >>
   ‘ALOOKUP (ZIP
             (gen_temps tmp (LENGTH les),
              MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])) nn = NONE’ by (
     TRY (fs [Abbr ‘rn’]) >>
     fs [ALOOKUP_NONE] >>
     CCONTR_TAC >> fs [MEM_MAP] >>
     first_x_assum (qspec_then ‘y’ assume_tac) >>
     fs [] >> rveq >> fs [FST] >>
     qmatch_asmsub_rename_tac ‘nt < LENGTH _’ >>

     ‘tmp <= EL nt (gen_temps tmp (LENGTH les))’ by
       fs [gen_temps_def] >>
     imp_res_tac compile_exps_out_rel >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   fs [domain_lookup] >>
   TRY (cases_on ‘v’ >> fs [wlab_wloc_def]) >> NO_TAC) >>
   (
   strip_tac >> fs [Abbr ‘rn’, Abbr ‘lns’] >>
   cases_on ‘res’ >> fs [] >> rveq
   (* NONE case of return handler *)
   >- (
    qexists_tac ‘ck + ck' + ck'' + 1’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck' + ck'' + 1’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
    drule loop_eval_nested_assign_distinct_eq >>
    disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
    impl_tac
    >- (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     rewrite_tac [distinct_lists_def] >>
     fs [EVERY_GENLIST] >>
     rw [] >>
     CCONTR_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exps_le_tmp_domain >>
     disch_then drule >>
     qmatch_asmsub_rename_tac ‘tmp + nx’ >>
     disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
     rfs [] >>
     fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
     >- (
      qmatch_asmsub_rename_tac ‘ MEM _ (var_cexp cv)’ >>
      ‘?v. eval s cv = SOME v’ by (
        qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
        fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> fs [locals_rel_def] >>
      res_tac >> rfs [] >> rveq >> fs []) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck' + ck'' + 1’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘pcal’ assume_tac) >>
    fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
    fs [Abbr ‘pcal’, nested_seq_def] >>
    rewrite_tac [evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    fs [get_vars_local_clock_upd_eq] >>
    ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    fs [] >> pop_assum kall_tac >>
    fs [find_code_def] >>
    pop_assum mp_tac >>
    rewrite_tac [wlab_wloc_def] >>
    rfs [] >>
    fs [cut_res_def, cut_state_def] >>
    ‘LENGTH ((gen_temps tmp (LENGTH les))) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ mp_tac) >>
    strip_tac >>  fs [] >>
    ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
      qsuff_tac ‘domain l ⊆ domain st.locals’
      >- fs [SUBSET_DEF] >>
      imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
      imp_res_tac locals_rel_intro >>
      imp_res_tac cut_sets_union_domain_subset >>
      fs [SUBSET_DEF]) >>
    fs [] >>
    ‘st.clock <> 0’ by fs [state_rel_def] >>
    fs [dec_clock_def] >>
    rfs [set_var_def] >>
    qpat_x_assum ‘ evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'' + 1’ assume_tac) >>
    fs [] >>
    fs [ocompile_def] >>
    drule loop_liveProofTheory.optimise_correct >>
    fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    rfs [] >>
    qpat_x_assum ‘evaluate (compile _ _ p, _) = (_,t1')’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘1’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    strip_tac >>
    fs [cut_res_def, cut_state_def] >>
    ‘domain l ⊆ domain t1'.locals’ by (
      imp_res_tac locals_rel_intro >>
      fs [SUBSET_INSERT_RIGHT]) >>
    fs [dec_clock_def] >> rveq >> fs [] >>
    conj_tac >- fs [state_rel_def] >>
    qpat_x_assum ‘locals_rel _ _ s1.locals _’ assume_tac >>
    fs [locals_rel_def] >>
    conj_tac >- fs [domain_inter, SUBSET_DEF] >>
    rw [] >>
    res_tac >> fs [] >>
    fs [lookup_inter, domain_lookup]) >>
   qexists_tac ‘ck + ck' + ck''’ >>
   qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + ck''’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   ‘MAP (eval st) les =
    MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
   drule loop_eval_nested_assign_distinct_eq >>
   disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
   impl_tac
   >- (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    rewrite_tac [distinct_lists_def] >>
    fs [EVERY_GENLIST] >>
    rw [] >>
    CCONTR_TAC >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exps_le_tmp_domain >>
    disch_then drule >>
    qmatch_asmsub_rename_tac ‘tmp + nx’ >>
    disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
    rfs [] >>
    fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
    >- (
     qmatch_asmsub_rename_tac ‘MEM _ (var_cexp cv)’ >>
     ‘?v. eval s cv = SOME v’ by (
       qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> fs [locals_rel_def] >>
    res_tac >> rfs [] >> rveq >> fs []) >>
   strip_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + ck''’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pcal’ assume_tac) >>
   fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
   fs [Abbr ‘pcal’, nested_seq_def] >>
   rewrite_tac [evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   fs [get_vars_local_clock_upd_eq] >>
   ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
     ho_match_mp_tac get_vars_local_update_some_eq >>
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   fs [] >> pop_assum kall_tac >>
   fs [find_code_def] >>
   pop_assum mp_tac >>
   rewrite_tac [wlab_wloc_def] >>
   rfs [] >>
   fs [cut_res_def, cut_state_def] >>
   ‘LENGTH ((gen_temps tmp (LENGTH les))) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule domain_alist_insert >>
   disch_then (qspec_then ‘st.locals’ mp_tac) >>
   strip_tac >>  fs [] >>
   ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
     qsuff_tac ‘domain l ⊆ domain st.locals’
     >- fs [SUBSET_DEF] >>
     imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
     imp_res_tac locals_rel_intro >>
     imp_res_tac cut_sets_union_domain_subset >>
     fs [SUBSET_DEF]) >>
   fs [] >>
   ‘st.clock <> 0’ by fs [state_rel_def] >>
   fs [dec_clock_def] >>
   qpat_x_assum ‘ evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck''’ assume_tac) >>
   fs [] >>
   fs [ocompile_def] >>
   drule loop_liveProofTheory.optimise_correct >>
   fs [] >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   rfs [set_var_def] >>
   qmatch_asmsub_rename_tac ‘rx ≠ Error’ >>
   cases_on ‘rx’ >> fs [] >> rveq >> fs [] >>
   fs [cut_res_def, cut_state_def] >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   fs [code_rel_def]))
  >- (
   (* case split on handler option variable *)
   fs [CaseEq "option"] >> rveq >> fs []
   (* NONE case of excp handler *)
   >- (
    fs [Abbr ‘lns’] >>
    qexists_tac ‘ck + ck'’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
    drule loop_eval_nested_assign_distinct_eq >>
    disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
    impl_tac
    >- (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     rewrite_tac [distinct_lists_def] >>
     fs [EVERY_GENLIST] >>
     rw [] >>
     CCONTR_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exps_le_tmp_domain >>
     disch_then drule >>
     qmatch_asmsub_rename_tac ‘tmp + nx’ >>
     disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
     rfs [] >>
     fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
     >- (
      qmatch_asmsub_rename_tac ‘ MEM _ (var_cexp cv)’ >>
      ‘?v. eval s cv = SOME v’ by (
        qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
        fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> fs [locals_rel_def] >>
      res_tac >> rfs [] >> rveq >> fs []) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘pcal’ assume_tac) >>
    fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
    fs [Abbr ‘pcal’, nested_seq_def] >>
    rewrite_tac [evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    fs [get_vars_local_clock_upd_eq] >>
    ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    fs [] >> pop_assum kall_tac >>
    fs [find_code_def] >>
    pop_assum mp_tac >>
    rewrite_tac [wlab_wloc_def] >>
    rfs [] >>
    fs [cut_res_def, cut_state_def] >>
    ‘LENGTH ((gen_temps tmp (LENGTH les))) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ mp_tac) >>
    strip_tac >>  fs [] >>
    ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
      qsuff_tac ‘domain l ⊆ domain st.locals’
      >- fs [SUBSET_DEF] >>
      imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
      imp_res_tac locals_rel_intro >>
      imp_res_tac cut_sets_union_domain_subset >>
      fs [SUBSET_DEF]) >>
    fs [] >>
    ‘st.clock <> 0’ by fs [state_rel_def] >>
    fs [dec_clock_def] >>
    rfs [set_var_def] >>
    qpat_x_assum ‘ evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
    fs [ocompile_def] >>
    drule loop_liveProofTheory.optimise_correct >>
    fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    pop_assum kall_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘1’ assume_tac) >>
    fs [] >>
    pop_assum kall_tac >>
    rfs [] >>
    fs [evaluate_def, cut_res_def] >>
    strip_tac >> fs [] >> rveq >>
    fs [call_env_def] >>
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    fs [state_rel_def, code_rel_def]) >>
   (* SOME case of excp handler *)
   cases_on ‘v3’ >> fs [] >>
   fs [Abbr ‘lns’] >>
   (* cannot delay case split on exp values
      because of clock inst *)
   reverse (cases_on ‘c = c'’) >> fs []
   >- (
    (* absent eid *)
    qexists_tac ‘ck + ck'’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
    drule loop_eval_nested_assign_distinct_eq >>
    disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
    impl_tac
    >- (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     rewrite_tac [distinct_lists_def] >>
     fs [EVERY_GENLIST] >>
     rw [] >>
     CCONTR_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exps_le_tmp_domain >>
     disch_then drule >>
     qmatch_asmsub_rename_tac ‘tmp + nx’ >>
     disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
     rfs [] >>
     fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
     >- (
      qmatch_asmsub_rename_tac ‘ MEM _ (var_cexp cv)’ >>
      ‘?v. eval s cv = SOME v’ by (
        qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
        fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> fs [locals_rel_def] >>
      res_tac >> rfs [] >> rveq >> fs []) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘pcal’ assume_tac) >>
    fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
    fs [Abbr ‘pcal’, nested_seq_def] >>
    rewrite_tac [evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    fs [get_vars_local_clock_upd_eq] >>
    ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    fs [] >> pop_assum kall_tac >>
    fs [find_code_def] >>
    pop_assum mp_tac >>
    rewrite_tac [wlab_wloc_def] >>
    rfs [] >>
    fs [cut_res_def, cut_state_def] >>
    ‘LENGTH ((gen_temps tmp (LENGTH les))) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ mp_tac) >>
    strip_tac >>  fs [] >>
    ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
      qsuff_tac ‘domain l ⊆ domain st.locals’
      >- fs [SUBSET_DEF] >>
      imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
      imp_res_tac locals_rel_intro >>
      imp_res_tac cut_sets_union_domain_subset >>
      fs [SUBSET_DEF]) >>
    fs [] >>
    ‘st.clock <> 0’ by fs [state_rel_def] >>
    fs [dec_clock_def] >>
    rfs [set_var_def] >>
    qpat_x_assum ‘ evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
    fs [ocompile_def] >>
    drule loop_liveProofTheory.optimise_correct >>
    fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    pop_assum kall_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘1’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    rfs [] >>
    fs [evaluate_def] >>
    fs [get_var_imm_def, asmTheory.word_cmp_def] >>
    fs [evaluate_def] >>
    fs [cut_res_def] >>
    strip_tac >> fs [] >> rveq >>
    fs [call_env_def] >>
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    fs [state_rel_def, code_rel_def]) >>
   (* handling exception *)
   last_x_assum (qspecl_then
                 [‘t1 with locals :=
                   insert (ctxt.vmax + 1) (Word c')
                   (inter (alist_insert (gen_temps tmp (LENGTH les))
                           (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])
                           st.locals) l)’,
                  ‘ctxt’, ‘l’] mp_tac) >>
   impl_tac
   >- (
   fs [crepSemTheory.set_var_def, ctxt_fc_def] >>
   conj_tac >- fs [state_rel_def] >>
   conj_tac >- fs [code_rel_def] >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [domain_inter] >>
    ‘LENGTH (gen_temps tmp (LENGTH les)) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ assume_tac) >>
    fs [] >>
    qsuff_tac
    ‘(domain st.locals ∪ set (gen_temps tmp (LENGTH les))) ∩ domain l = domain l’
    >- fs [SUBSET_INSERT_RIGHT] >>
    fs [INTER_SUBSET_EQN |> CONJUNCT2] >>
    imp_res_tac compile_exps_out_rel >> fs [] >> rveq >> fs [] >>
    imp_res_tac cut_sets_union_domain_subset >>
    fs [SUBSET_DEF]) >>
   rw [] >>
   res_tac >> rfs [] >>
   ‘n' <> ctxt.vmax + 1’ by (
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   qmatch_goalsub_rename_tac ‘lookup nn _’ >>
   fs [lookup_insert, lookup_inter] >>
   ‘LENGTH (gen_temps tmp (LENGTH les)) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule MEM_ZIP >>
   strip_tac >>
   drule lookup_alist_insert >>
   disch_then (qspec_then ‘st.locals’ assume_tac) >>
   fs [] >>
   ‘ALOOKUP (ZIP
             (gen_temps tmp (LENGTH les),
              MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])) nn = NONE’ by (
     fs [ALOOKUP_NONE] >>
     CCONTR_TAC >> fs [MEM_MAP] >>
     first_x_assum (qspec_then ‘y’ assume_tac) >>
     fs [] >> rveq >> fs [FST] >>
     qmatch_asmsub_rename_tac ‘nt < LENGTH _’ >>
     ‘tmp <= EL nt (gen_temps tmp (LENGTH les))’ by
       fs [gen_temps_def] >>
     imp_res_tac compile_exps_out_rel >>
     fs [ctxt_max_def] >> res_tac >> rfs []) >>
   fs [domain_lookup]) >>
   strip_tac >> fs [] >>
   cases_on ‘res’ >> fs []
   >- (
    qexists_tac ‘ck + ck' + ck'' + 3’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck' + ck'' + 3’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
    drule loop_eval_nested_assign_distinct_eq >>
    disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
    impl_tac
    >- (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     rewrite_tac [distinct_lists_def] >>
     fs [EVERY_GENLIST] >>
     rw [] >>
     CCONTR_TAC >> fs [] >>
     imp_res_tac locals_rel_intro >>
     drule compile_exps_le_tmp_domain >>
     disch_then drule >>
     qmatch_asmsub_rename_tac ‘tmp + nx’ >>
     disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
     rfs [] >>
     fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
     >- (
      qmatch_asmsub_rename_tac ‘ MEM _ (var_cexp cv)’ >>
      ‘?v. eval s cv = SOME v’ by (
        qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
        fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
      drule_all eval_some_var_cexp_local_lookup >>
      strip_tac >> fs [locals_rel_def] >>
      res_tac >> rfs [] >> rveq >> fs []) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck' + ck'' + 3’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘pcal’ assume_tac) >>
    fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
    fs [Abbr ‘pcal’, nested_seq_def] >>
    rewrite_tac [evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    fs [get_vars_local_clock_upd_eq] >>
    ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
      ho_match_mp_tac get_vars_local_update_some_eq >>
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    fs [] >> pop_assum kall_tac >>
    fs [find_code_def] >>
    pop_assum mp_tac >>
    rewrite_tac [wlab_wloc_def] >>
    rfs [] >>
    fs [cut_res_def, cut_state_def] >>
    ‘LENGTH ((gen_temps tmp (LENGTH les))) =
     LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
      fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
      imp_res_tac compile_exps_out_rel >> fs [] >>
      metis_tac [LENGTH_MAP]) >>
    drule domain_alist_insert >>
    disch_then (qspec_then ‘st.locals’ mp_tac) >>
    strip_tac >>  fs [] >>
    ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
      qsuff_tac ‘domain l ⊆ domain st.locals’
      >- fs [SUBSET_DEF] >>
      imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
      imp_res_tac locals_rel_intro >>
      imp_res_tac cut_sets_union_domain_subset >>
      fs [SUBSET_DEF]) >>
    fs [] >>
    ‘st.clock <> 0’ by fs [state_rel_def] >>
    fs [dec_clock_def] >>
    rfs [set_var_def] >>
    qpat_x_assum ‘evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'' + 3’ assume_tac) >>
    fs [] >>
    fs [ocompile_def] >>
    drule loop_liveProofTheory.optimise_correct >>
    fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    rfs [] >>
    fs [evaluate_def] >>
    fs [get_var_imm_def, asmTheory.word_cmp_def] >>
    fs [evaluate_def, dec_clock_def] >>
    qpat_x_assum ‘evaluate (compile _ _ p'', _) = _’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘2’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    strip_tac >>
    fs [cut_res_def, cut_state_def] >>
    ‘domain l ⊆ domain t1'.locals’ by (
      imp_res_tac locals_rel_intro >>
      fs [SUBSET_INSERT_RIGHT]) >>
    fs [dec_clock_def] >> rveq >> fs [] >>
    fs [cut_res_def, cut_state_def] >>
    fs [domain_inter] >>
    fs [dec_clock_def] >> rveq >> fs [] >>
    conj_tac >- fs [state_rel_def] >>
    qpat_x_assum ‘locals_rel _ _ s1.locals _’ assume_tac >>
    fs [locals_rel_def] >>
    conj_tac >- fs [domain_inter, SUBSET_DEF] >>
    rw [] >>
    res_tac >> fs [] >>
    fs [lookup_inter, domain_lookup]) >>
   cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
   (
   qexists_tac ‘ck + ck' + ck'' + 1’ >>
   qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + ck'' + 1’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt.funcs) (args ++ [Label fname]))’ by fs [] >>
   drule loop_eval_nested_assign_distinct_eq >>
   disch_then (qspec_then ‘gen_temps tmp (LENGTH les)’ mp_tac) >>
   impl_tac
   >- (
    fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
    rewrite_tac [distinct_lists_def] >>
    fs [EVERY_GENLIST] >>
    rw [] >>
    CCONTR_TAC >> fs [] >>
    imp_res_tac locals_rel_intro >>
    drule compile_exps_le_tmp_domain >>
    disch_then drule >>
    qmatch_asmsub_rename_tac ‘tmp + nx’ >>
    disch_then (qspec_then ‘tmp + nx’ assume_tac) >>
    rfs [] >>
    fs [MEM_FLAT, MEM_MAP] >> rveq >> fs []
    >- (
     qmatch_asmsub_rename_tac ‘ MEM _ (var_cexp cv)’ >>
     ‘?v. eval s cv = SOME v’ by (
       qpat_x_assum ‘MAP _ _ = MAP SOME args’ assume_tac >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL]) >>
     drule_all eval_some_var_cexp_local_lookup >>
     strip_tac >> fs [locals_rel_def] >>
     res_tac >> rfs [] >> rveq >> fs []) >>
    drule_all eval_some_var_cexp_local_lookup >>
    strip_tac >> fs [locals_rel_def] >>
    res_tac >> rfs [] >> rveq >> fs []) >>
   strip_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck' + ck'' + 1’ assume_tac) >>
   drule evaluate_none_nested_seq_append >>
   disch_then (qspec_then ‘pcal’ assume_tac) >>
   fs [Abbr ‘ptmp’] >> pop_assum kall_tac >>
   fs [Abbr ‘pcal’, nested_seq_def] >>
   rewrite_tac [evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   fs [get_vars_local_clock_upd_eq] >>
   ‘get_vars (gen_temps tmp (LENGTH les))
    (st with locals :=
     alist_insert (gen_temps tmp (LENGTH les))
     (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt.funcs) args ++ [wlab_wloc ctxt.funcs (Label fname)])’ by (
     ho_match_mp_tac get_vars_local_update_some_eq >>
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   fs [] >> pop_assum kall_tac >>
   fs [find_code_def] >>
   pop_assum mp_tac >>
   rewrite_tac [wlab_wloc_def] >>
   rfs [] >>
   fs [cut_res_def, cut_state_def] >>
   ‘LENGTH ((gen_temps tmp (LENGTH les))) =
    LENGTH (MAP (wlab_wloc ctxt.funcs) args ++ [Loc loc 0])’ by (
     fs [gen_temps_def, ALL_DISTINCT_GENLIST] >>
     imp_res_tac compile_exps_out_rel >> fs [] >>
     metis_tac [LENGTH_MAP]) >>
   drule domain_alist_insert >>
   disch_then (qspec_then ‘st.locals’ mp_tac) >>
   strip_tac >>  fs [] >>
   ‘domain l ⊆ domain st.locals ∪ set (gen_temps tmp (LENGTH les))’ by (
     qsuff_tac ‘domain l ⊆ domain st.locals’
     >- fs [SUBSET_DEF] >>
     imp_res_tac compile_exps_out_rel >> rveq >> fs [] >>
     imp_res_tac locals_rel_intro >>
     imp_res_tac cut_sets_union_domain_subset >>
     fs [SUBSET_DEF]) >>
   fs [] >>
   ‘st.clock <> 0’ by fs [state_rel_def] >>
   fs [dec_clock_def] >>
   rfs [set_var_def] >>
   qpat_x_assum ‘evaluate (compile _ _ prog, _) = (_,t1)’ assume_tac >>
   drule evaluate_add_clock_eq >>
   fs [] >>
   disch_then (qspec_then ‘ck'' + 1’ assume_tac) >>
   fs [] >>
   fs [ocompile_def] >>
   drule loop_liveProofTheory.optimise_correct >>
   fs [] >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   rfs [] >>
   fs [evaluate_def] >>
   fs [get_var_imm_def, asmTheory.word_cmp_def] >>
   fs [evaluate_def, dec_clock_def] >>
   fs [cut_res_def] >>
   strip_tac >> fs [] >> rveq >> fs [])) >>
   fcalled_timed_out_tac
QED


Theorem ncompile_correct:
   ^(compile_prog_tm ())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [compile_Skip_Break_Continue, compile_Tick,
          compile_Seq, compile_Return, compile_Raise,
          compile_Store, compile_StoreByte, compile_StoreGlob,
          compile_Assign, compile_Dec, compile_If, compile_FFI,
          compile_While, compile_Call]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED


Theorem ocompile_correct:
  evaluate (p,s) = (res,s1) ∧ state_rel s t ∧
  mem_rel ctxt.funcs s.memory t.memory ∧
  globals_rel ctxt.funcs s.globals t.globals ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt l s.locals t.locals ∧ res ≠ SOME Error ∧ res ≠ SOME Break ∧
  res ≠ SOME Continue ∧ res ≠ NONE ⇒
  ∃ck res1 t1.
    evaluate (ocompile ctxt l p,t with clock := t.clock + ck) =
    (res1,t1) ∧ state_rel s1 t1 ∧ mem_rel ctxt.funcs s1.memory t1.memory ∧
    globals_rel ctxt.funcs s1.globals t1.globals ∧
    code_rel ctxt s1.code t1.code ∧
    case res of
     | NONE => F
     | SOME Error => F
     | SOME TimeOut => res1 = SOME TimeOut
     | SOME Break => F
     | SOME Continue => F
     | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt.funcs v)) ∧
           ∀f. v = Label f ⇒ f ∈ FDOM ctxt.funcs
     | SOME (Exception eid) => res1 = SOME (Exception (Word eid))
     | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)

Proof
  rw [] >>
  drule_all ncompile_correct >>
  strip_tac >> fs [] >>
  fs [ocompile_def] >>
  drule loop_liveProofTheory.optimise_correct >>
  impl_tac
  >- (
   cases_on ‘res’ >> fs [] >>
   cases_on ‘x’ >> fs []) >>
  strip_tac >>
  qexists_tac ‘ck’ >> fs [] >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs []
QED


Theorem distinct_make_funcs:
  !crep_code. distinct_funcs (make_funcs crep_code)
Proof
  rw [distinct_funcs_def] >>
  fs [make_funcs_def] >>
  qmatch_asmsub_abbrev_tac ‘MAP2 _ (GENLIST _ _) ps’ >>
  dxrule ALOOKUP_MEM >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  strip_tac >>
  fs [MEM_EL] >>
  ‘n < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST (λn. n + first_name) (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP] >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num”,
                     “:'c” |-> “:'a # num # num”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST (λn. n + first_name) (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP]  >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num”,
                     “:'c” |-> “:'a # num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs [] >>
  ‘n < MIN (LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  drule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c” |-> “:num # num”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  dxrule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c” |-> “:num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs []
QED


Theorem map_map2_fst:
  !xs ys h. LENGTH xs = LENGTH ys ==>
   MAP FST
       (MAP2
        (λx (n,p,b). (x,GENLIST I (LENGTH p),h p b)) xs ys) = xs
Proof
  Induct_on ‘xs’ >>
  rw [] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  cases_on ‘h''’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem mem_lookup_fromalist_some:
  !xs n x.
   ALL_DISTINCT (MAP FST xs) ∧
   MEM (n,x) xs ==>
   lookup n (fromAList xs) = SOME x
Proof
  Induct >>
  rw [] >> fs [] >>
  fs [fromAList_def] >>
  cases_on ‘h’ >>
  fs [fromAList_def] >>
  fs [lookup_insert] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> fs [MEM_MAP] >>
  first_x_assum (qspec_then ‘(n,x)’ mp_tac) >>
  fs []
QED


Theorem first_compile_prog_all_distinct:
  !crep_code.
    ALL_DISTINCT (MAP FST (compile_prog crep_code))
Proof
  rw [] >>
  fs [crep_to_loopTheory.compile_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP FST ls’ >>
  qsuff_tac ‘MAP FST ls = GENLIST ((λn. n + first_name)) (LENGTH crep_code)’
  >- (
   strip_tac >>
   fs [ALL_DISTINCT_GENLIST]) >>
  fs [Abbr ‘ls’] >>
  fs [MAP_MAP_o] >>
  ‘LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code)) = LENGTH crep_code’ by fs [] >>
  drule (INST_TYPE [“:'a”|->“:num”,
                      “:'b”|->“:mlstring”,
                      “:'c”|->“:num”,
                      “:'d”|->“:'a crepLang$prog”,
                      “:'e”|-> “:'a prog”] map_map2_fst) >>
  disch_then (qspec_then ‘λparams body. loop_live$optimise
                          (comp_func (make_funcs crep_code)
                           params body)’ mp_tac) >> fs []
QED

Theorem mk_ctxt_code_imp_code_rel:
  !crep_code start np. ALL_DISTINCT (MAP FST crep_code) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  code_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0)
            (alist_to_fmap crep_code)
            (fromAList (crep_to_loop$compile_prog crep_code))
Proof
  rw [code_rel_def, mk_ctxt_def]
  >- fs [distinct_make_funcs] >>
  fs [mk_ctxt_def, make_funcs_def] >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  fs [MEM_EL] >> rveq >>
  qexists_tac ‘n + first_name’ >>
  conj_tac
  >- (
   ho_match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac
   >- (
    qmatch_goalsub_abbrev_tac ‘MAP FST ls’ >>
    ‘MAP FST ls = MAP FST crep_code’ by (
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      conj_tac >- fs [Abbr ‘ls’] >>
      conj_tac >- fs [Abbr ‘ls’] >>
      rw [] >>
      fs [Abbr ‘ls’] >>
      qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
      ‘n' < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
      drule (INST_TYPE [“:'a”|->“:mlstring”,
                        “:'b”|->“:num # num”,
                        “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
      disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
      strip_tac >> fs [] >>
      match_mp_tac EL_MAP >>
      fs []) >>
    fs []) >>
   fs [MEM_EL] >>
   qexists_tac ‘n’ >>
   fs [] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:mlstring”,
                     “:'b”|->“:num # num”,
                     “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   conj_asm1_tac
   >- (
    fs [EL_MAP] >>
    qpat_x_assum ‘_ = EL n crep_code’ (mp_tac o GSYM) >>
    fs []) >>
   fs [Abbr ‘ps’] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code))) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c”|-> “:num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [Abbr ‘ps’] >>
   ‘n < LENGTH (MAP (LENGTH ∘ FST ∘ SND) crep_code)’ by fs [] >>
   drule (INST_TYPE [“:'a”|->“:mlstring # num list # 'a crepLang$prog”,
                     “:'b”|->“:num”] EL_MAP) >>
   disch_then (qspec_then ‘LENGTH ∘ FST ∘ SND’ mp_tac) >>
   strip_tac >>
   fs [] >>
   qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
   fs []) >>
  fs [compile_prog_def, ctxt_fc_def] >>
  match_mp_tac mem_lookup_fromalist_some >>
  conj_tac
  >- metis_tac [(REWRITE_RULE
                 [crep_to_loopTheory.compile_prog_def, LET_THM]
                 first_compile_prog_all_distinct)] >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 _ ps _)’ >>
  ‘n < MIN (LENGTH ps) (LENGTH crep_code)’ by fs [Abbr ‘ps’] >>
  drule (INST_TYPE [“:'a”|->“:num”,
                    “:'b”|->“:mlstring # num list # 'a crepLang$prog”,
                    “:'c”|-> “:num # num list # 'a prog”] EL_MAP2) >>
  disch_then (qspec_then ‘λn' (name,params,body).
       (n',GENLIST I (LENGTH params),
        loop_live$optimise (comp_func (make_funcs crep_code)
                  params body))’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >> fs [] >>
  fs [Abbr ‘ps’] >>
  qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
  fs [] >>
  fs [comp_func_def] >>
  fs [mk_ctxt_def, make_vmap_def, make_funcs_def] >>
  fs [loop_liveTheory.optimise_def, ocompile_def] >>
  fs [pan_commonPropsTheory.list_max_i_genlist]
QED


Theorem make_funcs_domain_compile_prog:
  !start lc crep_code. FLOOKUP (make_funcs crep_code) start = SOME (lc,0) ==>
    lc ∈ domain (fromAList (compile_prog crep_code))
Proof
  rw [] >>
  fs [domain_fromAList] >>
  fs [make_funcs_def] >>
  drule ALOOKUP_MEM >>
  pop_assum kall_tac >>
  strip_tac >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  conj_tac
  >- fs [compile_prog_def] >>
  qmatch_asmsub_abbrev_tac ‘MAP2 _ (GENLIST (λn. n + first_name) _) ps’ >>
  ‘n < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST (λn. n + first_name) (LENGTH crep_code)) ps))’ by
    fs [Abbr ‘ps’, LENGTH_MAP] >>
  dxrule (INST_TYPE [“:'a”|->“:mlstring”,
                     “:'b”|->“:num # num”,
                     “:'c” |-> “:mlstring # num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
  strip_tac >> fs [] >>
  fs [compile_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP _ pps)’ >>
  ‘n < LENGTH pps’ by fs [Abbr ‘pps’] >>
  dxrule (INST_TYPE [“:'a”|->“:num # num list # 'a prog”,
                     “:'b”|->“:num”] EL_MAP) >>
  disch_then (qspec_then ‘FST’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘pps’] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP2 ffs _ _)’ >>
  ‘n < MIN (LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code)))
   (LENGTH crep_code)’ by fs [] >>
  dxrule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:mlstring # num list # 'a crepLang$prog”,
                     “:'c” |-> “:num # num list # 'a prog”] EL_MAP2) >>
  disch_then (qspec_then ‘ffs’ mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [Abbr ‘ffs’] >>
  cases_on ‘EL n crep_code’ >> fs [] >>
  cases_on ‘r’ >> fs [] >>
  ‘n < MIN (LENGTH (GENLIST (λn. n + first_name) (LENGTH crep_code)))
   (LENGTH ps)’ by fs [Abbr ‘ps’] >>
  dxrule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c” |-> “:num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
  strip_tac >> fs []
QED

(* move to pan_commonProps *)
Theorem alookup_el_pair_eq_el:
  !prog start cp n.
   EL n prog = (start, [], SND(SND(EL n prog))) /\
   ALL_DISTINCT (MAP FST prog) /\ n < LENGTH prog /\
   ALOOKUP prog start = SOME ([],cp) ==>
    EL n prog = (start, [], cp)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs [] >> rveq >> fs []
  >- (cases_on ‘h’ >> rfs []) >>
  last_x_assum match_mp_tac >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘q = start’ >> fs [] >> rveq >> fs [] >>
  fs [MEM_EL] >>
  last_x_assum (qspec_then ‘n'’ mp_tac) >>
  fs [] >>
  strip_tac >>
  metis_tac [el_pair_map_fst_el]
QED


Theorem initial_prog_make_funcs_el:
  !prog start n. FLOOKUP (make_funcs prog) start = SOME (n + first_name,0) ==>
   (start, [], (SND o SND) (EL n prog)) = EL n prog /\ n < LENGTH prog
Proof
  rw [] >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  dxrule ALOOKUP_MEM >>
  fs [] >>
  strip_tac >>
  fs [MEM_EL] >>
  pop_assum mp_tac >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 ff ws xs)’ >>
  ‘EL n' (MAP2 ff ws xs) = ff (EL n' ws) (EL n' xs)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  strip_tac >>
  fs [] >>
  pop_assum mp_tac >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 ff ws xs)’ >>
  ‘EL n' (MAP2 ff ws xs) = ff (EL n' ws) (EL n' xs)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  ‘EL n (MAP FST prog) = FST (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs [])  >>
  fs [] >>
  pop_assum kall_tac >>
  ‘EL n (MAP (LENGTH ∘ FST ∘ SND) prog) =
   (LENGTH ∘ FST ∘ SND) (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs [])  >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  cases_on ‘EL n prog’ >>
  fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem compile_prog_distinct_params:
  ∀prog.
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog ⇒
    EVERY (λ(name,params,body). ALL_DISTINCT params) (compile_prog prog)
Proof
  rw [] >>
  fs [EVERY_MEM] >>
  rw [] >>
  PairCases_on ‘e’ >> fs [] >>
  fs [compile_prog_def] >>
  fs [MEM_EL] >>
  qmatch_asmsub_abbrev_tac ‘MAP2 ff xs _’ >>
  ‘EL n (MAP2 ff xs prog) = ff (EL n xs) (EL n prog)’ by (
    match_mp_tac EL_MAP2 >>
    fs [Abbr ‘xs’]) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ff’] >>
  cases_on ‘EL n prog’ >>
  cases_on ‘r’ >> fs [] >> rveq >>
  fs [ALL_DISTINCT_GENLIST]
QED


Theorem state_rel_imp_semantics:
  !s t crep_code start prog lc. s.memaddrs = t.mdomain ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧ s.base_addr = t.base_addr ∧
  mem_rel (make_funcs crep_code) s.memory t.memory ∧
  globals_rel (make_funcs crep_code) s.globals t.globals ∧
  ALL_DISTINCT (MAP FST crep_code) ∧
  s.code = alist_to_fmap crep_code ∧
  t.code = fromAList (crep_to_loop$compile_prog crep_code) ∧
  s.locals = FEMPTY ∧
  ALOOKUP crep_code start = SOME ([],prog) ∧
  FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) ∧
  semantics s start <> Fail ==>
  semantics t lc = semantics s start
Proof
  rw [] >>
  drule mk_ctxt_code_imp_code_rel >>
  disch_then (qspecl_then [‘start’, ‘prog’] mp_tac) >>
  fs [] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘code_rel nctxt _ _’ >>
  reverse (Cases_on ‘semantics s start’) >> fs []
  >- (
   (* Termination case of crep semantics *)
   fs [crepSemTheory.semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   rw [] >>
   rw [loopSemTheory.semantics_def]
   >- (
    (* the fail case of loop semantics *)
    qhdtm_x_assum ‘crepSem$evaluate’ kall_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >>
    last_x_assum(qspec_then ‘k'’ mp_tac) >> simp[] >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    CCONTR_TAC >> fs [] >>
    drule ocompile_correct >> fs [] >>
    map_every qexists_tac [‘t with clock := k'’, ‘LN’, ‘nctxt’] >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
     fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
     fs [locals_rel_def, distinct_vars_def, ctxt_max_def] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    CCONTR_TAC >>
    fs [] >>
    fs [ocompile_def, compile_def] >>
    fs [compile_exp_def] >>
    fs [gen_temps_def, MAP2_DEF] >>
    fs [nested_seq_def] >>
    ‘find_lab nctxt start = lc’ by (
      fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
    fs [] >>
    drule make_funcs_domain_compile_prog >>
    strip_tac >>
    fs [loop_liveTheory.optimise_def] >>
    fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
    fs [] >>
    fs [loop_liveTheory.shrink_def] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rveq >> fs [] >>
    fs [loop_liveTheory.mark_all_def] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rveq >> gs [] >>
    cases_on ‘t1' ∧ t1''’ >>
    gs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
      rw [Once loopSemTheory.evaluate_def] >>
      rw [Once loopSemTheory.evaluate_def] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def] >> rveq >>
      ‘res = NONE ∧ s1 = t with clock := ck + k' ∧ res' = NONE ∧ s1' = s1’ by
        fs [evaluate_def] >>
      qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
      qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
      rveq >> fs [] >>
      CCONTR_TAC >> fs [] >>
      cases_on ‘evaluate
                (Call NONE (SOME (find_lab nctxt start)) [] NONE,
                 t with clock := k')’ >>
      fs [] >>
      cases_on ‘q'’ >> fs []
      >- (
        drule evaluate_add_clock_eq >>
        disch_then (qspec_then ‘ck’ mp_tac) >>
        strip_tac >> fs [] >> rveq >> fs [] >>
        qpat_x_assum ‘_ = (res1,t1)’ mp_tac >>
        rw [evaluate_def] >>
        CCONTR_TAC >>
        fs [] >> rveq >> fs [] >>
        cases_on ‘q’ >> fs [] >>
        cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
      cases_on ‘x’ >> fs [] >> (
        drule evaluate_add_clock_eq >>
        disch_then (qspec_then ‘ck’ mp_tac) >>
        strip_tac >> fs [] >> rveq >> fs [] >>
        rveq >> fs [] >>
        cases_on ‘q’ >> fs [] >>
        cases_on ‘x’ >> fs [] >> rveq >> fs []))
    >- (
      cases_on ‘t1''’ >> fs []
      >- (
        qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
        rw [Once loopSemTheory.evaluate_def] >>
        rw [Once loopSemTheory.evaluate_def] >>
        pairarg_tac >> fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        pairarg_tac >> fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        pairarg_tac >> fs [] >>
        pop_assum mp_tac >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        strip_tac >>
        fs [loop_liveTheory.shrink_def,
            lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
        rveq >> fs [lookup_def] >>  rveq >> fs [] >>
        gs [loop_liveTheory.mark_all_def]) >>
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rw [Once loopSemTheory.evaluate_def] >>
      rw [Once loopSemTheory.evaluate_def] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
   (* the termination/diverging case of loop semantics *)
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* the termination case of loop semantics *)
   >- (
    rw [] >> fs [] >>
    drule ocompile_correct >> fs [] >>
    ‘r ≠ SOME Error ∧
     r ≠ SOME Break ∧ r ≠ SOME Continue ∧ r ≠ NONE’ by (
      cases_on ‘r’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
    fs [] >>
    disch_then (qspecl_then [‘t with clock := k’, ‘LN’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def] >>
     fs [locals_rel_def, distinct_vars_def, ctxt_max_def]) >>
    strip_tac >> fs [] >>
    fs [ocompile_def, compile_def] >>
    fs [compile_exp_def] >>
    fs [gen_temps_def, MAP2_DEF] >>
    fs [nested_seq_def] >>
    ‘find_lab nctxt start = lc’ by (
      fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
    fs [] >>
    drule make_funcs_domain_compile_prog >>
    strip_tac >>
    fs [loop_liveTheory.optimise_def] >>
    fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
    fs [loop_liveTheory.shrink_def] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rveq >> fs [] >>
    fs [loop_liveTheory.mark_all_def] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rveq >> gs [] >>
    cases_on ‘t1' ∧ t1''’ >>
    gs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def] >> rveq >>
      ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
        fs [evaluate_def] >>
      qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
      qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
      rveq >> fs [] >>
      strip_tac >>
      drule loopPropsTheory.evaluate_add_clock_eq >>
      disch_then (qspec_then ‘k'’ mp_tac) >>
      impl_tac
      >- (
        CCONTR_TAC >> fs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
      qpat_x_assum ‘evaluate _ = (r', _)’ assume_tac >>
      drule loopPropsTheory.evaluate_add_clock_eq >>
      disch_then (qspec_then ‘ck + k’ mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      ntac 2 strip_tac >> fs[] >> rveq >> fs[] >>
      Cases_on ‘r’ >> fs[] >>
      Cases_on ‘r'’ >> fs [] >>
      Cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
      fs [state_rel_def] >>
      fs [loopSemTheory.state_accfupds, loopSemTheory.state_component_equality])
    >- (
      cases_on ‘t1''’ >> fs []
      >- (
        qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        pairarg_tac >> fs [] >>
        pairarg_tac >> fs [] >>
        pairarg_tac >> fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        strip_tac >>
        fs [loop_liveTheory.shrink_def,
            lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
        rveq >> fs [lookup_def] >>  rveq >> fs [] >>
        gs [loop_liveTheory.mark_all_def]) >>
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
   (* the diverging case of loop semantics *)
   rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
   drule ocompile_correct >> fs [] >>
   ‘r ≠ SOME Error ∧
    r ≠ SOME Break ∧ r ≠ SOME Continue ∧ r ≠ NONE’ by (
     cases_on ‘r’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘LN’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
    fs [locals_rel_def, distinct_vars_def, ctxt_max_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >> fs [] >>
   fs [ocompile_def, compile_def] >>
   fs [compile_exp_def] >>
   fs [gen_temps_def, MAP2_DEF] >>
   fs [nested_seq_def] >>
   ‘find_lab nctxt start = lc’ by (
     fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
   fs [] >>
   drule make_funcs_domain_compile_prog >>
   strip_tac >>
   fs [loop_liveTheory.optimise_def] >>
   fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
   fs [loop_liveTheory.shrink_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [loop_liveTheory.mark_all_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> gs [] >>
   cases_on ‘t1' ∧ t1''’ >>
   gs []
   >- (
    qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def] >> rveq >>
    ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
      fs [evaluate_def] >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    rveq >> fs [] >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck + k’ mp_tac) >> simp[] >>
    first_x_assum(qspec_then ‘ck + k’ mp_tac) >> simp[] >>
    every_case_tac >> fs[] >> rw[] >> rfs[])
   >- (
    cases_on ‘t1''’ >> fs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
   qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   strip_tac >>
   fs [loop_liveTheory.shrink_def,
       lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
   rveq >> fs [lookup_def] >>  rveq >> fs [] >>
   gs [loop_liveTheory.mark_all_def]) >>
  (* the diverging case of crep semantics *)
  fs [crepSemTheory.semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw [] >>
  rw [loopSemTheory.semantics_def]
  >- (
   (* the fail case of loop semantics *)
   fs[] >> rveq >> fs[] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   CCONTR_TAC >> fs [] >>
   drule ocompile_correct >> fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘LN’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
    fs [locals_rel_def, distinct_vars_def, ctxt_max_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   fs [ocompile_def, compile_def] >>
   fs [compile_exp_def] >>
   fs [gen_temps_def, MAP2_DEF] >>
   fs [nested_seq_def] >>
   ‘find_lab nctxt start = lc’ by (
     fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
   fs [] >>
   drule make_funcs_domain_compile_prog >>
   strip_tac >>
   fs [loop_liveTheory.optimise_def] >>
   fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
   fs [loop_liveTheory.shrink_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [loop_liveTheory.mark_all_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> gs [] >>
   cases_on ‘t1' ∧ t1''’ >>
   gs []
   >- (
    qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def] >> rveq >>
    ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
      fs [evaluate_def] >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    rveq >> fs [] >>
    CCONTR_TAC >> fs [] >>
    cases_on ‘evaluate
              (Call NONE (SOME (find_lab nctxt start)) [] NONE,
               t with clock := k)’ >>
    fs [] >>
    cases_on ‘q'’ >> fs []
    >- (
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘ck’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [] >>
      qpat_x_assum ‘_ = (res1,t1)’ mp_tac >>
      rw [evaluate_def] >>
      CCONTR_TAC >>
      fs [] >> rveq >> fs [] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
    cases_on ‘x’ >> fs [] >> (
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘ck’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [] >>
      rveq >> fs [] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs [] >> rveq >> fs []))
   >- (
    cases_on ‘t1''’ >> fs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rw [Once loopSemTheory.evaluate_def] >>
      rw [Once loopSemTheory.evaluate_def] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
   qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
   rw [Once loopSemTheory.evaluate_def] >>
   rw [Once loopSemTheory.evaluate_def] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   strip_tac >>
   fs [loop_liveTheory.shrink_def,
       lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
   rveq >> fs [lookup_def] >>  rveq >> fs [] >>
   gs [loop_liveTheory.mark_all_def]) >>
  (* the termination/diverging case of loop semantics *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* the termination case of loop semantics *)
  >- (
   rw [] >>  fs[] >>
   qpat_x_assum ‘∀x y. _’ (qspec_then ‘k’ mp_tac)>>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   strip_tac >>
   drule ocompile_correct >> fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘LN’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
    fs [locals_rel_def, distinct_vars_def, ctxt_max_def] >>
    last_x_assum (qspec_then ‘k’ assume_tac) >>
    rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   fs [ocompile_def, compile_def] >>
   fs [compile_exp_def] >>
   fs [gen_temps_def, MAP2_DEF] >>
   fs [nested_seq_def] >>
   ‘find_lab nctxt start = lc’ by (
     fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
   fs [] >>
   drule make_funcs_domain_compile_prog >>
   strip_tac >>
   fs [loop_liveTheory.optimise_def] >>
   fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
   fs [loop_liveTheory.shrink_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [loop_liveTheory.mark_all_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> gs [] >>
   cases_on ‘t1' ∧ t1''’ >>
   gs []
   >- (
    qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def] >> rveq >>
    ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
      fs [evaluate_def] >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    rveq >> fs [] >>
    cases_on ‘evaluate
              (Call NONE (SOME (find_lab nctxt start)) [] NONE,
               t with clock := k)’ >>
    fs [] >>
    cases_on ‘q'’ >> fs []
    >- (
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘ck’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [] >>
      qpat_x_assum ‘_ = (res1,t1)’ mp_tac >>
      rw [evaluate_def] >>
      CCONTR_TAC >>
      fs [] >> rveq >> fs [] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
    cases_on ‘x’ >> fs [] >> (
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘ck’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [] >>
      rveq >> fs [] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs [] >> rveq >> fs []))
   >- (
    cases_on ‘t1''’ >> fs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rw [Once loopSemTheory.evaluate_def] >>
      rw [Once loopSemTheory.evaluate_def] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
   qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
   rw [Once loopSemTheory.evaluate_def] >>
   rw [Once loopSemTheory.evaluate_def] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   pop_assum mp_tac >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   strip_tac >>
   fs [loop_liveTheory.shrink_def,
       lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
   rveq >> fs [lookup_def] >>  rveq >> fs [] >>
   gs [loop_liveTheory.mark_all_def]) >>
   (* the diverging case of word semantics *)
  rw [] >>
  qmatch_abbrev_tac ‘build_lprefix_lub l1 = build_lprefix_lub l2’ >>
  ‘(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2’
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac
  >- (
   UNABBREV_ALL_TAC >>
   conj_tac >>
   Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
   REWRITE_TAC[IMAGE_COMPOSE] >>
   match_mp_tac prefix_chain_lprefix_chain >>
   simp[prefix_chain_def,PULL_EXISTS] >>
   qx_genl_tac [‘k1’, ‘k2’] >>
   qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES >>
   simp[LESS_EQ_EXISTS] >>
   rw [] >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               crepPropsTheory.evaluate_add_clock_io_events_mono) >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               loopPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME lc) [] NONE’, ‘t with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME lc) [] NONE’, ‘t with clock := k2’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call Tail (Label start) []’, ‘s with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call Tail (Label start) []’, ‘s with clock := k2’, ‘p’] mp_tac) >>
   fs []) >>
  simp [equiv_lprefix_chain_thm] >>
  fs [Abbr ‘l1’, Abbr ‘l2’]  >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac
  >- (
   qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
   Cases_on`p` >> pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
   drule ocompile_correct >> fs [] >>
   ‘q ≠ SOME Error ∧
    q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
     last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   disch_then (qspecl_then [‘t with clock := k’, ‘LN’, ‘nctxt’] mp_tac) >>
   impl_tac
   >- (
    fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def] >>
    fs [locals_rel_def, distinct_vars_def, ctxt_max_def]) >>
   strip_tac >> fs [] >>
   qexists_tac ‘ck+k’ >> simp[] >>
   fs [ocompile_def, compile_def] >>
   fs [compile_exp_def] >>
   fs [gen_temps_def, MAP2_DEF] >>
   fs [nested_seq_def] >>
   ‘find_lab nctxt start = lc’ by (
     fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
   fs [] >>
   drule make_funcs_domain_compile_prog >>
   strip_tac >>
   fs [] >>
   fs [loop_liveTheory.optimise_def] >>
   fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
   fs [loop_liveTheory.shrink_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   fs [loop_liveTheory.mark_all_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rveq >> gs [] >>
   cases_on ‘t1' ∧ t1''’ >>
   gs []
   >- (
    qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def] >> rveq >>
    ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
      fs [evaluate_def] >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
    rveq >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def, LET_THM] >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck’ kall_tac) >>
    first_x_assum (qspec_then ‘ck+k’ mp_tac) >>
    fs [] >>
    strip_tac >>
    cases_on ‘res''’ >> fs [] >> rveq >> fs [] >>
    TRY (cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
    fs [state_rel_def])
   >- (
      cases_on ‘t1''’ >> fs []
      >- (
        qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        fs [] >>
        pairarg_tac >> fs [] >>
        pairarg_tac >> fs [] >>
        pairarg_tac >> fs [] >>
        rewrite_tac [Once loopSemTheory.evaluate_def] >>
        strip_tac >>
        fs [loop_liveTheory.shrink_def,
            lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
        rveq >> fs [lookup_def] >>  rveq >> fs [] >>
        gs [loop_liveTheory.mark_all_def]) >>
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
   qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   rewrite_tac [Once loopSemTheory.evaluate_def] >>
   strip_tac >>
   fs [loop_liveTheory.shrink_def,
       lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
   rveq >> fs [lookup_def] >>  rveq >> fs [] >>
   gs [loop_liveTheory.mark_all_def]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k:num``}]
                                        (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule ocompile_correct >> fs [] >>
  ‘q ≠ SOME Error ∧
   q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
    last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
  fs [] >>
  disch_then (qspecl_then [‘t with clock := k’, ‘LN’, ‘nctxt’] mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def] >>
   fs [locals_rel_def, distinct_vars_def, ctxt_max_def]) >>
  strip_tac >> fs [] >>
  fs [ocompile_def, compile_def] >>
  fs [compile_exp_def] >>
  fs [gen_temps_def, MAP2_DEF] >>
  fs [nested_seq_def] >>
  ‘find_lab nctxt start = lc’ by (
    fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
  fs [] >>
  drule make_funcs_domain_compile_prog >>
  strip_tac >>
  fs [] >>
  fs [loop_liveTheory.optimise_def] >>
  fs [loop_callTheory.comp_def, loop_liveTheory.comp_def] >>
  fs [loop_liveTheory.shrink_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  rveq >> fs [] >>
  fs [loop_liveTheory.mark_all_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  rveq >> gs [] >>
  cases_on ‘t1' ∧ t1''’ >>
  gs []
  >- (
  qpat_x_assum ‘loopSem$evaluate (Mark _, _) = (_,_)’ mp_tac >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  strip_tac >>
  fs [loop_liveTheory.shrink_def,
      lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
  rveq >> fs [lookup_def] >>  rveq >> fs [] >>
  gs [loop_liveTheory.mark_all_def] >> rveq >>
  ‘res = NONE ∧ s1 = t with clock := ck + k ∧ res' = NONE ∧ s1' = s1’ by
    fs [evaluate_def] >>
  qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
  qpat_x_assum ‘evaluate(Mark Skip, _) = _’ kall_tac >>
  rveq >> fs [] >>
  strip_tac >>
  assume_tac (INST_TYPE [``:'a``|->``:'a``,
                         ``:'b``|->``:'b``]
              loopPropsTheory.evaluate_add_clock_io_events_mono) >>
  first_x_assum (qspecl_then
                 [‘Call NONE (SOME (find_lab nctxt start)) [] NONE’,
                  ‘t with clock := k’, ‘ck’] mp_tac) >>
  strip_tac >> rfs [] >>
  qexists_tac ‘k’ >>
  cases_on ‘q’ >> fs [] >>
  cases_on ‘x’ >> fs [] >> rveq >> fs []
  >- (
    qpat_x_assum ‘_ = (_,t1)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def, LET_THM] >>
    TOP_CASE_TAC >>  fs [] >> strip_tac >> rveq >> fs [] >> rveq >>
    fs [state_rel_def, IS_PREFIX_THM])
  >- (
    qpat_x_assum ‘_ = (_,t1)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def, LET_THM] >>
    TOP_CASE_TAC >>  fs [] >> strip_tac >> rveq >> fs [] >> rveq >>
    fs [state_rel_def, IS_PREFIX_THM])
  >- (
    qpat_x_assum ‘_ = (_,t1)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def, LET_THM] >>
    TOP_CASE_TAC >>  fs [] >> strip_tac >> rveq >> fs [] >> rveq >>
    fs [state_rel_def, IS_PREFIX_THM]) >>
  qpat_x_assum ‘_ = (_,t1)’ mp_tac >>
  rewrite_tac [Once loopSemTheory.evaluate_def, LET_THM] >>
  TOP_CASE_TAC >>  fs [] >> strip_tac >> rveq >> fs [] >> rveq >>
  fs [state_rel_def, IS_PREFIX_THM])
  >- (
    cases_on ‘t1''’ >> fs []
    >- (
      qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      pairarg_tac >> fs [] >>
      rewrite_tac [Once loopSemTheory.evaluate_def] >>
      strip_tac >>
      fs [loop_liveTheory.shrink_def,
          lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
      rveq >> fs [lookup_def] >>  rveq >> fs [] >>
      gs [loop_liveTheory.mark_all_def]) >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >>
    rewrite_tac [Once loopSemTheory.evaluate_def] >>
    strip_tac >>
    fs [loop_liveTheory.shrink_def,
        lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
    rveq >> fs [lookup_def] >>  rveq >> fs [] >>
    gs [loop_liveTheory.mark_all_def]) >>
  qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  fs [] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  rewrite_tac [Once loopSemTheory.evaluate_def] >>
  strip_tac >>
  fs [loop_liveTheory.shrink_def,
      lookup_insert, lookup_def, fromAList_def, loop_liveTheory.vars_of_exp_def] >>
  rveq >> fs [lookup_def] >>  rveq >> fs [] >>
  gs [loop_liveTheory.mark_all_def]
QED

(* first_name offset *)

Theorem crep_to_loop_compile_prog_lab_min:
  crep_to_loop$compile_prog cprog = lprog ⇒
  EVERY (λprog. 60 ≤ FST prog) lprog
Proof
  gs[crep_to_loopTheory.compile_prog_def]>>
  gs[MAP2_MAP, EVERY_MEM]>>
  rpt strip_tac>>gvs[MEM_MAP,MEM_ZIP]>>
  pairarg_tac>>gs[crep_to_loopTheory.first_name_def]
QED

val _ = export_theory();
