(*
  Correctness proof for ---
*)

open preamble
     crepSemTheory crepPropsTheory
     loopLangTheory loopSemTheory loopPropsTheory
     pan_commonTheory pan_commonPropsTheory
     listRangeTheory rich_listTheory crep_to_loopTheory


val _ = new_theory "crep_to_loopProof";

val evaluate_nested_seq_append_first =
      evaluate_nested_seq_cases |> CONJUNCT1
val evaluate_none_nested_seq_append =
      evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT1
val evaluate_not_none_nested_seq_append =
      evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT2

(* state relation *)

val s = ``(s:('a,'ffi) crepSem$state)``

(* any built-in list const? *)
Definition equivs_def:
  equivs xs ys = !n. MEM n xs <=> MEM n ys
End

Definition state_rel_def:
  state_rel (s:('a,'ffi) crepSem$state) (t:('a,'ffi) loopSem$state) <=>
   s.memaddrs = t.mdomain ∧
   s.clock = t.clock ∧
   s.be = t.be ∧
   s.ffi = t.ffi
End

(*
  Loc encodes label of a function, e.g:
  Loc n1 n2 represents the label n2
  inside the function n1
*)

Definition wlab_wloc_def:
  (wlab_wloc _ (Word w) = Word w) /\
  (wlab_wloc ctxt (Label fname) =
   case FLOOKUP ctxt.funcs fname of
    | SOME (n, _) =>  Loc n 0
    | NONE =>  Loc 0 0)  (* impossible *)
End

Definition mem_rel_def:
  mem_rel ctxt smem tmem <=>
  !ad. wlab_wloc ctxt (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
End

Definition globals_rel_def:
  globals_rel ctxt sglobals tglobals <=>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc ctxt v) /\
     !f. v = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
End

Definition distinct_funcs_def:
  distinct_funcs fm <=>
    !x y n m rm rm'. FLOOKUP fm x = SOME (n, rm) /\
       FLOOKUP fm y = SOME (m, rm') /\ n = m ==> x = y
End

(* could have been stated differently *)
Definition ctxt_fc_def:
  ctxt_fc cvs ns args es =
    <|vars := FEMPTY |++ ZIP (ns, args);
      funcs := cvs;
      vmax := list_max args;
      ceids := es |>
End

Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
   distinct_funcs ctxt.funcs /\
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc len. FLOOKUP ctxt.funcs f = SOME (loc, len) /\
       LENGTH ns = len /\
       let args = GENLIST I len;
           nctxt = ctxt_fc ctxt.funcs ns args ctxt.ceids in
       lookup loc t_code =
          SOME (args,
                compile nctxt (list_to_num_set args) prog)
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
    lookup n t_locals = SOME (wlab_wloc ctxt v) /\
    !f. v = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ mem_rel ctxt s.memory t.memory ∧
      equivs s.eids ctxt.ceids /\
      globals_rel ctxt s.globals t.globals ∧
      code_rel ctxt s.code t.code ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃ck res1 t1. evaluate (compile ctxt l prog,
                             t with clock := t.clock + ck) = (res1,t1) /\
      state_rel s1 t1 ∧ mem_rel ctxt s1.memory t1.memory ∧
      equivs s1.eids ctxt.ceids /\
      globals_rel ctxt s1.globals t1.globals ∧
      code_rel ctxt s1.code t1.code ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt l s1.locals t1.locals

       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt l s1.locals t1.locals
        | SOME Continue => res1 = SOME Continue /\
                           locals_rel ctxt l s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt v)) /\
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
  s.ffi = t.ffi
Proof
  rw [state_rel_def]
QED

Theorem locals_rel_intro:
  locals_rel ctxt l (s_locals:num |-> 'a word_lab) t_locals ==>
   distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
   ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc ctxt v) /\
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
           nctxt = ctxt_fc ctxt.funcs ns args ctxt.ceids in
       lookup loc t_code =
          SOME (args,
                compile nctxt (list_to_num_set args) prog)
Proof
  rw [code_rel_def]
QED

Theorem mem_rel_intro:
  mem_rel ctxt smem tmem ==>
   !ad. wlab_wloc ctxt (smem ad) = tmem ad /\
    !f. smem ad = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
Proof
  rw [mem_rel_def] >>
  metis_tac []
QED

Theorem globals_rel_intro:
  globals_rel ctxt sglobals tglobals ==>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc ctxt v) /\
     !f. v = Label f ==>
      ?n m. FLOOKUP ctxt.funcs f = SOME (n, m)
Proof
  rw [globals_rel_def] >> metis_tac []
QED

Triviality state_rel_clock_add_zero:
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
  !nb ctxt sm tm w dm be.
   mem_rel ctxt sm tm ==>
   mem_rel ctxt (write_bytearray w nb sm dm be)
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


Triviality evaluate_comb_seq:
  !p s t q r.
    evaluate (p,s) = (NONE, t) /\ evaluate (q,t) = (NONE,r) ==>
    evaluate (Seq p q,s) = (NONE,r)
Proof
  fs [evaluate_def]
QED


Theorem compile_exp_out_rel_cases:
  (!(ct: 'a context) tmp l (e:'a crepLang$exp) p le ntmp nl.
    compile_exp ct tmp l e = (p,le,ntmp, nl) ==>
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p)) /\
  (!(ct: 'a context) tmp l (e:'a crepLang$exp list) p le ntmp nl.
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

val compile_exp_out_rel = compile_exp_out_rel_cases |> CONJUNCT1
val compile_exps_out_rel = compile_exp_out_rel_cases |> CONJUNCT2


Theorem comp_exp_assigned_vars_tmp_bound_cases:
  (!(ct: 'a context) tmp l (e :α crepLang$exp) p le ntmp nl n.
    compile_exp ct tmp l e = (p,le,ntmp,nl) /\ MEM n (assigned_vars (nested_seq p)) ==>
      tmp <= n /\ n < ntmp) /\
  (!(ct: 'a context) tmp l (e :α crepLang$exp list) p le ntmp nl n.
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

val comp_exp_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT1
val comp_exps_assigned_vars_tmp_bound = comp_exp_assigned_vars_tmp_bound_cases |> CONJUNCT2

Theorem compile_exp_le_tmp_domain_cases:
  (!(ct: 'a context) tmp l (e:'a crepLang$exp) p le tmp' l' n.
    ctxt_max ct.vmax ct.vars /\
    compile_exp ct tmp l e = (p,le,tmp', l') /\ ct.vmax < tmp /\
    (!n. MEM n (var_cexp e) ==> ?m. FLOOKUP ct.vars n = SOME m /\ m ∈ domain l) /\
    MEM n (locals_touched le) ==> n < tmp' /\ n ∈ domain l') /\
  (!(ct: 'a context) tmp l (es:'a crepLang$exp list) p les tmp' l' n.
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

val compile_exp_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT1
val compile_exps_le_tmp_domain = compile_exp_le_tmp_domain_cases |> CONJUNCT2

Theorem comp_exp_preserves_eval:
  ∀s e v (t :('a, 'b) state) (ctxt: 'a context) tmp l p le ntmp nl.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exp ctxt tmp l e = (p,le, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc ctxt v) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
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
    state_rel s st ∧ mem_rel ctxt s.memory st.memory ∧
    globals_rel ctxt s.globals st.globals ∧
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
  fs [loopSemTheory.eval_def, wlab_wloc_def]) >>
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
   fs [domain_lookup])
QED

Theorem comp_exps_preserves_eval:
  ∀es s vs (t :('a, 'b) state) (ctxt: 'a context) tmp l p les ntmp nl.
  OPT_MMAP (eval s) es = SOME vs /\
  state_rel s t /\ mem_rel ctxt s.memory t.memory /\
  globals_rel ctxt s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exps ctxt tmp l es = (p,les, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     OPT_MMAP (eval st) les = SOME (MAP (wlab_wloc ctxt) vs) /\
     state_rel s st /\ mem_rel ctxt s.memory st.memory /\
     globals_rel ctxt s.globals st.globals /\
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
                          ‘tmp'’, ‘le’, ‘wlab_wloc ctxt h'’, ‘ck’, ‘ck'’] mp_tac) >>
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
  (!(ct: 'a context) tmp l (e:'a crepLang$exp) p le ntmp nl n.
   n ∈ domain l /\
   compile_exp ct tmp l e = (p,le,ntmp,nl) ==>
     survives n (nested_seq p)) /\
  (!(ct: 'a context) tmp l (e:'a crepLang$exp list) p le ntmp nl n.
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


val member_cutset_survives_comp_exp =
     member_cutset_survives_comp_exp_cases |> CONJUNCT1
val member_cutset_survives_comp_exps =
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
  (!(ctxt: 'a context) tmp l (e:'a crepLang$exp) p le ntmp nl n.
    compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
    ctxt_max ctxt.vmax ctxt.vars /\
    (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧ n < tmp ==>
      ~MEM n (assigned_vars (nested_seq p))) /\
  (!(ctxt: 'a context) tmp l (e:'a crepLang$exp list) p le ntmp nl n.
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

val not_mem_assigned_mem_gt_comp_exp =
      not_mem_assigned_mem_gt_comp_exp_cases |> CONJUNCT1
val not_mem_assigned_mem_gt_comp_exps =
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
   TOP_CASE_TAC >> fs [] >>
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
  ‘eval (st' with locals := insert stmp (wlab_wloc ctxt w) st'.locals) dle =
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
                [‘st' with locals := insert tmp (wlab_wloc ctxt value) st'.locals’,
                 ‘ctxt with <|vars := ctxt.vars |+ (v,tmp); vmax := tmp|>’,
                 ‘insert tmp () l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- fs [state_rel_def] >>
   imp_res_tac compile_exp_out_rel >>
   conj_tac
   >- (
    rw [mem_rel_def] >>
    drule mem_rel_intro >>
    disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
    cases_on ‘s.memory ad’ >> fs [wlab_wloc_def] >>
    FULL_CASE_TAC >> rfs []) >>
   conj_tac
   >- (
    rw [globals_rel_def] >>
    drule globals_rel_intro >>
    disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
    res_tac >> fs [] >>
    cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
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
  conj_tac
  >- (
   rw [mem_rel_def] >>
   drule mem_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   cases_on ‘st.memory ad’ >> fs [wlab_wloc_def]) >>
  conj_tac
  >- (
   rw [globals_rel_def] >>
   drule globals_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   res_tac >> fs [] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
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
    disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt pv’] mp_tac) >>
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
  cases_on ‘x’ >> fs [] >> rveq >>
  TRY (
  conj_tac >- fs [state_rel_def] >>
  conj_tac
  >- (
   rw [mem_rel_def] >>
   drule mem_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   cases_on ‘st.memory ad’ >> fs [wlab_wloc_def]) >>
  conj_tac
  >- (
   rw [globals_rel_def] >>
   drule globals_rel_intro >>
   disch_then (qspec_then ‘ad’ assume_tac) >> fs [] >>
   res_tac >> fs [] >>
   cases_on ‘v'’ >> fs [wlab_wloc_def]) >>
  fs [code_rel_def]) >>
  TRY (
  cases_on ‘w’ >> fs [wlab_wloc_def] >> NO_TAC) >> (
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
   disch_then (qspecl_then [‘pn’,‘wlab_wloc ctxt pv’] mp_tac) >>
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
  !ns lns args s st (ctxt: 'a context) nl fname argexps prog loc.
   ALL_DISTINCT ns /\ ALL_DISTINCT lns /\
   LENGTH ns = LENGTH lns /\
   LENGTH args = LENGTH lns /\
   state_rel s st /\
   equivs s.eids ctxt.ceids /\
   mem_rel ctxt s.memory st.memory /\
   globals_rel ctxt s.globals st.globals /\
   code_rel ctxt s.code st.code /\
   locals_rel ctxt nl s.locals st.locals /\
   FLOOKUP s.code fname = SOME (ns,prog) /\
   FLOOKUP ctxt.funcs fname = SOME (loc,LENGTH lns) /\
   MAP (eval s) argexps = MAP SOME args ==>
   let nctxt = ctxt_fc ctxt.funcs ns lns ctxt.ceids in
        state_rel
          (s with
           <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock − 1|>)
          (st with
           <|locals :=
               fromAList
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])));
             clock := st.clock − 1|>) ∧
        mem_rel nctxt s.memory st.memory ∧
        equivs s.eids nctxt.ceids /\ (* trivially true *)
        globals_rel nctxt s.globals st.globals ∧
        code_rel nctxt s.code st.code ∧
        locals_rel nctxt (list_to_num_set lns)
          (FEMPTY |++ ZIP (ns,args))
          (fromAList
             (ZIP (lns,FRONT (MAP (wlab_wloc ctxt) args ++ [Loc loc 0]))))
Proof
  rw [] >>
  fs [ctxt_fc_def]
  >- fs [state_rel_def]
  >- (
   fs [mem_rel_def] >> rw [] >> fs [] >>
   res_tac >> fs [] >>
   first_x_assum (qspec_then ‘ad’ assume_tac) >>
   cases_on ‘st.memory ad’ >>
   cases_on ‘s.memory ad’ >>
   fs [wlab_wloc_def]
   >- fs [AllCaseEqs ()] >>
   fs [])
  >- (
   fs [globals_rel_def] >>
   rpt gen_tac >>
   first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
   cases_on ‘v’ >>
   fs [wlab_wloc_def])
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
  ‘FRONT (MAP (wlab_wloc ctxt) args ++ [Loc loc 0]) =
   MAP (wlab_wloc ctxt) args’ by (
    cases_on ‘[Loc loc 0]’ >- fs [] >>
    rewrite_tac  [FRONT_APPEND, FRONT_DEF] >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  conj_tac
  >- (
   fs [domain_fromAList] >>
   ‘LENGTH lns = LENGTH (MAP (wlab_wloc ctxt) args)’ by
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
  ‘lookup (EL n lns) (fromAList (ZIP (lns,MAP (wlab_wloc ctxt) args))) =
   SOME (EL n (MAP (wlab_wloc ctxt) args))’ by (
    fs [lookup_fromAList] >>
    ‘n < LENGTH (ZIP (lns,MAP (wlab_wloc ctxt) args))’ by
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
  disch_then (qspec_then ‘wlab_wloc ctxt’ assume_tac) >>
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
   qpat_x_assum ‘mem_rel ctxt s.memory t.memory’ assume_tac >>
   drule mem_rel_intro >>
   strip_tac >> fs [] >>
   res_tac >> rfs []) >>
  qpat_x_assum ‘globals_rel ctxt s.globals st.globals’ assume_tac >>
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
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt) args ++ [Loc loc 0]))))’,
     ‘(ctxt_fc ctxt.funcs ns lns ctxt.ceids)’, ‘list_to_num_set lns’] mp_tac) >>
    impl_tac
    >- (
     fs [crepSemTheory.dec_clock_def, dec_clock_def] >>
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
      (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
    conj_tac
    >- (
     cases_on ‘w’ >>
     fs [wlab_wloc_def, ctxt_fc_def])) >>
    TRY (
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    conj_tac >- fs [state_rel_def] >>
    conj_tac
    >- (
     fs [mem_rel_def] >> rw [] >> fs [] >>
     res_tac >> rfs [] >>
     first_x_assum (qspec_then ‘ad’ assume_tac) >>
     cases_on ‘s1'.memory ad’ >>
     cases_on ‘r.memory ad’ >>
     fs [wlab_wloc_def]) >>
    conj_tac
    >- (
     fs [globals_rel_def] >>
     rpt gen_tac >>
     first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
     cases_on ‘v’ >>
     fs [wlab_wloc_def]) >>
    fs [code_rel_def])) >>
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
    MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
      (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
   fs [state_rel_def]

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
    MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
      (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
   fs [state_rel_def]


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
    MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
      (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
     SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
   conj_tac >- fs [ctxt_fc_def] >>
   conj_tac
   >- (
    qpat_x_assum ‘globals_rel _ r.globals s1.globals’ assume_tac >>
    fs [globals_rel_def, ctxt_fc_def] >>
    rw [] >>
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    TRY (cases_on ‘v’) >>
    rfs [wlab_wloc_def]) >>
   fs [code_rel_def, ctxt_fc_def]


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
   MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
    (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
   SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
   LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
  fs [code_rel_def, ctxt_fc_def]


Theorem compile_Call:
  ^(get_goal "compile _ _ (crepLang$Call _ _ _)")
Proof
  rw [] >>
  cases_on ‘caltyp’ >> fs []
  (* Tail case *)
  >- tail_case_tac >>
  (* Return case *)
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
                 (ZIP (lns,FRONT (MAP (wlab_wloc ctxt) args ++ [Loc loc 0]))))’,
     ‘(ctxt_fc ctxt.funcs ns lns ctxt.ceids)’, ‘list_to_num_set lns’] mp_tac) >>
  impl_tac
  >- (
   fs [crepSemTheory.dec_clock_def, dec_clock_def] >>
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
                   (wlab_wloc (ctxt_fc ctxt.funcs ns lns ctxt.ceids) w)
                   (inter (alist_insert (gen_temps tmp (LENGTH les))
                           (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])
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
    fs [mem_rel_def] >> rw [] >> fs [] >>
    res_tac >> fs [] >>
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    cases_on ‘r.memory ad’ >>
    cases_on ‘t1.memory ad’ >>
    fs [wlab_wloc_def, AllCaseEqs()] >>
    rveq >> fs []) >>
   conj_tac
   >- (
    FULL_CASE_TAC >> fs [] >> rveq >> fs [] >>
    fs [globals_rel_def] >>
    rpt gen_tac >>
    first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
    cases_on ‘v’ >>
    fs [wlab_wloc_def]) >>
   conj_tac
   >- (
    FULL_CASE_TAC >> fs [] >> rveq >> fs [] >>
    fs [code_rel_def]) >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [domain_inter] >>
    ‘LENGTH (gen_temps tmp (LENGTH les)) =
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
              MAP (wlab_wloc ctxt) args ++ [Loc loc 0])) nn = NONE’ by (
     fs [Abbr ‘rn’, ALOOKUP_NONE] >>
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    fs [] >> pop_assum kall_tac >>
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
    MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
   fs [] >> pop_assum kall_tac >>
   rfs [set_var_def] >>
   qmatch_asmsub_rename_tac ‘rx ≠ Error’ >>
   cases_on ‘rx’ >> fs [] >> rveq >> fs [] >>
   fs [cut_res_def, cut_state_def] >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   fs [code_rel_def] >>
   imp_res_tac mem_rel_ctxt_vmax_preserve >>
   imp_res_tac globals_rel_ctxt_vmax_preserve >>
   fs []))
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    disch_then (qspec_then ‘1’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    rfs [] >>
    fs [evaluate_def, cut_res_def] >>
    strip_tac >> fs [] >> rveq >>
    fs [call_env_def] >>
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    conj_tac >- fs [state_rel_def] >>
    conj_tac
    >- (
     fs [mem_rel_def] >> rw [] >> fs [] >>
     res_tac >> rfs [] >>
     TRY (qpat_x_assum ‘∀n. _ ⇔ MEM _ ctxt.ceids’ kall_tac) >>
     first_x_assum (qspec_then ‘ad’ assume_tac) >>
     cases_on ‘t1.memory ad’ >>
     cases_on ‘r.memory ad’ >>
     fs [wlab_wloc_def]) >>
    conj_tac
    >- (
     fs [globals_rel_def] >>
     rpt gen_tac >>
     first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
     cases_on ‘v’ >>
     fs [wlab_wloc_def]) >>
    fs [code_rel_def]) >>
   (* SOME case of excp handler *)
   cases_on ‘v3’ >> fs [] >>
   reverse (cases_on ‘MEM c' s.eids’) >> fs []
   >- (
    (* absent eid *)
    fs [Abbr ‘lns’, equivs_def] >>
    rfs [] >>
    qexists_tac ‘ck + ck'’ >>
    qpat_x_assum ‘ evaluate (_,_) = (NONE,st)’ assume_tac >>
    drule evaluate_add_clock_eq >>
    fs [] >>
    disch_then (qspec_then ‘ck'’ assume_tac) >>
    drule evaluate_none_nested_seq_append >>
    disch_then (qspec_then ‘ptmp ++ pcal’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    ‘MAP (eval st) les =
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    disch_then (qspec_then ‘1’ assume_tac) >>
    fs [] >> pop_assum kall_tac >>
    rfs [] >>
    fs [evaluate_def, cut_res_def] >>
    strip_tac >> fs [] >> rveq >>
    fs [call_env_def] >>
    fs [crepSemTheory.empty_locals_def, ctxt_fc_def] >>
    conj_tac >- fs [state_rel_def] >>
    conj_tac
    >- (
     fs [mem_rel_def] >> rw [] >> fs [] >>
     res_tac >> rfs [] >>
     TRY (qpat_x_assum ‘∀n. _ ⇔ MEM _ ctxt.ceids’ kall_tac) >>
     first_x_assum (qspec_then ‘ad’ assume_tac) >>
     cases_on ‘t1.memory ad’ >>
     cases_on ‘r.memory ad’ >>
     fs [wlab_wloc_def]) >>
    conj_tac
    >- (
     fs [globals_rel_def] >>
     rpt gen_tac >>
     first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
     cases_on ‘v’ >>
     fs [wlab_wloc_def]) >>
    fs [code_rel_def]) >>
   fs [Abbr ‘lns’]
   ‘MEM c' ctxt.ceids’ by metis_tac [equivs_def] >>
   fs [] >>
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    conj_tac >- fs [state_rel_def] >>
    conj_tac
    >- (
     fs [mem_rel_def] >> rw [] >> fs [] >>
     res_tac >> rfs [] >>
     TRY (qpat_x_assum ‘∀n. _ ⇔ MEM _ ctxt.ceids’ kall_tac) >>
     first_x_assum (qspec_then ‘ad’ assume_tac) >>
     cases_on ‘t1.memory ad’ >>
     cases_on ‘r.memory ad’ >>
     fs [wlab_wloc_def]) >>
    conj_tac
    >- (
     fs [globals_rel_def] >>
     rpt gen_tac >>
     first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
     cases_on ‘v’ >>
     fs [wlab_wloc_def]) >>
    fs [code_rel_def]) >>
   (* handling exception *)
   last_x_assum (qspecl_then
                 [‘t1 with locals :=
                   insert (ctxt.vmax + 1) (Word c')
                   (inter (alist_insert (gen_temps tmp (LENGTH les))
                           (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])
                           st.locals) l)’,
                  ‘ctxt’, ‘l’] mp_tac) >>
   impl_tac
   >- (
   fs [crepSemTheory.set_var_def, ctxt_fc_def] >>
   conj_tac >- fs [state_rel_def] >>
   conj_tac
   >- (
    fs [mem_rel_def] >> rw [] >> fs [] >>
    res_tac >> fs [] >>
    first_x_assum (qspec_then ‘ad’ assume_tac) >>
    cases_on ‘r.memory ad’ >>
    cases_on ‘t1.memory ad’ >>
    fs [wlab_wloc_def]) >>
   conj_tac
   >- (
    fs [globals_rel_def] >>
    rpt gen_tac >>
    first_x_assum (qspecl_then [‘ad’, ‘v’] assume_tac) >>
    cases_on ‘v’ >>
    fs [wlab_wloc_def]) >>
   conj_tac >- fs [code_rel_def] >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [domain_inter] >>
    ‘LENGTH (gen_temps tmp (LENGTH les)) =
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
              MAP (wlab_wloc ctxt) args ++ [Loc loc 0])) nn = NONE’ by (
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
     LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
    fs [] >> pop_assum kall_tac >>
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
     MAP SOME (MAP (wlab_wloc ctxt) (args ++ [Label fname]))’ by fs [] >>
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
     (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)]) st.locals) =
    SOME (MAP (wlab_wloc ctxt) args ++ [wlab_wloc ctxt (Label fname)])’ by (
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
    LENGTH (MAP (wlab_wloc ctxt) args ++ [Loc loc 0])’ by (
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
   fs [] >> pop_assum kall_tac >>
   rfs [] >>
   fs [evaluate_def] >>
   fs [get_var_imm_def, asmTheory.word_cmp_def] >>
   fs [evaluate_def, dec_clock_def] >>
   fs [cut_res_def] >>
   strip_tac >> fs [] >> rveq >> fs [])) >>
   fcalled_timed_out_tac
QED


Theorem compile_correct:
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


Theorem flookup_make_fmap_not_elem:
  !xs fm x n. ~MEM x xs ==>
   FLOOKUP (make_fmap n xs fm) x = FLOOKUP fm x
Proof
  Induct >>
  rw []
  >- fs [make_fmap_def, FLOOKUP_UPDATE] >>
  fs [make_fmap_def] >>
  fs [FLOOKUP_UPDATE]
QED

Theorem make_fmap_el_value:
  !xs n fm m.
    n < LENGTH xs /\ ALL_DISTINCT xs  ==>
      FLOOKUP (make_fmap m xs fm) (EL n xs) = SOME (m+n)
Proof
  Induct >>
  rw [] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [make_fmap_def] >>
   metis_tac [flookup_make_fmap_not_elem, FLOOKUP_UPDATE]) >>
  fs [make_fmap_def]
QED

Theorem distinct_make_func_fmap:
  distinct_funcs (make_func_fmap crep_code)
Proof
  rw [distinct_funcs_def] >>
  fs [make_func_fmap_def] >>
  qmatch_asmsub_abbrev_tac ‘MAP2 _ (GENLIST _ _) ps’ >>
  dxrule ALOOKUP_MEM >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  strip_tac >>
  fs [MEM_EL] >>
  ‘n < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST I (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP] >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num list”,
                     “:'c” |-> “:'a # num # num list”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST I (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP]  >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num list”,
                     “:'c” |-> “:'a # num # num list”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs [] >>
  ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  drule (INST_TYPE [“:'a”|->“:'num”,
                     “:'b”|->“:num list”,
                     “:'c” |-> “:'num # num list”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  dxrule (INST_TYPE [“:'a”|->“:'num”,
                     “:'b”|->“:num list”,
                     “:'c” |-> “:num # num list”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs []
QED


Theorem sublist_el_eqs:
  !n xs ys.
   n < LENGTH xs /\
   (!x. MEM x xs ==> MEM x ys) ==>
  ?m. m < LENGTH ys /\ EL n xs = EL m ys
Proof
  rw [] >>
  fs [MEM_EL] >>
  last_x_assum (qspec_then ‘EL n xs’ mp_tac) >>
  impl_tac >- metis_tac [] >>
  fs []
QED

Theorem mem_lookup_tonumset_some:
  !xs x.
    MEM x xs ==> lookup x (toNumSet xs) = SOME ()
Proof
  Induct >>
  rw [] >> fs [] >>
  fs [toNumSet_def] >>
  fs [lookup_insert]
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

Definition mk_ctxt_code_def:
  mk_ctxt_code params crep_code =
     mk_ctxt params
             (make_vmap params crep_code)
             (make_vmax params crep_code)
             (make_func_fmap crep_code)
             (get_eids crep_code)
End

Theorem map2_fst:
  !l l' f. LENGTH l = LENGTH l' ==>
   MAP FST (list$MAP2 (λx y. (x, f y)) l l') = l
Proof
  Induct_on ‘l’ >>
  rw [] >>
  fs [] >>
  cases_on ‘l'’ >> fs []
QED

Theorem map_map2_fst:
  !xs ys zs f e. LENGTH xs = LENGTH ys ∧  LENGTH xs = LENGTH zs ==>
   MAP FST (MAP2
            (λ(x,y) (n,p,b). (x,y,f p b e))
            (MAP2 (λx y. (x,y)) xs ys) zs) = xs
Proof
  Induct_on ‘xs’ >>
  rw [] >>
  fs [] >>
  cases_on ‘ys’ >> cases_on ‘zs’ >> fs [] >>
  cases_on ‘h''’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem mk_ctxt_code_imp_code_rel:
  ALL_DISTINCT (MAP FST crep_code) /\
  list$EVERY ALL_DISTINCT (MAP FST (MAP SND crep_code)) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  code_rel (mk_ctxt_code [] crep_code)
           (alist_to_fmap crep_code)
           (fromAList (crep_to_loop$compile_prog crep_code))
Proof
  rw [code_rel_def, mk_ctxt_code_def]
  >- fs [mk_ctxt_def, distinct_make_func_fmap] >>
  fs [mk_ctxt_def, make_func_fmap_def] >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  fs [MEM_EL] >>
  rveq >>
  qexists_tac ‘n’ >>
  qexists_tac ‘MAP (from_fm
                    (make_fmap 0 (prog_vars (MAP SND crep_code))
                     FEMPTY)) ns’ >>
  conj_tac
  >- (
   ho_match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac
   >- (
    qmatch_goalsub_abbrev_tac ‘MAP FST ls’ >>
    ‘MAP FST ls = MAP FST crep_code’ suffices_by fs [] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    rw [] >>
    fs [Abbr ‘ls’] >>
    qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
    ‘n' < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
    drule (INST_TYPE [“:'a”|->“:'mlstring”,
                      “:'b”|->“:'num # num list”,
                      “:'c”|-> “:'mlstring # num # num list”] EL_MAP2) >>
    disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
    strip_tac >> fs [] >>
    match_mp_tac EL_MAP >>
    fs []) >>
   fs [MEM_EL] >>
   qexists_tac ‘n’ >>
   fs [] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:'mlstring”,
                     “:'b”|->“:'num # num list”,
                     “:'c”|-> “:'mlstring # num # num list”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   conj_asm1_tac
   >- (
    fs [EL_MAP] >>
    qpat_x_assum ‘_ = EL n crep_code’ (mp_tac o GSYM) >>
    fs []) >>
   fs [Abbr ‘ps’] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:'num”,
                     “:'b”|->“:'num list”,
                     “:'c”|-> “:'num # num list”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [Abbr ‘ps’] >>
   ‘n < LENGTH (MAP FST (MAP SND crep_code))’ by fs [] >>
   drule (INST_TYPE [“:'a”|->“:'num list”,
                     “:'b”|->“:'num list”] EL_MAP) >>
   disch_then (qspec_then
               ‘(λparams. MAP
                 (from_fm
                  (make_fmap 0 (prog_vars (MAP SND crep_code)) FEMPTY)) params)’
               mp_tac) >>
   strip_tac >>
   fs [] >>
   ‘EL n (MAP FST (MAP SND crep_code)) = ns’ suffices_by fs [] >>
   qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
   ‘n < LENGTH (MAP SND crep_code)’ by fs [] >>
   drule (INST_TYPE [
                     “:'b”|->“:num list”] EL_MAP) >>
   disch_then (qspec_then ‘FST’ mp_tac) >>
   fs [] >>
   strip_tac >>
   ‘EL n (MAP SND crep_code) = SND (EL n crep_code)’ by (
     match_mp_tac EL_MAP >>
     fs []) >>
   fs []) >>
  conj_tac
  >- (
   fs [prog_vars_def] >>
   match_mp_tac ALL_DISTINCT_MAP_INJ >>
   reverse (rw [])
   >- (
    fs [EVERY_MAP, EVERY_EL] >>
    pop_assum (assume_tac o GSYM) >>
    last_x_assum (qspec_then ‘n’ mp_tac) >>
    fs []) >>
   fs [from_fm_def] >>
   qmatch_asmsub_abbrev_tac ‘make_fmap _ xs _’ >>
   ‘ALL_DISTINCT xs’ by (
     fs [Abbr ‘xs’, fromNumSet_def] >>
     metis_tac [ALL_DISTINCT_MAP_FST_toAList]) >>
   fs [MEM_EL] >> rveq >> rfs [] >>
   ‘?m'. m' < LENGTH xs /\ EL n' ns = EL m' xs’ by (
     match_mp_tac sublist_el_eqs >>
     fs [] >> rw [] >>
     fs [Abbr ‘xs’, fromNumSet_def, MEM_MAP, EXISTS_PROD, MEM_toAList] >>
     fs [lookup_union] >>
     qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
     TOP_CASE_TAC >>
     fs [MAP_MAP_o] >>
     match_mp_tac mem_lookup_tonumset_some >>
     fs [MEM_FLAT, MEM_MAP] >>
     qexists_tac ‘ns’ >>
     fs [] >>
     qexists_tac ‘(f,ns,prog)’ >>
     fs [MEM_EL] >> rveq >>
     metis_tac []) >>
   ‘?m''. m'' < LENGTH xs /\ EL n'' ns = EL m'' xs’ by (
     match_mp_tac sublist_el_eqs >>
     fs [] >> rw [] >>
     fs [Abbr ‘xs’, fromNumSet_def, MEM_MAP, EXISTS_PROD, MEM_toAList] >>
     fs [lookup_union] >>
     qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
     TOP_CASE_TAC >>
     fs [MAP_MAP_o] >>
     match_mp_tac mem_lookup_tonumset_some >>
     fs [MEM_FLAT, MEM_MAP] >>
     qexists_tac ‘ns’ >>
     fs [] >>
     qexists_tac ‘(f,ns,prog)’ >>
     fs [MEM_EL] >> rveq >>
     metis_tac []) >>
   fs [] >>
   ‘FLOOKUP (make_fmap 0 xs FEMPTY) (EL m' xs) = SOME (0 + m')’ by (
     match_mp_tac make_fmap_el_value >>
     fs []) >>
   ‘FLOOKUP (make_fmap 0 xs FEMPTY) (EL m'' xs) = SOME (0 + m'')’ by (
     match_mp_tac make_fmap_el_value >>
     fs []) >>
   fs []) >>
  conj_tac >- fs [LENGTH_MAP] >>
  fs [compile_prog_def] >>
  fs [ctxt_fc_def] >>
  match_mp_tac mem_lookup_fromalist_some >>
  conj_tac
  >- (
   qmatch_goalsub_abbrev_tac ‘MAP FST ps’ >>
   ‘MAP FST ps = GENLIST I (LENGTH crep_code)’
   suffices_by fs [ALL_DISTINCT_GENLIST] >>
   fs [Abbr ‘ps’] >>
   match_mp_tac map_map2_fst >>
   fs [LENGTH_MAP, LENGTH_GENLIST]) >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 _ ps _)’ >>
  ‘n < MIN (LENGTH ps) (LENGTH crep_code)’ by fs [Abbr ‘ps’] >>
  drule (INST_TYPE [“:'a”|->“:'num # num list”,
                    “:'b”|->“:'mlstring # num list # 'a crepLang$prog”,
                    “:'c”|-> “:num # num list # 'a prog”] EL_MAP2) >>
  disch_then (qspec_then ‘λ(n,lparams) (name,params,body).
                          (n,lparams,comp_func params body crep_code)’ mp_tac) >>
  strip_tac >> fs [] >>
  qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
  fs [Abbr ‘ps’] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 _ _ ps)’ >>
  ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
  drule (INST_TYPE [“:'a”|->“:'num”,
                    “:'b”|->“:'num list”,
                    “:'c”|-> “:num # num list”] EL_MAP2) >>
  disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
  strip_tac >> fs [] >>
  conj_tac
  >- (
   fs [Abbr ‘ps’] >>
   qmatch_goalsub_abbrev_tac ‘EL n (MAP f' l')’ >>
   ‘EL n (MAP f' l') = f' (EL n l')’ by (
     match_mp_tac EL_MAP >>
     fs [Abbr ‘l'’]) >>
   fs [Abbr ‘f'’, Abbr ‘l'’] >>
   fs [MAP_MAP_o] >>
   ‘EL n (MAP (FST ∘ SND) crep_code) = (FST ∘ SND) (EL n crep_code)’ by (
     match_mp_tac EL_MAP >>
     fs []) >>
   fs []) >>
  fs [comp_func_def] >>
  fs [mk_ctxt_def, make_vmap_def, make_func_fmap_def, get_eids_def]
QED


Definition mk_ctxt_code_def:
  mk_ctxt_code params crep_code =
     mk_ctxt params
             (make_vmap params crep_code)
             (make_vmax params crep_code)
             (make_func_fmap crep_code)
             (get_eids crep_code)
End

Theorem state_rel_imp_semantics:
  s.memaddrs = t.mdomain ∧
  s.be = t.be ∧
  s.ffi = t.ffi /\
  mem_rel (mk_ctxt_code [] crep_code) s.memory t.memory ∧
  equivs s.eids (mk_ctxt_code [] crep_code).ceids ∧
  globals_rel (mk_ctxt_code [] crep_code) s.globals t.globals ∧
  ALL_DISTINCT (MAP FST crep_code) /\
  EVERY ALL_DISTINCT (MAP FST (MAP SND crep_code)) ∧
  s.code = alist_to_fmap crep_code ∧
  t.code = fromAList (crep_to_loop$compile_prog crep_code) ∧
  s.locals = FEMPTY ∧
  ALOOKUP crep_code start = SOME ([],prog) ∧
  FLOOKUP ((mk_ctxt_code [] crep_code).funcs) start = SOME (lc, []) ∧
  semantics s start <> Fail ==>
  semantics t lc = semantics s start
Proof
  rw [] >>
  drule mk_ctxt_code_imp_code_rel >>
  disch_then (qspecl_then [‘start’, ‘prog’] mp_tac) >>
  fs [] >>
  strip_tac >>
  drule code_rel_intro >>
  strip_tac >>
  pop_assum (qspecl_then [‘start’, ‘[]’, ‘prog’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [list_to_num_set_def] >>
  qmatch_asmsub_abbrev_tac ‘compile nctxt _ _’ >>
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
    drule compile_correct >> fs[] >>
    map_every qexists_tac [‘t with clock := k'’] >>
    qexists_tac ‘nctxt’ >>
    qexists_tac ‘LN’ >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
     conj_tac
     >- (
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
     conj_tac
     >- fs [state_rel_def] >>
     conj_tac
     >- (
      fs [Abbr ‘nctxt’] >>
      fs [ctxt_fc_def] >>
      fs [mem_rel_def] >>
      rw []
      >- (
       cases_on ‘s.memory ad’ >> fs []
       >- (
        last_x_assum (qspec_then ‘ad’ mp_tac) >>
        fs [mk_ctxt_def] >>
        fs [wlab_wloc_def]) >>
       last_x_assum (qspec_then ‘ad’ mp_tac) >>
       fs [mk_ctxt_def] >>
       fs [wlab_wloc_def]) >>
      last_x_assum (qspec_then ‘ad’ mp_tac) >>
      fs [mk_ctxt_def]) >>
     conj_tac
     >- fs [Abbr ‘nctxt’, ctxt_fc_def] >>
     conj_tac
     >- (
      fs [Abbr ‘nctxt’, ctxt_fc_def] >>
      fs [globals_rel_def] >>
      rw []
      >- (
       cases_on ‘v’ >> fs []
       >- (
        last_x_assum (qspec_then ‘ad’ mp_tac) >>
        fs [mk_ctxt_def] >>
        fs [wlab_wloc_def]) >>
       last_x_assum (qspec_then ‘ad’ mp_tac) >>
       fs [mk_ctxt_def] >>
       fs [wlab_wloc_def]) >>
      last_x_assum (qspec_then ‘ad’ mp_tac) >>
      fs [mk_ctxt_def]) >>
     conj_tac
     >- (
      fs [Abbr ‘nctxt’, ctxt_fc_def] >>
      fs [code_rel_def]) >>
     fs [Abbr ‘nctxt’, ctxt_fc_def] >>
     fs [locals_rel_def] >>
     fs [distinct_vars_def, list_max_def, ctxt_max_def] >>
     rw [FUPDATE_LIST_THM]) >>
    cases_on ‘evaluate (Call NONE (SOME lc) [] NONE,t with clock := k')’ >>
    fs [] >>
    cases_on ‘q'’ >> fs []
    >- (
    fs [compile_def] >>
    fs [compile_exp_def] >>
    fs [gen_temps_def, MAP2_DEF] >>
    fs [nested_seq_def] >>
    ‘find_lab nctxt start = lc’ by (
      fs [find_lab_def, Abbr ‘nctxt’] >>
      fs [mk_ctxt_def, ctxt_fc_def]) >>
    fs [] >>
    ‘lc ∈ domain (fromAList (compile_prog crep_code))’ by cheat >>
    fs []
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>
    rw [Once loopSemTheory.evaluate_def] >>

    fs [set_var_def] >>
    fs [eval_def] >>
    fs [get_vars_def] >>
    fs [find_code_def] >>
    rw []
    >- (
     fs [find_lab_def] >>
     fs [Abbr ‘nctxt’] >>
     fs [mk_ctxt_def, ctxt_fc_def] >>
     rfs []) >>
    fs [find_lab_def] >>
    fs [Abbr ‘nctxt’] >>
    fs [mk_ctxt_def, ctxt_fc_def] >>
    rfs []
    >- (
     ‘FLOOKUP (make_func_fmap crep_code) start = SOME (lc, [])’ by cheat >>
     fs [] >>
     fs [list_max_def] >>
     cases_on ‘r’ >> fs [] >>
     cases_on ‘x’ >> fs [] >> rveq >> fs [] >>


     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     cases_on ‘k' = 0’ >> fs []
  (* something with the clock *)

     )





    (* casing on the evaluation results of crepLang *)
    cases_on ‘r’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >> fs [] >> (
    cases_on ‘(evaluate (Call NONE (SOME lc) [] NONE,t with clock := k'))’ >>
    fs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    rveq >> fs [] >>
    cases_on ‘q'’ >> fs [] >>
    cases_on ‘x’ >> fs [])) >>
   (* the termination/diverging case of stack semantics *)
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* the termination case of word semantics *)
   >- (
    rw [] >> fs [] >>
    drule0 comp_Call >>
    ‘r <> SOME Error’ by(CCONTR_TAC >> fs[]) >>
    simp[] >>
    drule0 (GEN_ALL state_rel_with_clock) >> simp[] >>
    disch_then (qspec_then ‘k’ mp_tac) >> simp[] >>
    strip_tac >>
    disch_then drule >>
    disch_then (qspec_then ‘ctxt’ mp_tac) >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
    impl_tac
    >- (
     conj_tac
     >- (
      fs [Abbr ‘ctxt’] >>
      match_mp_tac locals_rel_mk_ctxt_ln >>
      fs []) >>
     conj_tac
     >- (
      fs [no_Loops_def, no_Loop_def] >>
      fs [every_prog_def]) >>
     fs [wordSemTheory.isWord_def, loopLangTheory.acc_vars_def]) >>
    fs [comp_def] >>
    strip_tac >>
    drule0 (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    disch_then (qspec_then ‘k'’ mp_tac) >>
    impl_tac
    >- (
     CCONTR_TAC >> fs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
    qpat_x_assum ‘evaluate _ = (r', _)’ assume_tac >>
    drule0 (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    disch_then (qspec_then ‘k’ mp_tac) >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    ntac 2 strip_tac >> fs[] >> rveq >> fs[] >>
    Cases_on ‘r’ >> fs[] >>
    Cases_on ‘r'’ >> fs [] >>
    Cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
    fs [state_rel_def] >>
    ‘t1.ffi = t''.ffi’ by
      fs [wordSemTheory.state_accfupds, wordSemTheory.state_component_equality] >>
    qpat_x_assum ‘t1.ffi = t'.ffi’ (assume_tac o GSYM) >>
    fs []) >>
   (* the diverging case of word semantics *)
   rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
   drule0 comp_Call >>
   ‘r ≠ SOME Error’ by (
     last_x_assum (qspec_then ‘k'’ mp_tac) >> simp[] >>
     rw[] >> strip_tac >> fs[]) >>
   simp [] >>
   map_every qexists_tac [‘t with clock := k’] >>
   drule0 (GEN_ALL state_rel_with_clock) >>
   disch_then(qspec_then ‘k’ strip_assume_tac) >>
   simp [] >>
   qexists_tac ‘ctxt’ >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [Abbr ‘ctxt’] >>
    match_mp_tac locals_rel_mk_ctxt_ln >>
    fs []) >>
   conj_tac
   >- (
    fs [no_Loops_def, no_Loop_def] >>
    fs [every_prog_def]) >>
   conj_tac >- fs [wordSemTheory.isWord_def] >>
   conj_tac >- fs [loopLangTheory.acc_vars_def] >>
   fs [comp_def] >>
   CCONTR_TAC >> fs [] >>
   first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >> simp[] >>
   every_case_tac >> fs[] >> rw[] >> rfs[])


  rw [wordSemTheory.semantics_def]




  fs [] >>
  strip_tac >>
  fs [comp_func_def] >>
  qmatch_asmsub_abbrev_tac ‘comp ctxt _ _’ >>
  reverse (Cases_on ‘semantics s start’) >> fs []




QED



val goal =
  ``λ(prog, s). ∀res s1 t ctxt l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ mem_rel ctxt s.memory t.memory ∧
      equivs s.eids ctxt.ceids /\
      globals_rel ctxt s.globals t.globals ∧
      code_rel ctxt s.code t.code ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃ck res1 t1. evaluate (compile ctxt l prog,
                             t with clock := t.clock + ck) = (res1,t1) /\
      state_rel s1 t1 ∧ mem_rel ctxt s1.memory t1.memory ∧
      equivs s1.eids ctxt.ceids /\
      globals_rel ctxt s1.globals t1.globals ∧
      code_rel ctxt s1.code t1.code ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt l s1.locals t1.locals

       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt l s1.locals t1.locals
        | SOME Continue => res1 = SOME Continue /\
                           locals_rel ctxt l s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt v)) /\
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
Theorem flookup_make_fmap_fempty_update:
  !xs x n m. ~MEM x xs ==>
   FLOOKUP (make_fmap n xs (FEMPTY |+ (x,m))) x = SOME m
Proof
  rw [] >>
  metis_tac [flookup_make_fmap_not_elem, FLOOKUP_UPDATE]
QED

Theorem foo:
  !xs fm  fm' x n.
   FLOOKUP fm x = NONE /\
   FLOOKUP fm' x = NONE /\
   ALL_DISTINCT xs  (* should be true without this assumption *) ==>
   FLOOKUP (make_fmap n xs fm) x =
   FLOOKUP (make_fmap n xs fm') x
Proof
  Induct >>
  rw []
  >- fs [make_fmap_def, FLOOKUP_UPDATE] >>
  fs [make_fmap_def] >>
  cases_on ‘~MEM x xs’
  >- metis_tac [flookup_make_fmap_not_elem, FLOOKUP_UPDATE] >>
  fs [] >>
  reverse (cases_on ‘x = h’) >> fs [] >> rveq >>
  last_x_assum (qspecl_then [‘fm |+ (h,n)’, ‘fm' |+ (h,n)’, ‘x’, ‘n+1’] mp_tac) >>
  impl_tac
  >- fs [FLOOKUP_UPDATE] >>
  fs []
QED

Theorem bar:
  !xs n fm m.
    n < LENGTH xs /\ ALL_DISTINCT xs /\
    FLOOKUP fm (EL n xs) = NONE  ==>
      FLOOKUP (make_fmap m xs fm) (EL n xs) = SOME (m+n)
Proof
  Induct >>
  rw [] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [make_fmap_def] >>
   metis_tac [flookup_make_fmap_not_elem, FLOOKUP_UPDATE]) >>
  fs [make_fmap_def] >>
  last_x_assum (qspecl_then [‘n'’, ‘fm’, ‘m+1’] mp_tac) >>
  fs [] >>
  strip_tac >>
  ‘FLOOKUP (make_fmap (m + 1) xs (fm |+ (h,m))) (EL n' xs) =
   FLOOKUP (make_fmap (m + 1) xs fm) (EL n' xs)’ suffices_by fs [] >>
  match_mp_tac foo >>
  fs [] >>
  fs [FLOOKUP_UPDATE] >>
  metis_tac [MEM_EL]
QED






Theorem bar:
  !x xs. MEM x xs ==>
   FLOOKUP (make_fmap 0 xs FEMPTY) n  =


  ALL_DISTINCT xs /\  ALL_DISTINCT ys ==>
  ALL_DISTINCT
  (MAP (from_fm (make_fmap 0 xs FEMPTY)) ys)
Proof
  rw [] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw [] >>
  fs [from_fm_def] >>




QED

Theorem bar:
  ALL_DISTINCT xs /\  ALL_DISTINCT ys ==>
  ALL_DISTINCT
  (MAP (from_fm (make_fmap 0 xs FEMPTY)) ys)
Proof
  rw [] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw [] >>
  fs [from_fm_def] >>
QED


(*
 code_rel (mk_ctxt ([], prog) crep_code) s.code t.code ∧
*)


val _ = export_theory();
