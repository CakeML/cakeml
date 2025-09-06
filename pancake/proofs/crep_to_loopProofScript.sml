(*
  Correctness proof for ---
*)
Theory crep_to_loopProof
Ancestors
  listRange rich_list crepProps loopProps pan_commonProps
  loop_liveProof crepSem loopLang loopSem pan_common
  crep_arithProof crep_to_loop
Libs
  preamble

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
   s.sh_memaddrs = t.sh_mdomain ∧
   s.clock = t.clock ∧
   s.be = t.be ∧
   s.ffi = t.ffi ∧
   s.base_addr = t.base_addr ∧
   s.top_addr = t.top_addr
End

(*
  Loc encodes label of a function, e.g:
  Loc n1 n2 represents the label n2
  inside the function n1
*)

Definition wlab_wloc_def:
  (wlab_wloc (panSem$Word w) = wordLang$Word w)
End

Definition mem_rel_def:
  mem_rel smem tmem dom <=>
  !ad. ad ∈ dom ⇒ wlab_wloc (smem ad) = tmem ad
End

Definition globals_rel_def:
  globals_rel sglobals tglobals <=>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc v)
End

Definition distinct_funcs_def:
  distinct_funcs fm <=>
    !x y n m rm rm'. FLOOKUP fm x = SOME (n, rm) /\
       FLOOKUP fm y = SOME (m, rm') /\ n = m ==> x = y
End

(* could have been stated differently *)
Definition ctxt_fc_def:
  ctxt_fc c cvs ns args =
    <|vars := FEMPTY |++ ZIP (ns, args);
      funcs := cvs;
      vmax := list_max args;
      target := c
      |>
End

Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
   distinct_funcs ctxt.funcs /\
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc len. FLOOKUP ctxt.funcs f = SOME (loc, len) /\
       LENGTH ns = len /\
       let args = GENLIST I len;
           nctxt = ctxt_fc ctxt.target ctxt.funcs ns args in
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
    lookup n t_locals = SOME (wlab_wloc v)
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ mem_rel s.memory t.memory s.memaddrs ∧
      globals_rel s.globals t.globals ∧
      code_rel ctxt s.code t.code ∧
      locals_rel ctxt l s.locals t.locals ⇒
      ∃ck res1 t1. evaluate (compile ctxt l prog,
                             t with clock := t.clock + ck) = (res1,t1) /\
      state_rel s1 t1 ∧ mem_rel s1.memory t1.memory s1.memaddrs ∧
      globals_rel s1.globals t1.globals ∧
      code_rel ctxt s1.code t1.code ∧
      (res1 = case res of
           NONE => NONE
         | SOME Break => SOME Break
         | SOME Continue => SOME Continue
         | SOME (Return v) => SOME (Result (wlab_wloc v))
         | SOME (Exception eid) => SOME (Exception (Word eid))
         | SOME TimeOut => SOME TimeOut
         | SOME (FinalFFI f) => SOME (FinalFFI f)
         | SOME Error => SOME Error) ∧
      (case res of
       | NONE => locals_rel ctxt l s1.locals t1.locals
       | SOME Break => locals_rel ctxt l s1.locals t1.locals
       | SOME Continue => locals_rel ctxt l s1.locals t1.locals
       | SOME (Return v) => T
       | SOME Error => F
       | _ => T)``

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
  s.sh_memaddrs = t.sh_mdomain ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  s.base_addr = t.base_addr ∧
  s.top_addr = t.top_addr
Proof
  rw [state_rel_def]
QED

Theorem locals_rel_intro:
  locals_rel ctxt l (s_locals:num |-> 'a word_lab) t_locals ==>
   distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\ domain l ⊆ domain t_locals /\
   ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃n. FLOOKUP ctxt.vars vname = SOME n ∧ n ∈ domain l ∧
    lookup n t_locals = SOME (wlab_wloc v)
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
           nctxt = ctxt_fc ctxt.target ctxt.funcs ns args in
       lookup loc t_code =
          SOME (args,
                ocompile nctxt (list_to_num_set args) prog)
Proof
  rw [code_rel_def]
QED

Theorem mem_rel_intro:
  mem_rel smem tmem dm ==>
   !ad. ad ∈ dm ⇒ wlab_wloc (smem ad) = tmem ad
Proof
  rw [mem_rel_def] >>
  metis_tac []
QED

Theorem globals_rel_intro:
  globals_rel sglobals tglobals ==>
   !ad v. FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc v)
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
  !nb sm tm w dm be.
   mem_rel sm tm dm ==>
   mem_rel (write_bytearray w nb sm dm be)
   (write_bytearray w nb tm dm be) dm
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
  disch_then (qspecl_then [‘w+1w’, ‘be’] mp_tac) >>
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

Theorem cut_sets_MAPi_Assign:
  ∀les cs offset.
    cut_sets cs (nested_seq (MAPi (λn. Assign (n + offset)) les)) =
    list_insert (GENLIST ($+ offset) (LENGTH les)) cs
Proof
  Induct_on ‘les’ \\
  rw[nested_seq_def,cut_sets_def,list_insert_def,o_DEF,GENLIST_CONS] \\
  PURE_ONCE_REWRITE_TAC[DECIDE “∀n m. n + SUC m = m + SUC n”] \\
  first_x_assum $ PURE_REWRITE_TAC o single \\
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\
  simp[FUN_EQ_THM]
QED

Theorem assigned_vars_MAPi_Assign:
  ∀les offset.
    assigned_vars (nested_seq (MAPi (λn. loopLang$Assign (n + offset)) les)) =
    GENLIST ($+ offset) (LENGTH les)
Proof
  Induct_on ‘les’ \\
  rw[nested_seq_def,assigned_vars_def,o_DEF,GENLIST_CONS] \\
  PURE_ONCE_REWRITE_TAC[DECIDE “∀n m. n + SUC m = m + SUC n”] \\
  first_x_assum $ PURE_REWRITE_TAC o single \\
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\
  simp[FUN_EQ_THM]
QED

Theorem survives_MAPi_Assign:
  ∀n les offset.
    survives n (nested_seq (MAPi (λn. Assign (n + offset)) les)) = T
Proof
  Induct_on ‘les’ \\
  rw[nested_seq_def,survives_def,o_DEF,GENLIST_CONS] \\
  PURE_ONCE_REWRITE_TAC[DECIDE “∀n m. n + SUC m = m + SUC n”] \\
  first_x_assum $ PURE_REWRITE_TAC o single \\
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\
  simp[FUN_EQ_THM]
QED

Theorem insert_insert_eq:
  insert a b $ insert a b c = insert a b c
Proof
  rw[Once insert_insert]
QED

Theorem list_insert_SNOC:
  ∀y l x.
  list_insert (SNOC x y) l =
  insert x () $ list_insert y l
Proof
  Induct_on ‘y’ \\ rw[list_insert_def]
QED

Theorem compile_exps_alt:
  compile_exps ctxt tmp l [] = ([],[],tmp,l) ∧
  compile_exps ctxt tmp l (e::es) =
  let
    (p,le,tmp',l') = compile_exp ctxt tmp l e;
    (p1,les,tmp'',l'') = compile_exps ctxt tmp' l' es
  in
    (p ++ p1,le::les,tmp'',l'')
Proof
  rw[] \\ rw[Once compile_exp_def]
QED

Theorem list_insert_insert:
  ∀x xs l. insert x () $ list_insert xs l = list_insert xs $ insert x () l
Proof
  Induct_on ‘xs’ \\ rw[list_insert_def] \\
  rename1 ‘insert a () $ insert b () _’ \\
  Cases_on ‘a = b’ \\ rw[insert_shadow,insert_swap]
QED

Theorem list_insert_append:
  ∀xs ys l. list_insert (xs ++ ys) l = list_insert xs $ list_insert ys l
Proof
  Induct \\ rw[list_insert_def,list_insert_insert]
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
  fs [nested_seq_def, comp_syntax_ok_def, cut_sets_def] >> NO_TAC)
  >- (
   rename [‘compile_exp _ _ _ (Load32 e)’] >>
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
    fs [comp_syntax_ok_def])) >>
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
    fs [comp_syntax_ok_def])) >>
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
   rename [‘compile_exp _ _ _ (Crepop _ _)’] >>
   simp [Once compile_exp_def] >>
   pairarg_tac >> fs [] >> rveq >>
   rpt gen_tac >> disch_then strip_assume_tac >>
   Cases_on ‘cop’ >>
   gvs[oneline compile_crepop_def,ELIM_UNCURRY,AllCaseEqs()] >>
   (conj_asm1_tac
    >- (rpt (match_mp_tac comp_syn_ok_nested_seq >> conj_tac) >>
        rw[] >>
        simp[nested_seq_def,comp_syntax_ok_def]
        >- (rpt $ pop_assum kall_tac >>
            rename1 ‘comp_syntax_ok cs’ >>
            qid_spec_tac ‘cs’ >>
            qid_spec_tac ‘tmp'’ >>
            Induct_on ‘les’ >> gvs[nested_seq_def,comp_syntax_ok_def] >>
            simp[o_DEF] >>
            rpt strip_tac >>
            first_x_assum(qspec_then ‘SUC tmp'’ mp_tac) >>
            rename1 ‘comp_syntax_ok css’ >>
            disch_then(qspec_then ‘css’ mp_tac) >>
            qmatch_goalsub_abbrev_tac ‘a1 ⇒ a2’ >>
            ‘a1 = a2’ suffices_by simp[] >>
            unabbrev_all_tac >>
            ntac 2 AP_TERM_TAC >>
            match_mp_tac MAPi_CONG >>
            rw[]) >>
        simp[cut_sets_nested_seq,nested_seq_def,cut_sets_def,cut_sets_MAPi_Assign,
             comp_syntax_ok_def] >>
        simp[insert_swap] >>
        conj_tac >> qexists_tac ‘[]’ >> simp[insert_swap,insert_shadow])) >>
   rw[] >>
   simp[cut_sets_nested_seq,nested_seq_def,cut_sets_def,cut_sets_MAPi_Assign] >>
   simp[insert_insert_eq] >>
   simp[Once insert_insert,SimpR “$=”,insert_insert_eq] >>
   simp[insert_insert_eq,GSYM ADD1,GENLIST,list_insert_SNOC] >>
   simp[insert_swap,insert_shadow] >>
   rw[CONV_RULE (STRIP_QUANT_CONV $ LHS_CONV $ PURE_ONCE_REWRITE_CONV [ADD_SYM]) GENLIST_APPEND] \\
   rw[list_insert_append,list_insert_insert,list_insert_def,insert_swap,ADD1])
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
    fs [comp_syntax_ok_def] >>
    fs [cut_sets_def] >>
    rw [Once comp_syntax_ok_def, list_insert_def] >>
    fs [cut_sets_nested_seq] >>
    qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
    qexists_tac ‘[t1;t2]’ >>
    simp[] >>
    Cases_on ‘t1 = t2’ >> simp[insert_swap,insert_shadow]) >>
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
     fs [cut_sets_nested_seq,comp_syntax_ok_def] >>
     qmatch_goalsub_abbrev_tac ‘insert t2 _ (insert t1 _ cc)’ >>
     qexists_tac ‘[t1;t2]’ >>
     simp[] >>
     Cases_on ‘t1 = t2’ >> simp[insert_swap,insert_shadow]) >>
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
   once_rewrite_tac [compile_exp_def] >> fs [oneline compile_crepop_def] >> strip_tac >>
   PURE_TOP_CASE_TAC >> fs[] >>
   pairarg_tac >> fs [] >>
   ‘tmp <= tmp'’ by metis_tac [compile_exp_out_rel_cases] >>
   rw[] >>
   gvs[assigned_vars_nested_seq_split,nested_seq_def,assigned_vars_def,assigned_vars_MAPi_Assign,
       MEM_GENLIST] >>
   res_tac >>
   DECIDE_TAC
  )
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
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [‘Op bop es’] >-
    (rpt gen_tac >>
     strip_tac >>
     qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
     once_rewrite_tac [compile_exp_def] >>
     strip_tac >> fs [] >>
     pairarg_tac >> fs [] >> rveq >>
     fs [locals_touched_def, crepLangTheory.var_cexp_def, ETA_AX])
  >~ [‘Crepop bop es’] >-
    (rpt gen_tac >>
     strip_tac >>
     qpat_x_assum ‘compile_exp _ _ _ _ = _’ mp_tac >>
     once_rewrite_tac [compile_exp_def] >>
     strip_tac >> fs [oneline compile_crepop_def] >>
     Cases_on ‘bop’ >>
     rpt(pairarg_tac >> fs [] >> rveq) >>
     fs [locals_touched_def, crepLangTheory.var_cexp_def, ETA_AX,AllCaseEqs()]
     )
  >~ [‘compile_exps’] >-
   (rpt gen_tac >>
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
    strip_tac >> fs []) >>
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
  ∀s e v (t :('a, 'b) loopSem$state) ctxt tmp l p le ntmp nl.
  eval s e = SOME v /\
  state_rel s t /\ mem_rel s.memory t.memory s.memaddrs /\
  globals_rel s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exp ctxt tmp l e = (p,le, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     eval st le = SOME (wlab_wloc v) /\
     state_rel s st /\ mem_rel s.memory st.memory s.memaddrs /\
     globals_rel s.globals st.globals /\
     code_rel ctxt s.code st.code /\
     locals_rel ctxt nl s.locals st.locals
Proof
  ho_match_mp_tac crepSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [‘eval s $ Op bop es’] >-
   (rename [‘eval s (Op op es)’] >>
    rw [] >>
    fs [Once compile_exp_def] >> fs [] >>
    pairarg_tac >> fs [] >> rveq >>
    fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
    fs [loopSemTheory.eval_def, wlab_wloc_def] >>
    qsuff_tac ‘∃ck st.
                 evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) ∧
                 the_words (MAP (λa. eval st a) les) =
                 SOME ((MAP (λw. case w of Word n =>  n) ws)) /\
                 state_rel s st ∧ mem_rel s.memory st.memory s.memaddrs ∧
                 globals_rel s.globals st.globals ∧
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
    fs [])
  >~ [‘eval s $ Crepop bop es’] >-
   (rw [] >>
    fs [Once compile_exp_def] >> fs [] >>
    pairarg_tac >> fs [] >> rveq >>
    fs [crepSemTheory.eval_def, CaseEq "option"] >> rveq >>
    fs [loopSemTheory.eval_def, wlab_wloc_def] >>
    fs [wlab_wloc_def] >>
    gvs[AllCaseEqs(),oneline crep_op_def,
        oneline compile_crepop_def,MAP_EQ_CONS,
        opt_mmap_eq_some,SF DNF_ss,
        compile_exps_alt
       ] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[AllCaseEqs()] >>
    rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
    first_x_assum drule_all >> strip_tac >>
    first_x_assum drule >> rpt $ disch_then drule >>
    (impl_keep_tac
     >- (imp_res_tac compile_exp_out_rel_cases >> DECIDE_TAC) >>
     strip_tac >>
     qexists_tac ‘ck + ck'’ >>
     qpat_x_assum ‘evaluate _ = (NONE,_)’ mp_tac >>
     drule loopPropsTheory.evaluate_add_clock_eq >>
     disch_then(qspec_then ‘ck'’ mp_tac) >>
     impl_tac >> simp[] >>
     strip_tac >>
     FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
     drule_then (PURE_REWRITE_TAC o single) (cj 2 evaluate_nested_seq_cases) >>
     strip_tac >>
     drule_then (PURE_REWRITE_TAC o single) (cj 2 evaluate_nested_seq_cases) >>
     drule_then drule nested_seq_pure_evaluation >>
     disch_then $ drule_at $ Pos last >>
     imp_res_tac compile_exp_out_rel_cases >> rveq >>
     ntac 2 $ disch_then drule >>
     simp[GSYM PULL_EXISTS] >>
     impl_tac >-
      (qexists_tac ‘tmp''’ (* generated name *) >>
       rw[] >>
       imp_res_tac comp_exp_assigned_vars_tmp_bound_cases >>
       TRY DECIDE_TAC >>
       MAP_FIRST match_mp_tac [cj 1 compile_exp_le_tmp_domain,
                               cj 2 compile_exp_le_tmp_domain] >>
       imp_res_tac locals_rel_intro >>
       first_x_assum $ irule_at $ Pos last >>
       ntac 2 $ first_x_assum $ irule_at $ Pos hd >>
       simp[] >>
       rw[] >>
       drule_all eval_some_var_cexp_local_lookup >>
       metis_tac[]) >>
     strip_tac >>
     simp[evaluate_def,nested_seq_def,eval_def,loop_arith_def,set_var_def,lookup_insert] >>
     rename1 ‘eval(st' with locals := insert tmp' (wlab_wloc (Word ww)) st'.locals) lee’ >>
     ‘∀w. eval (set_var tmp' (wlab_wloc w) st') lee
          =
          eval st' lee
     ’
       by(strip_tac >>
          match_mp_tac locals_touched_eq_eval_eq >>
          simp[set_var_def] >>
          imp_res_tac locals_rel_intro >>
          drule compile_exp_le_tmp_domain >>
          disch_then $ drule_then drule >>
          simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
          impl_tac
          >- (rw[] >>
              imp_res_tac eval_some_var_cexp_local_lookup >>
              metis_tac[]) >>
          rw[] >>
          res_tac >>
          rw[lookup_insert]) >>
     gvs[set_var_def] >>
     simp[set_var_def,wlab_wloc_def,lookup_insert,GSYM word_mul_def] >>
     simp[word_mul_def] >>
     conj_tac >- gvs[state_rel_def] >>
     gvs[locals_rel_def,list_insert_def] >>
     conj_tac
     >- (drule_then match_mp_tac SUBSET_TRANS >>
         rw[SUBSET_DEF]) >>
     rw[] >>
     res_tac >>
     gvs[] >>
     gvs[ctxt_max_def] >>
     res_tac >>
     rw[lookup_insert]))
  >~ [‘Const w’] >-
   (fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
    fs [nested_seq_def, evaluate_def, eval_def,
        wlab_wloc_def, state_rel_clock_add_zero])
  >~ [‘eval s (Var vname)’] >-
   (fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
    fs [nested_seq_def, evaluate_def, find_var_def] >>
    imp_res_tac locals_rel_intro >>
    fs [eval_def, state_rel_clock_add_zero])
  >~ [‘eval s (Load e)’] >-
   (fs [crepSemTheory.eval_def] >>
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
    gvs[mem_rel_def])
  >>~ [‘eval s (LoadByte e)’,‘eval s (Load32 e)’]
  >- (fs [crepSemTheory.eval_def] >>
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
      qpat_abbrev_tac ‘X = [loopLang$Assign tmp' _; _]’ >>
      disch_then (qspec_then ‘X’ mp_tac) >>
      strip_tac >> fs [Abbr‘X’] >>
      pop_assum kall_tac >>
      fs [nested_seq_def, loopSemTheory.evaluate_def] >>
      fs [set_var_def, wlab_wloc_def] >>
      fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
          wordSemTheory.mem_load_byte_aux_def,
          panSemTheory.mem_load_32_def, wordSemTheory.mem_load_32_def] >>
      drule mem_rel_intro >> strip_tac >>
      last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
      strip_tac >> fs [] >>
      rev_drule mem_rel_intro >> strip_tac >>
      last_x_assum (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
      strip_tac >> fs [wlab_wloc_def] >>
      rfs[] >>
      imp_res_tac state_rel_intro >>
      fs [eval_def, state_rel_def] >>
      imp_res_tac compile_exp_out_rel >>
      fs [locals_rel_def, SUBSET_INSERT_RIGHT] >>
      rpt gen_tac >> strip_tac >>
      first_x_assum drule >> fs [] >>
      strip_tac >> fs [] >>
      fs [lookup_insert] >>
      TOP_CASE_TAC >> fs [] >>
      fs [ctxt_max_def] >>
      first_x_assum drule >> fs [])
  >- (fs [crepSemTheory.eval_def] >>
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
      qpat_abbrev_tac ‘X = [loopLang$Assign tmp' _; _]’ >>
      disch_then (qspec_then ‘X’ mp_tac) >>
      strip_tac >> fs [Abbr‘X’] >>
      pop_assum kall_tac >>
      fs [nested_seq_def, loopSemTheory.evaluate_def] >>
      fs [set_var_def, wlab_wloc_def] >>
      fs [panSemTheory.mem_load_byte_def, CaseEq "word_lab",
          wordSemTheory.mem_load_byte_aux_def,
          panSemTheory.mem_load_32_def, wordSemTheory.mem_load_32_def] >>
      drule mem_rel_intro >>
      disch_then (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
      strip_tac >> fs [] >>
      rev_drule mem_rel_intro >>
      disch_then (qspec_then ‘byte_align c’ (mp_tac o GSYM)) >>
      strip_tac >> fs [wlab_wloc_def] >>
      rfs[] >>
      imp_res_tac state_rel_intro >>
      fs [eval_def, state_rel_def] >>
      imp_res_tac compile_exp_out_rel >>
      fs [locals_rel_def, SUBSET_INSERT_RIGHT] >>
      rpt gen_tac >> strip_tac >>
      first_x_assum drule >> fs [] >>
      strip_tac >> fs [] >>
      fs [lookup_insert] >>
      TOP_CASE_TAC >> fs [] >>
      fs [ctxt_max_def] >>
      first_x_assum drule >> fs [])
  >~ [‘eval s (LoadGlob gadr)’] >-
   (fs [crepSemTheory.eval_def, compile_exp_def] >> rveq >>
    fs [nested_seq_def, loopSemTheory.evaluate_def] >>
    fs [eval_def] >>
    imp_res_tac globals_rel_intro >>
    fs [] >>
    qexists_tac ‘0’ >> fs [] >>
    ‘t with clock := t.clock = t’ suffices_by fs [] >>
    fs [state_component_equality])
  >~ [‘Shift’] >-
   (rw [] >>
    fs [crepSemTheory.eval_def, CaseEq "option", CaseEq "word_lab",
        compile_exp_def] >>
    rveq >> fs [] >>
    pairarg_tac >> fs [] >> rveq >>
    fs [loopSemTheory.evaluate_def] >>
    last_x_assum drule_all >>
    strip_tac >> rfs [] >>
    qexists_tac ‘ck’ >> fs [] >>
    fs [loopSemTheory.eval_def, wlab_wloc_def])
  >~ [‘Cmp’] >-
   (rw [] >>
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
  ∀es s vs (t :('a, 'b) loopSem$state) ctxt tmp l p les ntmp nl.
  OPT_MMAP (eval s) es = SOME vs /\
  state_rel s t /\ mem_rel s.memory t.memory s.memaddrs /\
  globals_rel s.globals t.globals /\
  code_rel ctxt s.code t.code /\
  locals_rel ctxt l s.locals t.locals /\
  compile_exps ctxt tmp l es = (p,les, ntmp, nl) /\
  ctxt.vmax < tmp ==>
     ?ck st. evaluate (nested_seq p,t with clock := t.clock + ck) = (NONE,st) /\
     OPT_MMAP (eval st) les = SOME (MAP wlab_wloc vs) /\
     state_rel s st /\ mem_rel s.memory st.memory s.memaddrs /\
     globals_rel s.globals st.globals /\
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
                          ‘tmp'’, ‘le’, ‘wlab_wloc h'’, ‘ck’, ‘ck'’] mp_tac) >>
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
   rw [Once compile_exp_def, oneline compile_crepop_def, AllCaseEqs()] >> rveq >>
   rpt(pairarg_tac >> gvs[AllCaseEqs()]) >>
   match_mp_tac survives_nested_seq_intro >>
   simp[nested_seq_def,survives_def] >>
   match_mp_tac survives_nested_seq_intro >>
   res_tac >>
   simp[survives_MAPi_Assign])
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


Triviality member_cutset_survives_comp_exp_flip =
    member_cutset_survives_comp_exp |> ONCE_REWRITE_RULE [CONJ_COMM]
Triviality member_cutset_survives_comp_exps_flip =
    member_cutset_survives_comp_exps |> ONCE_REWRITE_RULE [CONJ_COMM]



Theorem member_cutset_survives_comp_prog:
  !ctxt l p n.
   n ∈ domain l ==>
   survives n (compile ctxt l p)
Proof
  ho_match_mp_tac (name_ind_cases [] compile_ind)
  \\ rw [] \\ fs []
  \\ fs [compile_def, survives_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [CaseEq "prod", CaseEq "option"]
  \\ rpt (irule_at Any survives_nested_seq_intro)
  \\ fs [nested_seq_def, survives_def]
  \\ rpt TOP_CASE_TAC
  \\ rpt (irule_at Any survives_nested_seq_intro)
  \\ fs [nested_seq_def, survives_def]
  \\ rpt (drule_then (irule_at Any) member_cutset_survives_comp_exp_flip)
  \\ rpt (drule_then (irule_at Any) member_cutset_survives_comp_exps_flip)
  \\ fs []
  \\ TRY (irule nested_assigns_survives)
  \\ fs [gen_temps_def]
  \\ imp_res_tac compile_exp_out_rel
  \\ fs []
  \\ TRY (irule_at Any (cut_sets_union_domain_subset |> REWRITE_RULE [SUBSET_DEF]))
  \\ fs []
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
   qpat_x_assum ‘compile_exp _ _ _ (Crepop _ _) = _’ mp_tac >>
   rw [Once compile_exp_def, AllCaseEqs(),oneline compile_crepop_def
            ] >> rveq >>
   rpt(pairarg_tac >> fs []) >>
   gvs[assigned_vars_MAPi_Assign,assigned_vars_nested_seq_split,MEM_GENLIST,
       assigned_vars_def,nested_seq_def,AllCaseEqs()
        ] >>
   imp_res_tac compile_exp_out_rel_cases >>
   DECIDE_TAC)
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
  ho_match_mp_tac (name_ind_cases [] compile_ind)
  \\ rw []
  >~ [‘Case (crepLang$Dec _ _ _)’]
  >~ [‘Case (crepLang$Call _ _ _)’]
  >- (
    fs [assigned_vars_def, compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ simp [nested_seq_def, assigned_vars_nested_seq_split, assigned_vars_def]
    \\ drule_then (irule_at Any) not_mem_assigned_mem_gt_comp_exps
    \\ simp [assigned_vars_nested_assign, gen_temps_def, MEM_GENLIST]
    \\ imp_res_tac compile_exps_out_rel
    \\ simp []
    \\ gvs [CaseEq "prod", CaseEq "option", assigned_vars_def]
    \\ conj_tac >- (
      cases_on `rt` \\ fs [rt_var_def]
      \\ TOP_CASE_TAC \\ fs []
      \\ CCONTR_TAC \\ gs []
    )
    >- (
      rpt (TOP_CASE_TAC \\ fs [assigned_vars_def])
    )
  )
  >- (
    fs [assigned_vars_def, compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ simp [nested_seq_def, assigned_vars_nested_seq_split, assigned_vars_def]
    \\ drule_then (irule_at Any) not_mem_assigned_mem_gt_comp_exp
    \\ simp []
    \\ first_assum (irule_at Any)
    \\ imp_res_tac compile_exp_out_rel
    \\ fs [ctxt_max_def, FLOOKUP_UPDATE]
    \\ rw []
    \\ res_tac
    \\ simp []
  )
  \\ fs [assigned_vars_def, compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [nested_seq_def, assigned_vars_nested_seq_split, assigned_vars_def]
  \\ imp_res_tac compile_exp_out_rel
  \\ fs []
  \\ rpt (drule_then (irule_at Any) not_mem_assigned_mem_gt_comp_exp)
  \\ simp []
  \\ rpt TOP_CASE_TAC
  \\ fs [nested_seq_def, assigned_vars_nested_seq_split, assigned_vars_def]
  \\ rpt (drule_then (irule_at Any) not_mem_assigned_mem_gt_comp_exp)
  \\ simp []
  \\ strip_tac \\ gs []
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
  gvs[] >>
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
  drule mem_rel_intro >>
  rw [FDOM_FLOOKUP] >> res_tac >> fs [] >>
  gvs[]
QED

Theorem compile_Raise:
  ^(get_goal "compile _ _ (crepLang$Raise _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def, eval_def, set_var_def, lookup_insert,
      call_env_def, state_rel_def, crepSemTheory.empty_locals_def] >> rveq >>
  fs [mem_rel_def]
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
  ‘eval (st' with locals := insert stmp (wlab_wloc w) st'.locals) dle =
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
  drule mem_rel_intro >>
  rw [mem_rel_def] >>
  rw [APPLY_UPDATE_THM]
QED


Theorem compile_Store32:
  ^(get_goal "compile _ _ (crepLang$Store32 _ _)")
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
                   Store32 stmp (stmp + 1)]’ mp_tac) >>
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
  fs [wordSemTheory.mem_store_32_def, panSemTheory.mem_store_32_def,
      AllCaseEqs ()] >>
  rveq >> fs [lookup_insert] >>
  ‘st'.memory (byte_align adr) = Word v’ by (
    gvs[mem_rel_def] >> res_tac >>
    metis_tac[wlab_wloc_def]) >>
  fs [state_rel_def] >>
  (reverse conj_tac
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
   drule mem_rel_intro >>
   rw [mem_rel_def] >>
   rw [APPLY_UPDATE_THM] >>
   fs [wlab_wloc_def])
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
    gvs[mem_rel_def] >>
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
  rw [APPLY_UPDATE_THM] >>
  gvs[wlab_wloc_def]
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
  reverse FULL_CASE_TAC >> fs [] >> rveq >>
  res_tac >> fs []
QED

Theorem compile_ShMem:
  ^(get_goal "compile _ _ (crepLang$ShMem _ _ _)")
Proof
  rw [] >>
  fs [crepSemTheory.evaluate_def, evaluate_def,
      compile_def,CaseEq"option",CaseEq"word_lab"] >> rveq >>
  cases_on ‘FLOOKUP s.locals v’>>fs[]>>
  pairarg_tac >> fs [] >>
  TOP_CASE_TAC >> fs [] >-
   (imp_res_tac locals_rel_intro >> fs [])>>
  rename1 ‘ShMem _ xx _’>>
  drule comp_exp_preserves_eval >>
  rpt (disch_then $ drule_at (Pos hd))>>
  fs [] >> strip_tac >> fs [] >>
  qexists_tac ‘ck’ >>fs[]>>
  drule evaluate_none_nested_seq_append >>
  disch_then (qspec_then ‘[ShMem op xx le]’ assume_tac) >>
  fs [] >> pop_assum kall_tac >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac>>fs[wlab_wloc_def,CaseEq"option"]>>
  imp_res_tac locals_rel_intro>>
  rfs[]>>fs[]>>
  cases_on ‘op’>>
  fs[crepSemTheory.sh_mem_op_def,
     crepSemTheory.sh_mem_load_def,crepSemTheory.sh_mem_store_def,
     sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
     empty_locals_def,call_env_def,
     CaseEq"option",CaseEq"bool",CaseEq"ffi_result"]>>
  fs[wlab_wloc_def]>>
  rveq>>fs[crepSemTheory.set_var_def,set_var_def]>>
  fs [state_rel_def]>>
  gvs[] >>~- ([‘SharedMem MappedRead’],
   fs[locals_rel_def]>>rw[]>-
     (imp_res_tac compile_exp_out_rel >>
      rveq >>
      drule cut_sets_union_domain_subset >>strip_tac>>
      match_mp_tac SUBSET_TRANS >>
      qexists_tac ‘domain (cut_sets l (nested_seq p))’ >>
      fs [] >>
      metis_tac [SUBSET_INSERT_RIGHT]) >>
    fs[lookup_insert,FLOOKUP_UPDATE]>>
    FULL_CASE_TAC>-gvs[wlab_wloc_def]>>
    first_x_assum $ qspecl_then [‘vname’, ‘v'’] assume_tac>>
    first_x_assum $ qspecl_then [‘vname’, ‘v'’] assume_tac>>
    rfs[]>>
    ‘n <> n'’ by
      (CCONTR_TAC>>fs[distinct_vars_def]>>
       first_x_assum $ qspecl_then [‘v’, ‘vname’, ‘n'’] assume_tac>>
       gvs[])>>fs[])>>
  (*write*)
  fs[CaseEq"word_lab",CaseEq"word_loc",CaseEq"bool",
     CaseEq"ffi_result"]>>
  rveq>>fs[]>>gvs[wlab_wloc_def]>>
  ‘subspt l l'’ by (
    imp_res_tac compile_exp_out_rel >> fs [] >>
    imp_res_tac comp_syn_impl_cut_sets_subspt >> fs [] >>
    rveq >> metis_tac [subspt_trans]) >>
  match_mp_tac locals_rel_cutset_prop >>
  metis_tac []
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
  rw []
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
                [‘st' with locals := insert tmp (wlab_wloc value) st'.locals’,
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
  TOP_CASE_TAC >> fs [] >> rveq >>
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
    disch_then (qspecl_then [‘pn’,‘wlab_wloc pv’] mp_tac) >>
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
    disch_then (qspecl_then [‘pn’,‘wlab_wloc pv’] mp_tac) >>
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
    gvs[mem_rel_def] >>
    rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
    spose_not_then strip_assume_tac >>
    first_x_assum $ drule_then assume_tac >>
    gvs[wlab_wloc_def]) >>
  fs [state_rel_def]
  >- (
   fs [] >>
   reverse conj_tac
   >- (
    fs [locals_rel_def] >>
    fs [domain_inter] >>
    rw [] >>
    res_tac >> fs [] >> rveq >>
    rfs [lookup_inter, domain_lookup]) >>
   match_mp_tac write_bytearray_mem_rel >>
   gvs []) >>
  fs [call_env_def,mem_rel_def]
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
   gvs [state_rel_def, crepSemTheory.empty_locals_def]) >>
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
    conj_tac >- gvs[] >>
    imp_res_tac compile_exp_out_rel >>
    rveq >>
    fs [locals_rel_def] >>
    conj_asm1_tac
    >- (
     drule cut_sets_union_domain_subset >>
     strip_tac >>
     match_mp_tac SUBSET_TRANS >>
     qexists_tac ‘domain (cut_sets l (nested_seq np))’ >>
     fs [] >>
     fs [SUBSET_INSERT_RIGHT]) >>
    rw [] >> last_assum drule >> strip_tac >> fs [] >>
    rveq >> fs [] >>
    rw [] >> first_assum drule >> strip_tac >> fs [] >>
    gvs[] >>
    ‘n <> tmp’ by (
      CCONTR_TAC >> fs [] >> rveq >>
      imp_res_tac compile_exp_out_rel >>
      rveq >>
      fs [ctxt_max_def] >>
      last_x_assum drule >>
      last_x_assum drule >>
      strip_tac >>
      disch_then kall_tac >>
      gvs[]) >>
    fs [lookup_insert,domain_lookup]) >>
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
   conj_tac >- gvs[] >>
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
   rw [] >> last_assum drule >> strip_tac >> fs [] >>
   rveq >> fs [] >>
   rw [] >> first_assum drule >> strip_tac >> fs [] >>
   gvs[] >>
   ‘n <> tmp’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     imp_res_tac compile_exp_out_rel >>
     rveq >>
     fs [ctxt_max_def] >>
     last_x_assum drule >>
     last_x_assum drule >>
     strip_tac >>
     disch_then kall_tac >>
     gvs[]) >>
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
   mem_rel s.memory st.memory s.memaddrs /\
   globals_rel s.globals st.globals /\
   code_rel ctxt s.code st.code /\
   locals_rel ctxt nl s.locals st.locals /\
   FLOOKUP s.code fname = SOME (ns,prog) /\
   FLOOKUP ctxt.funcs fname = SOME (loc,LENGTH lns) /\
   MAP (eval s) argexps = MAP SOME args ==>
   let nctxt = ctxt_fc ctxt.target ctxt.funcs ns lns in
        state_rel
          (s with
           <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock − 1|>)
          (st with
           <|locals :=
               fromAList
                 (ZIP (lns, MAP wlab_wloc args));
             clock := st.clock − 1|>) ∧
        code_rel nctxt s.code st.code ∧
        locals_rel nctxt (list_to_num_set lns)
          (FEMPTY |++ ZIP (ns,args))
          (fromAList
             (ZIP (lns, MAP wlab_wloc args)))
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
     disch_then drule >>
     fs [] >>
     strip_tac >> fs [] >>
     fs [MEM_EL] >>
     qexists_tac ‘n’ >> fs [] >>
     drule EL_ZIP >>
     disch_then (qspec_then ‘n’ mp_tac) >> fs []) >>
   assume_tac list_max_max >>
   pop_assum (qspec_then ‘lns’ assume_tac) >>
   fs [EVERY_MEM]) >>
  ‘FRONT (MAP wlab_wloc args ++ [Loc loc 0]) =
   MAP wlab_wloc args’ by (
    rewrite_tac  [FRONT_APPEND, FRONT_DEF] >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  conj_tac
  >- (
   fs [domain_fromAList] >>
   ‘LENGTH lns = LENGTH (MAP wlab_wloc args)’ by
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
  ‘lookup (EL n lns) (fromAList (ZIP (lns,MAP wlab_wloc args))) =
   SOME (EL n (MAP wlab_wloc args))’ by (
    fs [lookup_fromAList] >>
    ‘n < LENGTH (ZIP (lns,MAP wlab_wloc args))’ by
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
  disch_then (qspec_then ‘wlab_wloc’ assume_tac) >>
  fs [] >>
  cases_on ‘EL n args’ >>
  fs [wlab_wloc_def]
QED

Triviality evaluate_none_nested_seq_append_eq:
  evaluate (loopLang$nested_seq p, s) = (NONE, s1) /\
  evaluate (nested_seq q, s1) = res_s
  ==> evaluate (nested_seq (p ++ q), s) = res_s
Proof
  rw [] \\ simp [evaluate_none_nested_seq_append]
QED

Triviality find_code_collapse_cases:
  (dest <> NONE ==> dest = SOME loc) ==>
  find_code dest (args1 ++ TAKE (case dest of NONE => 1 | SOME _ => 0) [Loc loc 0]) st.code
  = (case lookup loc st.code of
      NONE => NONE
    | SOME (params,exp) =>
      if LENGTH args1 = LENGTH params then
        SOME (fromAList (ZIP (params,args1)),exp)
      else NONE)
Proof
  Cases_on `dest`
  \\ fs [find_code_def, FRONT_APPEND]
QED

Triviality OPT_MMAP_APPEND:
  OPT_MMAP f (xs ++ ys) = (OPTION_BIND (OPT_MMAP f xs)
    (\xsv. OPTION_BIND (OPT_MMAP f ys) (\ysv. SOME (xsv ++ ysv))))
Proof
  Induct_on `xs` \\ simp [OPT_MMAP_def]
  \\ Cases_on `OPT_MMAP f ys` \\ simp []
  \\ rw []
  \\ Cases_on `f h` \\ simp []
  \\ Cases_on `OPT_MMAP f xs` \\ simp []
QED

Triviality case_le:
  (case dest of NONE => 1 | SOME v1 => 0) <= 1n
Proof
  TOP_CASE_TAC \\ simp []
QED

Triviality crep_eval_upd_clock:
  crepSem$eval (s with clock := v) = crepSem$eval s
Proof
  simp [FUN_EQ_THM, crepPropsTheory.eval_upd_clock_eq]
QED

Triviality loop_eval_upd_clock:
  loopSem$eval (s with clock := v) = eval s
Proof
  simp [FUN_EQ_THM, loopPropsTheory.eval_upd_clock_eq]
QED

Triviality UNCURRY_eq_case:
  UNCURRY f x = (case x of (a, b) => f a b)
Proof
  Cases_on `x` \\ simp []
QED

Triviality locals_rel_lookup_same:
  locals_rel ctxt l locs1 locs2 ==>
  (! n. lookup n locs2 = lookup n locs3) ==>
  locals_rel ctxt l locs1 locs3
Proof
  simp [locals_rel_def, SUBSET_DEF, domain_lookup]
  \\ metis_tac []
QED

Triviality locals_rel_inter_helper:
  locals_rel ctxt l locs1 locs2 ==>
  EVERY (\i. lookup i l = NONE) xs ==>
  LENGTH xs = LENGTH ys ==>
  locals_rel ctxt l locs1
    (inter (alist_insert xs ys locs2) l)
Proof
  simp [locals_rel_def, SUBSET_DEF, domain_lookup, lookup_inter, lookup_alist_insert]
  \\ rw []
  >- (
    res_tac
    \\ simp [CaseEq "option"]
    \\ metis_tac [option_nchotomy]
  )
  >- (
    res_tac
    \\ simp [CaseEq "option"]
    \\ DEP_REWRITE_TAC [last (RES_CANON ALOOKUP_NONE)]
    \\ fs [MAP_ZIP, EVERY_MEM]
    \\ strip_tac \\ res_tac \\ fs []
  )
QED

Theorem compile_Call:
  ^(get_goal "compile _ _ (crepLang$Call _ _ _)")
Proof
  rw []
  \\ fs [crepSemTheory.evaluate_def,
       CaseEq "option", CaseEq "word_lab",CaseEq "prod"]
  \\ rveq \\ fs []
  \\ fs [compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule_at (Pat `compile_exps _ _ _ _ = _`) comp_exps_preserves_eval
  \\ disch_then (drule_at (Pat `mem_rel _ _ _`))
  \\ simp [OPT_MMAP_APPEND]
  \\ rw []
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ irule_at Any evaluate_none_nested_seq_append_eq
  \\ irule_at Any evaluate_none_nested_seq_append_eq
  \\ irule_at Any loop_eval_nested_assign_distinct_eq
  \\ simp [GSYM opt_mmap_eq_some]
  \\ simp [nested_seq_def]
  \\ drule evaluate_add_clock_eq
  \\ simp []
  \\ rewrite_tac [ADD_ASSOC]
  \\ disch_then (irule_at Any)
  \\ simp [crep_eval_upd_clock, loop_eval_upd_clock]
  \\ simp_tac bool_ss [GSYM PULL_EXISTS]
  \\ `LENGTH argexps = LENGTH args`
    by (fs [opt_mmap_eq_some] \\ metis_tac [LENGTH_MAP])
  \\ rewrite_tac [CONJ_ASSOC]
  \\ conj_tac >- (
    simp [gen_temps_def, ALL_DISTINCT_GENLIST]
    (* prove the GENLIST doesn't intersect the previous locals - no fun *)
    \\ imp_res_tac compile_exps_out_rel \\ fs []
    \\ simp [distinct_lists_def, EVERY_GENLIST]
    \\ rpt strip_tac
    \\ drule_at (Pat `compile_exps _ _ _ _ = _`) compile_exps_le_tmp_domain
    \\ disch_then (drule_at (Pat `MEM _ (FLAT _)`))
    \\ imp_res_tac locals_rel_intro
    \\ rw []
    \\ gvs [MEM_FLAT, MEM_MAP]
    \\ metis_tac [opt_mmap_mem_func, eval_some_var_cexp_local_lookup]
  )
  \\ simp [evaluate_def]
  \\ simp [get_vars_local_clock_upd_eq]
  \\ DEP_REWRITE_TAC [get_vars_local_update_some_eq]
  \\ conj_tac >- (
    simp [gen_temps_def, ALL_DISTINCT_GENLIST]
    \\ imp_res_tac compile_exps_out_rel
    \\ simp [LENGTH_TAKE_EQ, case_le]
  )
  \\ simp [MAP_TAKE, wlab_wloc_def]
  \\ gs [lookup_code_def, CaseEq "option" |> Q.GEN `v` |> Q.ISPEC `NONE : 'z option`,
        CaseEq "prod"]
  \\ drule_then drule (last (RES_CANON code_rel_intro))
  \\ strip_tac \\ fs [find_code_def,find_lab_def]
  \\ simp [cut_res_def, cut_state_def]
  \\ DEP_REWRITE_TAC [domain_alist_insert]
  \\ conj_tac >- (
    imp_res_tac compile_exps_out_rel
    \\ fs [gen_temps_def, LENGTH_TAKE_EQ, case_le]
  )
  (* case split on clock *)
  \\ fs [CaseEq "bool"]
  >- (
    fs [state_rel_def, PULL_EXISTS]
    \\ GEN_EXISTS_TAC "ck'" `0`
    \\ fs [CaseEq "option"] \\ gvs [CaseEq "prod"]
    \\ fs [crepSemTheory.empty_locals_def]
    \\ rw []
    \\ imp_res_tac locals_rel_intro
    \\ qpat_x_assum `~ (_ SUBSET _)` mp_tac
    \\ simp []
    \\ imp_res_tac compile_exps_out_rel
    \\ irule SUBSET_TRANS
    \\ drule_then (irule_at Any) cut_sets_union_domain_subset
    \\ metis_tac [SUBSET_TRANS, SUBSET_UNION]
  )
  \\ `st.clock <> 0` by fs [state_rel_def]
  \\ gvs [CaseEq "prod"]
  \\ drule_at (Pat `locals_rel _ _ _ _`) call_preserve_state_code_locals_rel
  \\ disch_then (qspecl_then [`ns`, `GENLIST I (LENGTH args)`, `args`] mp_tac)
  \\ simp [GSYM opt_mmap_eq_some]
  \\ rpt (disch_then (drule_at Any))
  \\ simp [ALL_DISTINCT_GENLIST]
  \\ disch_tac \\ fs []
  \\ fs [crepSemTheory.dec_clock_def, dec_clock_def]
  \\ first_x_assum (drule_at (Pat `state_rel _ _`))
  \\ simp []
  \\ disch_then (drule_at (Pat `locals_rel _ _ _`))
  \\ impl_tac
  >- (
    simp [ctxt_fc_def]
    \\ strip_tac \\ fs []
  )
  \\ strip_tac \\ fs []
  \\ drule loop_liveProofTheory.optimise_correct
  \\ impl_tac
  >- (
    gvs [CaseEq "crepSem$result", CaseEq "option"]
  )
  \\ strip_tac
  \\ simp [ocompile_def, PULL_EXISTS]
  \\ gvs [CaseEq "prod", CaseEq "option"]
  >- (
    (* tail call case *)
    GEN_EXISTS_TAC "ck''" `ck'`
    \\ gvs [CaseEq "prod", CaseEq "crepSem$result", CaseEq "option"]
    \\ fs [empty_locals_def, ctxt_fc_def]
    \\ fs [code_rel_def, state_rel_def]
  )
  >- (
    (* general call case *)
    rw []
    \\ qmatch_goalsub_abbrev_tac ‘domain l SUBSET rhs’
    \\ reverse (qsuff_tac `domain l SUBSET rhs`)
    >- (
      fs [Abbr `rhs`]
      \\ imp_res_tac compile_exps_out_rel
      \\ irule SUBSET_TRANS
      \\ drule_then (irule_at Any) cut_sets_union_domain_subset
      \\ imp_res_tac locals_rel_intro
      \\ metis_tac [SUBSET_TRANS, SUBSET_UNION]
    )
    \\ strip_tac \\ simp []
    (* cases by inner result *)
    \\ gvs [CaseEq "prod", CaseEq "crepSem$result"]
    >- (
      GEN_EXISTS_TAC "ck''" `ck'`
      \\ fs [empty_locals_def, ctxt_fc_def] \\ fs [code_rel_def, state_rel_def]
    )
    >- (
      (* the tricky Return case in which rp runs, requiring more clock adjustments *)
      drule evaluate_add_clock_eq
      \\ simp [UNCURRY_eq_case, CaseEq "prod"]
      \\ rewrite_tac [ADD_ASSOC]
      \\ disch_then (irule_at Any)
      \\ simp [set_var_def]
      (* now we have the state rp needs to run on *)
      \\ qmatch_goalsub_abbrev_tac
          `evaluate (_, base_st with <| locals := locs; clock := _ |>)`
      (* unfortunately we just have to case-split here to use the correct IH *)
      \\ gs [CaseEq "option"]
      >- (
        first_x_assum (qspec_then `base_st with <| locals := locs |>` mp_tac)
        \\ fs [Abbr `locs`]
        \\ disch_then (qspecl_then [`ctxt`, `l`] mp_tac)
        \\ simp []
        \\ impl_tac
        >- (
          (* complicated proof that the locals reset correctly *)
          fs [state_rel_def, ctxt_fc_def]
          \\ fs [code_rel_def]
          \\ fs [rt_var_def]
          \\ irule locals_rel_insert_gt_vmax \\ simp []
          \\ simp [locals_rel_def]
          \\ simp [domain_inter]
          \\ DEP_REWRITE_TAC [domain_alist_insert]
          \\ simp [SUBSET_TRANS]
          \\ imp_res_tac compile_exps_out_rel
          \\ simp [gen_temps_def, LENGTH_TAKE_EQ, case_le]
          \\ rw [] \\ imp_res_tac locals_rel_intro \\ fs []
          \\ gs [lookup_inter]
          \\ DEP_REWRITE_TAC [lookup_alist_insert]
          \\ simp [LENGTH_TAKE_EQ, case_le]
          \\ DEP_REWRITE_TAC [last (RES_CANON ALOOKUP_NONE), hd (RES_CANON MAP_ZIP)]
          \\ simp [LENGTH_TAKE_EQ, case_le, MEM_GENLIST]
          \\ fs [domain_lookup]
          \\ fs [ctxt_max_def]
          \\ rw [] \\ res_tac \\ fs []
        )
        \\ rw []
        \\ GEN_EXISTS_TAC "ck''" `if res = NONE then ck'' + 1 else ck''`
        \\ Cases_on `res` \\ gs []
        >- (
          drule_then (qspec_then `1` assume_tac) evaluate_add_clock_eq
          \\ fs []
          \\ simp [cut_res_def, cut_state_def]
          \\ drule_then (CHANGED_TAC o simp o single) locals_rel_intro
          \\ simp [dec_clock_def]
          \\ fs [state_rel_def]
          \\ fs [locals_rel_def, domain_inter, lookup_inter, CaseEq "option"]
          \\ fs [domain_lookup]
          \\ metis_tac []
        )
        >- (
          simp [cut_res_def, cut_state_def]
          \\ fs [TypeBase.case_pred_disj_of ``: 'a crepSem$result``
                  |> Q.ISPEC `\ (x : bool). x` |> SIMP_RULE bool_ss []]
        )
      )
      >- (
        (* second rt case - very similar *)
        first_x_assum (qspec_then `base_st with <| locals := locs |>` mp_tac)
        \\ fs [Abbr `locs`]
        \\ disch_then (qspecl_then [`ctxt`, `l`] mp_tac)
        \\ simp []
        \\ impl_tac
        >- (
          (* complicated proof that the locals reset correctly *)
          fs [state_rel_def, ctxt_fc_def]
          \\ fs [code_rel_def]
          \\ fs [rt_var_def]
          \\ simp [locals_rel_def]
          \\ simp [domain_inter]
          \\ DEP_REWRITE_TAC [domain_alist_insert]
          \\ simp []
          \\ imp_res_tac compile_exps_out_rel
          \\ simp [gen_temps_def, LENGTH_TAKE_EQ, case_le]
          \\ rw [] \\ imp_res_tac locals_rel_intro \\ fs []
          >- (fs [SUBSET_DEF])
          \\ gs [lookup_inter, lookup_insert, FLOOKUP_UPDATE]
          \\ gs [CaseEq "bool"]
          \\ fs []
          \\ imp_res_tac locals_rel_intro \\ fs []
          \\ gvs []
          \\ DEP_REWRITE_TAC [lookup_alist_insert]
          \\ simp [LENGTH_TAKE_EQ, case_le]
          \\ DEP_REWRITE_TAC [last (RES_CANON ALOOKUP_NONE), hd (RES_CANON MAP_ZIP)]
          \\ simp [LENGTH_TAKE_EQ, case_le, MEM_GENLIST]
          \\ fs [domain_lookup]
          \\ fs [ctxt_max_def]
          \\ rw [] \\ res_tac \\ fs []
          \\ gvs []
          \\ imp_res_tac (hd (RES_CANON distinct_vars_def))
          \\ fs []
        )
        \\ rw []
        \\ GEN_EXISTS_TAC "ck''" `if res = NONE then ck'' + 1 else ck''`
        \\ Cases_on `res` \\ gs []
        >- (
          drule_then (qspec_then `1` assume_tac) evaluate_add_clock_eq
          \\ fs []
          \\ simp [cut_res_def, cut_state_def]
          \\ drule_then (CHANGED_TAC o simp o single) locals_rel_intro
          \\ simp [dec_clock_def]
          \\ fs [state_rel_def]
          \\ fs [locals_rel_def, domain_inter, lookup_inter, CaseEq "option"]
          \\ fs [domain_lookup]
          \\ metis_tac []
        )
        >- (
          simp [cut_res_def, cut_state_def]
          \\ fs [TypeBase.case_pred_disj_of ``: 'a crepSem$result``
                  |> Q.ISPEC `\ (x : bool). x` |> SIMP_RULE bool_ss []]
        )
      )
    )
    >- (
      (* handle case, which is really three cases *)
      fs [CaseEq "option", CaseEq "prod", CaseEq "bool"]
      >- (
        (* no handler, direct return *)
        GEN_EXISTS_TAC "ck''" `ck'`
        \\ simp [evaluate_def, set_var_def, cut_res_def, call_env_def]
        \\ gvs []
        \\ simp [empty_locals_def]
        \\ fs [state_rel_def, ctxt_fc_def]
        \\ fs [code_rel_def]
      )
      >- (
        (* caught handler *)
        gvs []
        \\ dxrule evaluate_add_clock_eq
        \\ simp [UNCURRY_eq_case, CaseEq "prod"]
        \\ rewrite_tac [ADD_ASSOC]
        \\ disch_then (irule_at Any)
        \\ simp [evaluate_def, set_var_def, get_var_imm_def, asmTheory.word_cmp_def]
        \\ qmatch_goalsub_abbrev_tac
            `dec_clock (base_st with <| locals := locs; clock := _ |>)`
        \\ first_x_assum (qspec_then `base_st with <| locals := locs |>` mp_tac)
        \\ fs [Abbr `locs`]
        \\ disch_then (qspecl_then [`ctxt`, `l`] mp_tac)
        \\ simp []
        \\ impl_tac
        >- (
          (* yet another copy of basically the same proof about alist insert *)
          fs [state_rel_def, ctxt_fc_def]
          \\ fs [code_rel_def]
          \\ irule locals_rel_insert_gt_vmax \\ simp []
          \\ simp [locals_rel_def]
          \\ simp [domain_inter]
          \\ DEP_REWRITE_TAC [domain_alist_insert]
          \\ simp [SUBSET_TRANS]
          \\ imp_res_tac compile_exps_out_rel
          \\ simp [gen_temps_def, LENGTH_TAKE_EQ, case_le]
          \\ rw [] \\ imp_res_tac locals_rel_intro \\ fs []
          \\ gs [lookup_inter]
          \\ DEP_REWRITE_TAC [lookup_alist_insert]
          \\ simp [LENGTH_TAKE_EQ, case_le]
          \\ DEP_REWRITE_TAC [last (RES_CANON ALOOKUP_NONE), hd (RES_CANON MAP_ZIP)]
          \\ simp [LENGTH_TAKE_EQ, case_le, MEM_GENLIST]
          \\ fs [domain_lookup]
          \\ fs [ctxt_max_def]
          \\ rw [] \\ res_tac \\ fs []
        )
        \\ rw []
        \\ GEN_EXISTS_TAC "ck''" `ck'' + 1 + (if res = NONE then 2 else 0)`
        \\ simp [dec_clock_def]
        \\ Cases_on `res` \\ fs [] \\ rw []
        >- (
          dxrule evaluate_add_clock_eq
          \\ disch_then (qspec_then `2` mp_tac)
          \\ rw []
          \\ simp [cut_res_def, cut_state_def]
          \\ rw [] \\ TRY (imp_res_tac locals_rel_intro \\ fs [] \\ NO_TAC)
          \\ simp [cut_res_def, cut_state_def]
          \\ simp [dec_clock_def, domain_inter]
          \\ fs [state_rel_def]
          \\ simp [locals_rel_def, domain_inter, lookup_inter]
          \\ rw [] \\ imp_res_tac locals_rel_intro \\ fs []
          \\ simp [CaseEq "option"]
          \\ fs [domain_lookup]
        )
        >- (
          fs [cut_res_def]
          \\ reverse (rw [])
          >- (
            fs [CaseEq "crepSem$result"]
          )
          \\ simp [cut_res_def]
        )
      )
      >- (
        gs []
        \\ GEN_EXISTS_TAC "ck''" `ck'`
        \\ simp [evaluate_def, set_var_def, get_var_imm_def, asmTheory.word_cmp_def]
        \\ simp [cut_res_def, call_env_def]
        \\ gvs []
        \\ fs [state_rel_def, empty_locals_def, ctxt_fc_def]
        \\ fs [code_rel_def]
        \\ gvs[]
      )
    )
    >- (
      GEN_EXISTS_TAC "ck''" `ck'`
      \\ simp [cut_res_def]
      \\ gvs []
      \\ fs [state_rel_def, empty_locals_def, ctxt_fc_def]
      \\ fs [code_rel_def]
      \\ gvs[]
    )
  )
QED

Theorem ncompile_correct:
   ^(compile_prog_tm ())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [compile_Skip_Break_Continue, compile_Tick, compile_ShMem,
          compile_Seq, compile_Return, compile_Raise, compile_Store32,
          compile_Store, compile_StoreByte, compile_StoreGlob,
          compile_Assign, compile_Dec, compile_If, compile_FFI,
          compile_While, compile_Call]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED


Theorem ocompile_correct:
  evaluate (p,s) = (res,s1) ∧ state_rel s t ∧
  mem_rel s.memory t.memory s.memaddrs ∧
  globals_rel s.globals t.globals ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt l s.locals t.locals ∧ res ≠ SOME Error ∧ res ≠ SOME Break ∧
  res ≠ SOME Continue ∧ res ≠ NONE ⇒
  ∃ck res1 t1.
    evaluate (ocompile ctxt l p,t with clock := t.clock + ck) =
    (res1,t1) ∧ state_rel s1 t1 ∧ mem_rel s1.memory t1.memory s1.memaddrs ∧
    globals_rel s1.globals t1.globals ∧
    code_rel ctxt s1.code t1.code ∧
    case res of
     | NONE => F
     | SOME Error => F
     | SOME TimeOut => res1 = SOME TimeOut
     | SOME Break => F
     | SOME Continue => F
     | SOME (Return v) => res1 = SOME (Result (wlab_wloc v))
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
  !c crep_code.
    ALL_DISTINCT (MAP FST (compile_prog c crep_code))
Proof
  rw [] >>
  fs [crep_to_loopTheory.compile_prog_def] >>
  simp [MAP2_ZIP, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM, MAP_ZIP] >>
  simp [ALL_DISTINCT_GENLIST]
QED

Definition code_rel2_def:
  code_rel2 ctxt s_code t_code <=>
   code_rel ctxt (FMAP_MAP2 (\(s, n, p). (n,crep_arith$simp_prog p)) s_code) t_code
End

Triviality ALOOKUP_EQ_EL:
  n < LENGTH xs ==>
  FST (EL n xs) = nm ==>
  ALL_DISTINCT (MAP FST xs) ==>
  y = SND (EL n xs) ==>
  ALOOKUP xs nm = SOME y
Proof
  rw []
  \\ irule ALOOKUP_ALL_DISTINCT_MEM
  \\ simp []
  \\ simp [MEM_EL]
  \\ metis_tac []
QED

Theorem mk_ctxt_code_imp_code_rel2:
  !c crep_code start np. ALL_DISTINCT (MAP FST crep_code) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  code_rel2 (mk_ctxt c FEMPTY (make_funcs crep_code) 0)
            (alist_to_fmap crep_code)
            (fromAList (crep_to_loop$compile_prog c crep_code))
Proof
  rw [code_rel2_def, code_rel_def, mk_ctxt_def]
  \\ fs [distinct_make_funcs]
  \\ fs [FLOOKUP_FMAP_MAP2, EXISTS_PROD]
  \\ fs [mk_ctxt_def, make_funcs_def]
  \\ fs [ocompile_def, compile_prog_def, lookup_fromAList]
  \\ drule ALOOKUP_MEM
  \\ rw []
  \\ fs [MEM_EL]
  \\ qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM)
  \\ rpt (irule_at Any ALOOKUP_EQ_EL)
  \\ simp []
  \\ rpt (qpat_assum `_ < LENGTH _` (irule_at Any))
  \\ simp [EL_MAP2, EL_MAP]
  \\ simp [comp_func_def, mk_ctxt_def, ctxt_fc_def, make_vmap_def,
    make_funcs_def, pan_commonPropsTheory.list_max_i_genlist]
  \\ simp [MAP2_ZIP, MAP_MAP_o, o_DEF, ELIM_UNCURRY]
  \\ simp [ETA_THM, MAP_ZIP]
  \\ simp [ALL_DISTINCT_GENLIST]
QED

(*
Theorem make_funcs_ALOOKUP_compile_prog:
  !start lc crep_code c. FLOOKUP (make_funcs crep_code) start = SOME (lc,0) ==>
    ALL_DISTINCT (MAP FST crep_code) ==>
    ALOOKUP (compile_prog c crep_code) lc =
        SOME ([], optimise (comp_func c (make_funcs crep_code) []
            (SND (THE (ALOOKUP crep_code start)))))
Proof
  rw [make_funcs_def]
  \\ drule ALOOKUP_MEM
  \\ csimp [MEM_EL, EL_MAP2, EL_MAP]
  \\ rw []
  \\ irule ALOOKUP_ALL_DISTINCT_MEM
  \\ simp [first_compile_prog_all_distinct]
  \\ csimp [compile_prog_def, MEM_EL, EL_MAP2]
  \\ simp [UNCURRY]
  \\ simp [ALOOKUP_ALL_DISTINCT_EL, make_funcs_def]
QED
*)

Theorem make_funcs_domain_compile_prog:
  !start lc crep_code c. FLOOKUP (make_funcs crep_code) start = SOME (lc,0) ==>
    lc ∈ domain (fromAList (compile_prog c crep_code))
Proof
  rw [] >>
  fs [domain_fromAList, make_funcs_def] >>
  drule ALOOKUP_MEM >>
  csimp [MEM_EL, EL_MAP2, EL_MAP] >>
  csimp [compile_prog_def, EL_MAP2, UNCURRY] >>
  metis_tac []
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
  ∀prog c.
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog ⇒
    EVERY (λ(name,params,body). ALL_DISTINCT params) (compile_prog c prog)
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

Triviality evaluate_Seq_Skip:
  loopSem$evaluate (Seq prog Skip, s) = evaluate (prog, s)
Proof
  simp [evaluate_def]
  \\ pairarg_tac \\ fs []
  \\ simp [CaseEq "bool"]
QED

Triviality evaluate_less_clock_cases:
  loopSem$evaluate (prog, s) = (res, s2) ==>
  ck <= s.clock ==>
  ? res2 s3.
  loopSem$evaluate (prog, s with clock := ck) = (res2, s3) /\
  ((res = res2 /\ (?ck2. s3 = (s2 with clock := ck2))) \/
    (res2 = SOME TimeOut))
Proof
  rw []
  \\ cases_on `evaluate (prog,s with clock := ck)`
  \\ CCONTR_TAC \\ fs []
  \\ drule_then (qspec_then `s.clock - ck` mp_tac) evaluate_add_clock_eq
  \\ `(s with clock := s.clock) = s` by fs[loopSemTheory.state_component_equality]
  \\ rw []
  \\ CCONTR_TAC \\ fs []
  \\ fs [loopSemTheory.state_component_equality]
QED

Triviality evaluate_twice_cases:
  loopSem$evaluate (prog, s) = (res, s2) ==>
  loopSem$evaluate (prog, s3) = (res2, s4) ==>
  (s with clock := 0) = (s3 with clock := 0) ==>
  (s.clock <= s3.clock /\ (res = SOME TimeOut \/
    (res = res2 /\ (?ck. s2 = (s4 with clock := ck))))) \/
  (s3.clock <= s.clock /\ (res2 = SOME TimeOut \/
    (res2 = res /\ (?ck. s4 = (s2 with clock := ck)))))
Proof
  rw []
  \\ `?ck. s3 = (s with clock := ck)`
    by (fs [loopSemTheory.state_component_equality])
  \\ fs []
  \\ Cases_on `s.clock <= ck`
  >- (
    drule evaluate_less_clock_cases
    \\ simp []
    \\ disch_then drule
    \\ `(s with clock := s.clock) = s` by fs[loopSemTheory.state_component_equality]
    \\ rw[]
    \\ metis_tac []
  )
  >- (
    last_x_assum assume_tac
    \\ drule_then (qspec_then `ck` mp_tac) evaluate_less_clock_cases
    \\ simp []
    \\ metis_tac []
  )
QED

Triviality evaluate_io_mono_rephrases =
  [crepPropsTheory.evaluate_add_clock_io_events_mono |> Q.SPECL [`exs`, `s with clock := k`],
    loopPropsTheory.evaluate_add_clock_io_events_mono |> Q.SPECL [`exs`, `s with clock := k`]]
    |> map (SIMP_RULE (srw_ss ()) [])
    |> LIST_CONJ

Theorem code_rel_evaluate_call_correct:

code_rel2 nctxt s_code t_code ==>
  evaluate (Call NONE start [], s) = (res, s') ==>
  s.be = t.be /\ s.sh_memaddrs = t.sh_mdomain /\
  s.memaddrs = t.mdomain /\ s.clock = t.clock /\
  s.ffi = t.ffi /\ s.base_addr = t.base_addr /\ s.top_addr = t.top_addr /\
  mem_rel s.memory t.memory s.memaddrs /\
  globals_rel s.globals t.globals /\
  s.locals = FEMPTY /\
  s.code = s_code /\ t.code = t_code ==>
  FLOOKUP (make_funcs crep_code) start = SOME (find_lab nctxt start, 0) ==>
  find_lab nctxt start = lc /\
  s.code = alist_to_fmap crep_code /\
  nctxt.funcs = make_funcs crep_code /\
  ALOOKUP crep_code start = SOME ([],prog) /\
  distinct_vars nctxt.vars /\ ctxt_max nctxt.vmax nctxt.vars

==>
  res <> SOME Error ==>

  ?k res' t'.
  evaluate (Call NONE (SOME (find_lab nctxt start)) [] NONE,
    t with clock := t.clock + k) = (res', t') /\
  state_rel s' t' /\
  (res' = case res of
           NONE => NONE
         | SOME Break => SOME Break
         | SOME Continue => SOME Continue
         | SOME (Return v) => SOME (Result (wlab_wloc v))
         | SOME (Exception eid) => SOME (Exception (Word eid))
         | SOME TimeOut => SOME TimeOut
         | SOME (FinalFFI f) => SOME (FinalFFI f)
         | SOME Error => SOME Error)

Proof
  rw []
  \\ dxrule crep_arithProofTheory.simp_prog_correct
  \\ fs [crep_arithTheory.simp_prog_def, crep_arithTheory.simp_exp_def]
  \\ rw []
  \\ drule ncompile_correct
  \\ simp []
  \\ fs [code_rel2_def]
  \\ disch_then (drule_at (Pat `code_rel _ _ _`))
  \\ disch_then (qspec_then `LN` mp_tac)
  \\ simp [state_rel_def, locals_rel_def]
  \\ gvs[]
  \\ simp [crep_to_loopTheory.compile_def]
  \\ simp [crep_to_loopTheory.compile_exp_def, nested_seq_def, gen_temps_def]
  \\ simp [evaluate_Seq_Skip]
  \\ rw [] \\ fs []
  \\ qexists_tac `ck`
  \\ simp []
QED

Datatype:
  semantics_run_res =
    RunError | CompleteResult 'a | Incomplete
End

Definition semantics_wrapper_def:
  semantics_wrapper f = (if ?k v. f k = (RunError, v) then Fail
    else case some res. ?k r ev. f k = (CompleteResult r, ev) /\ res = Terminate r ev
      of SOME res => res
        | NONE => Diverge (LUB (IMAGE (fromList o SND o f) (UNIV : num set))))
End

Theorem crep_sem_is_wrapper:
  crepSem$semantics s start =
  let prog = crepLang$Call NONE start [] in
  semantics_wrapper (((\res. case res of
    | SOME TimeOut => Incomplete
    | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
    | SOME (Return _) => CompleteResult Success
    | _ => RunError) ## (\s. s.ffi.io_events)) o
    (\k. crepSem$evaluate (prog, s with clock := k)))
Proof
  simp [crepSemTheory.semantics_def, semantics_wrapper_def]
  \\ irule COND_CONG
  \\ rw []
  >- (
    ho_match_mp_tac ConseqConvTheory.exists_eq_thm>>
    strip_tac>>
    simp[totoTheory.SPLIT_PAIRS,AllCasePreds()]>>
    simp[AllCaseEqs()]
  )
  >- (
    irule optionTheory.option_case_cong
    \\ rw []
    >- (
      AP_TERM_TAC
      \\ rw [FUN_EQ_THM]
      \\ AP_TERM_TAC
      \\ rw [FUN_EQ_THM]
      \\ simp [pairTheory.PAIR_MAP, CaseEq "prod"]
      \\ rename [`evaluate (p, s2)`]
      \\ Cases_on `evaluate (p, s2)` \\ simp []
      \\ every_case_tac \\ fs []
    )
    >- (
      AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ rw [FUN_EQ_THM]
    )
  )
QED

Theorem loop_sem_is_wrapper:
  loopSem$semantics s start =
  let prog = loopLang$Call NONE (SOME start) [] NONE in
  semantics_wrapper (((\res. case res of
    | SOME TimeOut => Incomplete
    | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
    | SOME (Result _) => CompleteResult Success
    | _ => RunError) ## (\s. s.ffi.io_events)) o (\k. loopSem$evaluate (prog, s with clock := k)))
Proof
  simp [loopSemTheory.semantics_def, semantics_wrapper_def]
  \\ irule COND_CONG
  \\ rw []
  >- (
    simp []
    \\ AP_TERM_TAC \\ rw [FUN_EQ_THM]
    \\ simp[totoTheory.SPLIT_PAIRS,AllCasePreds()]
    \\ simp[AllCaseEqs()])
  >- (
    irule optionTheory.option_case_cong
    \\ rw []
    >- (
      simp [CaseEq "prod", PULL_EXISTS]
      \\ AP_TERM_TAC \\ rw [FUN_EQ_THM]
      \\ AP_TERM_TAC \\ rw [FUN_EQ_THM]
      \\ simp [pairTheory.PAIR_MAP]
      \\ rename [`evaluate (p, s2)`]
      \\ Cases_on `evaluate (p, s2)` \\ simp []
      \\ every_case_tac \\ fs []
    )
    >- (
      AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ rw [FUN_EQ_THM]
    )
  )
QED

Theorem semantics_wrapper_eq:
  semantics_wrapper absf <> Fail ==>
  (! k r ev. absf k = (r, ev) /\ r <> RunError ==>
    ?k'. concf (k + k') = (r, ev)) ==>
  (!k k' r ev. concf k = (r, ev) ==>
    r <> Incomplete ==>
    concf (k + k') = (r, ev)) ==>
  (!k k' r ev. absf k = (r, ev) ==>
    r <> Incomplete ==>
    absf (k + k') = (r, ev)) ==>
  (!k k' ev. absf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. absf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  (!k k' ev. concf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. concf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  semantics_wrapper concf = semantics_wrapper absf
Proof
  rw []
  \\ Cases_on `semantics_wrapper absf` \\ fs []
  >- (
    fs [semantics_wrapper_def, CaseEq "bool"]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ disch_tac
    \\ reverse (qsuff_tac `?abs2. absf = (\k. (Incomplete, abs2 k))`)
    >- (
      qexists_tac `SND o absf`
      \\ rw [FUN_EQ_THM]
      \\ Cases_on `FST (absf k)` \\ Cases_on `absf k` \\ gs []
    )
    \\ strip_tac \\ fs []
    \\ reverse (qsuff_tac `?conc2. concf = (\k. (Incomplete, conc2 k))`)
    >- (
      qexists_tac `SND o concf`
      \\ rw [FUN_EQ_THM]
      \\ last_x_assum (qspec_then `k` mp_tac)
      \\ strip_tac
      \\ last_x_assum (qspecl_then [`k`, `k'`] mp_tac)
      \\ simp []
      \\ simp [PAIR_FST_SND_EQ]
    )
    \\ rw [] \\ fs []
    \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
    \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
      suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
    \\ conj_asm1_tac
    >- (
      UNABBREV_ALL_TAC
      \\ conj_tac
      \\ REWRITE_TAC[IMAGE_COMPOSE]
      \\ match_mp_tac prefix_chain_lprefix_chain
      \\ simp [prefix_chain_def, PULL_EXISTS]
      \\ qx_genl_tac [‘k1’, ‘k2’]
      \\ qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES
      \\ simp[LESS_EQ_EXISTS]
      \\ rw []
      \\ metis_tac [ADD_COMM]
    )
    \\ simp [equiv_lprefix_chain_thm]
    \\ UNABBREV_ALL_TAC
    \\ simp[LNTH_fromList,PULL_EXISTS]
    \\ conj_tac
    >- (
      rw []
      \\ last_x_assum (qspec_then `x'` mp_tac)
      \\ strip_tac
      \\ pop_assum (assume_tac o GSYM)
      \\ qexists_tac `x'`
      \\ fs []
      \\ metis_tac [IS_PREFIX_THM, LESS_LESS_EQ_TRANS, ADD_COMM]
    )
    >- (
      rw []
      \\ metis_tac []
    )
  )
  \\ fs [semantics_wrapper_def, CaseEq "bool", CaseEq "option"]
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ strip_tac
  \\ last_x_assum drule
  \\ simp [] \\ strip_tac
  \\ rename [`concf a_k = _`]
  \\ qsuff_tac `!k2 r v. concf k2 = (r, v) ==> (r, v) = concf a_k \/ (r = Incomplete)`
  >- (
    simp []
    \\ disch_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ rw [] \\ fsrw_tac [SATISFY_ss] []
    \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs []
  )
  \\ rw []
  \\ qspecl_then [`a_k`, `k2`] mp_tac LESS_EQ_CASES
  \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rw [] \\ res_tac \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ res_tac \\ full_simp_tac bool_ss []
  \\ gs []
QED

Triviality PAIR_MAP_EQ_UNCURRY:
  (f ## g) = (\(x, y). (f x, g y))
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem state_rel_imp_semantics:
  !s t crep_code start lc c. s.memaddrs = t.mdomain ∧
  s.be = t.be ∧ s.sh_memaddrs = t.sh_mdomain ∧
  s.ffi = t.ffi ∧ s.base_addr = t.base_addr ∧ s.top_addr = t.top_addr ∧
  mem_rel s.memory t.memory s.memaddrs ∧
  globals_rel s.globals t.globals ∧
  ALL_DISTINCT (MAP FST crep_code) ∧
  s.code = alist_to_fmap crep_code ∧
  t.code = fromAList (crep_to_loop$compile_prog c crep_code) ∧
  s.locals = FEMPTY ∧
  FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) ∧
  semantics s start <> Fail ==>
  semantics t lc = semantics s start
Proof
  simp [crep_sem_is_wrapper, loop_sem_is_wrapper]
  \\ rw []
  \\ ‘∃prog. ALOOKUP crep_code start = SOME ([],prog)’
    by (pop_assum mp_tac
        \\ qpat_x_assum ‘s.code = _’ mp_tac
        \\ rpt $ pop_assum kall_tac
        \\ simp[semantics_wrapper_def,AllCaseEqs()]
        \\ rpt strip_tac
        \\ pop_assum kall_tac
        \\ pop_assum $ qspec_then ‘1’ mp_tac
        \\ rw[crepSemTheory.evaluate_def,AllCaseEqs(),lookup_code_def]
        \\ Cases_on ‘ALOOKUP crep_code start’
        \\ gvs[]
        \\ metis_tac[FST,SND,PAIR])
  \\ match_mp_tac (semantics_wrapper_eq |> REWRITE_RULE [AND_IMP_INTRO] )
  \\ rw []
(*  \\ qpat_x_assum `_ <> Fail` kall_tac*)
  >- (
    fs []
    \\ drule_all mk_ctxt_code_imp_code_rel2
    \\ disch_then (qspec_then `c` mp_tac)
    \\ rw []
    \\ drule_then drule code_rel_evaluate_call_correct
    \\ disch_then (qspec_then `t with clock := k` mp_tac)
    \\ simp []
    \\ disch_then (drule_at (Pat `ALOOKUP _ _ = _`))
    \\ simp []
    \\ impl_tac
    >- (
      gs [find_lab_def, mk_ctxt_def]
      \\ simp [distinct_vars_def, ctxt_max_def]
      \\ CCONTR_TAC \\ fs []
    )
    \\ rw []
    \\ gs [find_lab_def, mk_ctxt_def]
    \\ qexists_tac `k'` \\ simp []
    \\ gvs[AllCaseEqs(),totoTheory.SPLIT_PAIRS]
    \\ fs [state_rel_def]
  )
  >- (
    fs [PAIR_MAP_EQ_UNCURRY, UNCURRY_eq_pair]
    \\ drule_then (qspec_then `k'` mp_tac) loopPropsTheory.evaluate_add_clock_eq
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ simp []
  )
  >- (
    fs [PAIR_MAP_EQ_UNCURRY, UNCURRY_eq_pair]
    \\ drule_then (qspec_then `k'` mp_tac) crepPropsTheory.evaluate_add_clock_eq
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ simp []
  )
  >- (
    gvs[totoTheory.SPLIT_PAIRS]
    \\ gvs[AllCaseEqs()]
    \\ simp [evaluate_io_mono_rephrases]
  )
  >- (
    gvs[totoTheory.SPLIT_PAIRS]
    \\ gvs[AllCaseEqs()]
    \\ simp [evaluate_io_mono_rephrases])
QED

(* first_name offset *)

Theorem crep_to_loop_compile_prog_lab_min:
  crep_to_loop$compile_prog c cprog = lprog ⇒
  EVERY (λprog. 60 ≤ FST prog) lprog
Proof
  gs[crep_to_loopTheory.compile_prog_def]>>
  gs[MAP2_MAP, EVERY_MEM]>>
  rpt strip_tac>>gvs[MEM_MAP,MEM_ZIP]>>
  pairarg_tac>>gs[crep_to_loopTheory.first_name_def]
QED

