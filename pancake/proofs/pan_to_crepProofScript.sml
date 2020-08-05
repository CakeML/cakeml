(*
  Correctness proof for --
*)

open preamble
     panSemTheory  panPropsTheory
     crepLangTheory crepSemTheory crepPropsTheory
     pan_commonTheory pan_commonPropsTheory
     listRangeTheory pan_to_crepTheory

val _ = new_theory "pan_to_crepProof";

val _ = set_grammar_ancestry  ["listRange", "crepProps", "pan_commonProps", "pan_to_crep"];


(* state relation *)

val s = ``(s:('a,'ffi) panSem$state)``

Definition excp_rel_def:
  excp_rel ctxt seids teids <=>
  FDOM seids =  FDOM ctxt.eid_map /\
  (∀e sh.
  FLOOKUP seids e = SOME sh ==>
  (?n. FLOOKUP ctxt.eid_map e = SOME (sh,n))) /\
  (!e e' sh sh' n n'.
    FLOOKUP ctxt.eid_map e = SOME (sh,n) /\
    FLOOKUP ctxt.eid_map e' = SOME (sh',n') /\
    n = n' ==> e = e') /\
  (IMAGE SND (FRANGE ctxt.eid_map) = set teids)
End

Definition ctxt_fc_def:
  ctxt_fc cvs em vs shs ns =
    <|var_nums := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
      code_vars := cvs; eid_map := em; max_var := list_max ns |>
End


Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ns. FLOOKUP ctxt.code_vars f = SOME (vshs, ns) /\
       ALL_DISTINCT ns /\
       let vs = MAP FST vshs;
           shs = MAP SND vshs;
           nctxt = ctxt_fc ctxt.code_vars ctxt.eid_map vs shs ns  in
       size_of_shape (Comb shs) = LENGTH ns /\
       FLOOKUP t_code f = SOME (ns, compile_prog nctxt prog)
End


Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi
End

Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals <=>
  no_overlap ctxt.var_nums /\ ctxt_max ctxt.max_var ctxt.var_nums /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃ns vs. FLOOKUP (ctxt.var_nums) vname = SOME (shape_of v, ns) ∧
    OPT_MMAP (FLOOKUP t_locals) ns = SOME vs ∧ flatten v = vs
End

Theorem code_rel_imp:
   code_rel ctxt s_code t_code ==>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog) ==>
  ?ns. FLOOKUP ctxt.code_vars f = SOME (vshs, ns) /\
       ALL_DISTINCT ns /\
       let vs = MAP FST vshs;
           shs = MAP SND vshs;
           nctxt = ctxt_fc ctxt.code_vars ctxt.eid_map vs shs ns  in
       size_of_shape (Comb shs) = LENGTH ns /\
       FLOOKUP t_code f = SOME (ns, compile_prog nctxt prog)
Proof
  fs [code_rel_def]
QED

Theorem code_rel_empty_locals:
  code_rel ctxt s.code t.code ==>
  code_rel ctxt (empty_locals s).code (empty_locals t).code
Proof
  fs [code_rel_def, empty_locals_def, panSemTheory.empty_locals_def]
QED

Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

Theorem compile_exp_val_rel:
  ∀s e v (t :('a, 'b) state) ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  MAP (eval t) es = MAP SOME (flatten v) ∧
  LENGTH es = size_of_shape sh ∧
  shape_of v = sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def, eval_def,
       panLangTheory.size_of_shape_def, shape_of_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [locals_rel_def] >>
   first_x_assum drule >>
   fs [] >> strip_tac >> fs [] >>
   fs [compile_exp_def] >> rveq >>
   fs [lookup_locals_eq_map_vars] >>
   fs [opt_mmap_eq_some] >>
   fs [MAP_MAP_o] >>
   metis_tac [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [flatten_def] >>
   fs [compile_exp_def] >> rveq >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >> fs [code_rel_def] >>
   cases_on ‘v1’ >>
   last_x_assum drule_all >> strip_tac >>
   fs [panLangTheory.size_of_shape_def, shape_of_def])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [MAP_MAP_o, MAP_FLAT, flatten_def] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs []
   >-  fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   rename [‘_ = SOME vs’] >>
   fs [] >>
   last_x_assum mp_tac >>
   impl_tac >-
    metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
    disch_then drule >> disch_then drule >>
    cases_on ‘compile_exp ct h’ >> fs [])
  >-
   (
   (* Field case *)
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   qpat_x_assum ‘_ = SOME (Struct _)’ kall_tac >>
   qpat_x_assum ‘compile_exp _ _ = _’ kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac
             [‘ct’,‘cexp’ ,‘sh’ , ‘es’, ‘t’, ‘s’, ‘index’, ‘vs’] >>
   Induct >> rpt gen_tac >- fs [] >>
   rewrite_tac [AND_IMP_INTRO] >>
   strip_tac >> fs [] >>
   cases_on ‘index’ >> fs []
   >- (
    fs [comp_field_def] >> rveq >>
    fs [MAP_TAKE, flatten_def] >>
    fs [panLangTheory.size_of_shape_def] >>
    fs [GSYM length_flatten_eq_size_of_shape] >>
    metis_tac [LENGTH_MAP, TAKE_LENGTH_APPEND]) >>
   fs [comp_field_def] >>
   last_x_assum drule >>
   ntac 4 (disch_then drule) >>
   fs [panLangTheory.size_of_shape_def, flatten_def] >>
   drule map_append_eq_drop >>
   fs [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   last_x_assum drule_all >>
   strip_tac >>
   fs [shape_of_def, panLangTheory.size_of_shape_def,flatten_def] >>
   rveq >> fs [] >> rveq >>
   fs [length_load_shape_eq_shape] >>
   drule mem_load_some_shape_eq >>
   strip_tac >> fs [] >>
   fs [MAP_EQ_EVERY2] >> fs [length_load_shape_eq_shape] >>
   rveq >> fs [GSYM length_flatten_eq_size_of_shape] >>
   fs [LIST_REL_EL_EQN] >>  fs [length_load_shape_eq_shape] >>
   rw [] >> fs [state_rel_def] >>
   drule mem_load_flat_rel >>
   disch_then drule >>
   strip_tac >> fs [] >>
   drule eval_load_shape_el_rel >>
   disch_then (qspecl_then [‘0w’, ‘t’,‘x0’] mp_tac) >> fs [] >>
   strip_tac >>
   fs [eval_def, OPT_MMAP_def] >>
   every_case_tac >> fs [] >> rveq >>
   fs[EVERY_DEF] >> cases_on ‘h’ >> fs [] >>
   fs [wordLangTheory.word_op_def] >> rveq >>
   qpat_x_assum ‘mem_load _ _ = _’ (mp_tac o GSYM) >>
   strip_tac >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   first_x_assum drule_all >> fs [shape_of_def] >>
   strip_tac >> fs [] >> rveq >>
   cases_on ‘cexp’ >> fs [panLangTheory.size_of_shape_def, flatten_def] >> rveq >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [eval_def, state_rel_def])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   ‘~MEM [] (MAP FST (MAP (λa. compile_exp ct a) es))’ by (
     CCONTR_TAC >> fs [] >> rveq >>
     fs [MEM_MAP] >> rveq >>
     drule opt_mmap_mem_func >>
     disch_then drule >>
     strip_tac >> fs [] >>
     rename1 ‘MEM e es’ >>
     cases_on ‘compile_exp ct e’ >> fs [] >>
     ‘shape_of m = One’ by (
       ‘MEM m ws’ by (
         drule opt_mmap_mem_defined >>
         strip_tac >> res_tac >> fs []) >>
       qpat_x_assum ‘EVERY _ ws’ mp_tac >>
       fs [EVERY_MEM] >>
       disch_then (qspec_then ‘m’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [shape_of_def]) >>
     last_x_assum drule_all >>
     strip_tac >> rveq >> rfs [panLangTheory.size_of_shape_def]) >>
     fs [] >> rveq >>
     fs [panLangTheory.size_of_shape_def, shape_of_def] >>
     fs [flatten_def, eval_def, MAP_MAP_o] >>
     ‘OPT_MMAP (λa. eval t a)
      (MAP (HD ∘ FST ∘ (λa. compile_exp ct a)) es) =
      OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es’ by (
       ho_match_mp_tac IMP_OPT_MMAP_EQ >>
       fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
       rw [] >>
       drule opt_mmap_length_eq >>
       strip_tac >> fs [] >>
       first_x_assum (qspec_then ‘EL n es’ mp_tac) >>
       impl_tac >- metis_tac [EL_MEM] >>
       drule opt_mmap_el >> fs [] >>
       disch_then drule >>
       strip_tac >> fs [] >>
       disch_then drule >>
       disch_then drule >>
       disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                                ‘SND(compile_exp ct (EL n es))’] mp_tac) >>
       fs [] >>
       strip_tac >>
       fs [EVERY_EL] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [] >>
       qpat_x_assum ‘LENGTH es = LENGTH _’ (mp_tac o GSYM) >>
       strip_tac >> fs [] >>
       drule (INST_TYPE [``:'a``|->``:'a panLang$exp``,
                         ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
       disch_then (qspec_then ‘(HD ∘ FST ∘ (λa. compile_exp ct a))’ mp_tac) >>
       strip_tac >> fs [] >>
       fs [flatten_def, v2word_def] >> rveq) >>
     fs [] >>
     ‘OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es =
      SOME (MAP v2word ws)’ by (
       ho_match_mp_tac opt_mmap_opt_map >> fs []) >>
     fs [EVERY_MAP, MAP_MAP_o] >>
     ‘∀x. (λw. case w of ValWord v6 => T | ValLabel v7 => F | Struct v3 => F) x ==>
      (λx. case v2word x of Word v2 => T | Label v3 => F) x’ by (
       rw [] >> every_case_tac >> fs [v2word_def]) >>
     drule MONO_EVERY >>
     disch_then (qspec_then ‘ws’ mp_tac) >> fs [] >>
     strip_tac >> fs [flatten_def] >>
     fs [GSYM MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘word_op op ins’ >>
     qmatch_asmsub_abbrev_tac ‘word_op op ins'’ >>
     ‘ins = ins'’ by (
       unabbrev_all_tac >> fs [MAP_EQ_EVERY2] >>
       fs [LIST_REL_EL_EQN] >>
       rw [] >>
       fs [EVERY_EL] >> (* for some reason, drule EL_MAP is not being inst. properly*)
       ‘EL n (MAP v2word ws) = v2word (EL n ws)’ by (
         match_mp_tac EL_MAP >> fs []) >>
       fs [] >>
       last_x_assum (qspec_then ‘n’ mp_tac) >>
       fs [] >> TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [v2word_def]) >>
     unabbrev_all_tac >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
   (* open compile_exp *)
   fs [compile_exp_def] >>
   cases_on ‘compile_exp ct e’ >>
   cases_on ‘compile_exp ct e'’ >>
   first_x_assum drule_all >>
   first_x_assum drule_all >>
   strip_tac >> strip_tac >>
   fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   fs [eval_def] >>
   every_case_tac >> fs [] >> EVAL_TAC) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
  fs [compile_exp_def] >>
  cases_on ‘compile_exp ct e’ >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
  rveq >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
  fs [eval_def] >>  every_case_tac >>
  fs [panLangTheory.size_of_shape_def, shape_of_def]
QED


Definition globals_lookup_def:
  globals_lookup t v =
    OPT_MMAP (FLOOKUP t.globals)
             (GENLIST (λx. n2w x) (size_of_shape (shape_of v)))
End


val gen_goal =
  ``λ comp (prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ code_rel ctxt s.code t.code /\
      excp_rel ctxt s.eshapes t.eids /\
      locals_rel ctxt s.locals t.locals ⇒
      ∃res1 t1. evaluate (comp ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧ code_rel ctxt s1.code t1.code /\
      excp_rel ctxt s1.eshapes t1.eids /\
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME Break => res1 = SOME Break /\
                       locals_rel ctxt s1.locals t1.locals
       | SOME Continue => res1 = SOME Continue /\
                       locals_rel ctxt s1.locals t1.locals
       | SOME (Return v) =>
          (size_of_shape (shape_of v) = 0 ==> res1 = SOME (Return (Word 0w))) ∧
          (size_of_shape (shape_of v) = 1 ==> res1 = SOME (Return (HD(flatten v)))) ∧
          (1 < size_of_shape (shape_of v) ==>
               res1 = SOME (Return (Word 0w)) /\ globals_lookup t1 v = SOME (flatten v) ∧
               size_of_shape (shape_of v) <= 32)
       | SOME (Exception eid v) =>
         (case FLOOKUP ctxt.eid_map eid of
           | SOME (sh,n) => res1 = SOME (Exception n) ∧
             (1 <= size_of_shape (shape_of v) ==>
                  globals_lookup t1 v = SOME (flatten v) ∧
                  size_of_shape (shape_of v) <= 32)
           | NONE => F)
       | SOME TimeOut => res1 = SOME TimeOut
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | _ => F``

local
  val goal = beta_conv ``^gen_goal pan_to_crep$compile_prog``
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_prog_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
  val fgoal = beta_conv ``^gen_goal pan_to_crep$compile``
end



Theorem compile_Skip_Break_Continue:
  ^(get_goal "compile_prog _ panLang$Skip") /\
  ^(get_goal "compile_prog _ panLang$Break") /\
  ^(get_goal "compile_prog _ panLang$Continue")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_prog_def] >> rveq >> fs []
QED


Theorem compile_Tick:
  ^(get_goal "compile_prog _ panLang$Tick")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_prog_def] >> rveq >> fs [] >>
  every_case_tac >> fs [panSemTheory.empty_locals_def, empty_locals_def,
                        panSemTheory.dec_clock_def, dec_clock_def] >>
  rveq >> fs [state_rel_def]
QED


Theorem locals_rel_lookup_ctxt:
  locals_rel ctxt lcl lcl' /\
  FLOOKUP lcl vr = SOME v ==>
  ?ns. FLOOKUP ctxt.var_nums vr = SOME (shape_of v,ns) /\
   LENGTH ns = LENGTH (flatten v) /\
   OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v)
Proof
  rw [locals_rel_def] >>
  metis_tac [opt_mmap_length_eq]
QED


Theorem eval_nested_assign_distinct_eq:
  !es ns t ev vs.
  MAP (eval t) es = MAP SOME ev /\
  OPT_MMAP (FLOOKUP t.locals) ns = SOME vs /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ==>
  evaluate (nested_seq (MAP2 Assign ns es),t) =
      (NONE, t with locals := t.locals |++ ZIP (ns, ev))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM,
       state_component_equality]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [MAP_EQ_CONS] >>
  rveq >> rfs [] >>
  fs [OPT_MMAP_def] >>
  rveq >> rfs [] >>
  rveq >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘FLOOKUP t.locals n = SOME nv’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  drule opt_mmap_flookup_update >>
  disch_then drule >>
  disch_then (qspec_then ‘v’ assume_tac) >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule >>
  fs [state_accfupds] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  fs [FUPDATE_LIST_THM]
QED


Theorem eval_nested_decs_seq_res_var_eq:
  !es ns t ev p.
  MAP (eval t) es = MAP SOME ev /\
  LENGTH ns = LENGTH es /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns ==>
  let (q,r) = evaluate (p, t with locals := t.locals |++ ZIP (ns, ev)) in
  evaluate (nested_decs ns es p, t) =
  (q, r with locals :=
        FOLDL res_var r.locals (ZIP (ns, MAP (FLOOKUP t.locals) ns)))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [nested_decs_def, FUPDATE_LIST_THM] >>
   cases_on ‘t’ >> cases_on ‘r’ >>
   fs [state_component_equality, state_locals_fupd]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_decs_def] >>
  fs [evaluate_def] >>
  fs [MAP_EQ_CONS] >>
  pairarg_tac >> fs [] >>
  rveq >> rfs [] >>
  pairarg_tac >> fs [] >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘~MEM n t'’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [FUPDATE_LIST_THM] >>
  fs [state_component_equality] >>
  ‘MAP (FLOOKUP (t.locals |+ (n,v))) t' =
   MAP (FLOOKUP t.locals) t'’ by
    metis_tac [MAP_EQ_f, FLOOKUP_UPDATE] >>
  fs [] >>
  pop_assum kall_tac >>
  qpat_x_assum ‘~MEM n t'’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘r’, ‘n’,‘t’, ‘t'’] >>
  Induct >> rw [] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  disch_then (qspec_then ‘r with locals :=
                          res_var r.locals (h,FLOOKUP t.locals h)’ mp_tac) >>
  fs [] >>
  metis_tac [res_var_commutes]
QED

Theorem mem_comp_field:
  !sh i e shp ce es vs.
   i < LENGTH vs /\
  LENGTH e = size_of_shape (shape_of (Struct vs)) /\
  comp_field i sh e = (es,shp) /\
  Comb sh = shape_of (Struct vs) /\
  MEM ce es ==> MEM ce e
Proof
  Induct >> rw [comp_field_def] >>
  fs [] >> rveq
  >- fs [shape_of_def]
  >- (
   cases_on ‘vs’ >> fs [] >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >> fs [] >>
   ‘size_of_shape (shape_of h') <= LENGTH e’ by DECIDE_TAC >>
   metis_tac [MEM_TAKE]) >>
  cases_on ‘vs’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >>
  rveq >> fs [] >>
  first_x_assum (qspecl_then  [‘i-1’, ‘(DROP (size_of_shape (shape_of h')) e)’,
                               ‘shp’, ‘ce’, ‘es’, ‘t’] mp_tac) >>
  fs [] >>
  metis_tac [MEM_DROP_IMP]
QED


Theorem eval_var_cexp_present_ctxt:
  ∀(s :('a, 'b) panSem$state) e v (t :('a, 'b) state) ct es sh.
  state_rel s t /\
  eval s e = SOME v /\
  code_rel ct s.code t.code /\
  locals_rel ct s.locals t.locals /\
  compile_exp ct e = (es,sh) ==>
  (∀n. MEM n (FLAT (MAP var_cexp es)) ==>
   ?v shp ns. FLOOKUP ct.var_nums v = SOME (shp,ns)  /\
       MEM n ns)
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def] >>
   fs [CaseEq "option"] >> rveq
   >- fs [var_cexp_def] >>
   cases_on ‘v'’ >> fs [] >>
   rveq >>
   fs [MEM_MAP, MEM_FLAT] >>
   rveq >>
   fs [var_cexp_def] >>
   metis_tac [])
  >- (
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [MAP_MAP_o, MAP_FLAT] >>
   fs [o_DEF] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs [] >>
   rpt gen_tac >> strip_tac >>
   fs [OPT_MMAP_def] >>
   strip_tac >>
   strip_tac >>
   rveq >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
   disch_then drule >>
   cases_on ‘compile_exp ct h’ >> fs [] >>
   strip_tac >>
   strip_tac >>
   metis_tac [])
  >- (
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq
   >- rw [var_cexp_def] >>
   rpt gen_tac >> strip_tac >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >>
   first_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   fs [] >> rveq >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >>
    qexists_tac ‘y’ >> fs [] >>
    drule compile_exp_val_rel >>
    disch_then drule_all >>
    strip_tac >> fs [] >> rveq >>
    metis_tac [mem_comp_field]) >>
   fs [])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   rpt gen_tac >>
   strip_tac >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [] >>
   rveq >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   rveq >> fs [] >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >>
    qexists_tac ‘h’ >> fs [] >>
    metis_tac [var_exp_load_shape]) >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   cases_on ‘cexp’ >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   reverse (cases_on ‘shape’) >> fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   rw [] >>
   fs [var_cexp_def] >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   FULL_CASE_TAC >>
   fs [] >> rveq
   >- (rw [] >> fs [MEM_FLAT, MEM_MAP, var_cexp_def]) >>
   fs [var_cexp_def, ETA_AX] >>
   rveq >>
   rw [] >>
   ntac 4 (pop_assum mp_tac) >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   ntac 3 (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘n’,‘ws’, ‘x’, ‘es’] >>
   Induct
   >- (
    rw [] >> fs [cexp_heads_def, var_cexp_def] >>
    rveq  >> fs [MAP, FLAT]) >>
   rpt gen_tac >> strip_tac >>
   fs [OPT_MMAP_def] >>
   rpt strip_tac >>
   rveq >>
   fs [cexp_heads_def] >>
   fs [CaseEq "list", CaseEq "option"] >>
   rveq >>
   fs [MAP, MEM_FLAT, MEM_MAP] >> rveq
   >- (
    first_x_assum (qspec_then ‘h’ mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then (qspec_then ‘ct’ mp_tac) >>
    cases_on ‘compile_exp ct h’ >> fs []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   impl_tac
   >- (
    qexists_tac ‘var_cexp y’ >>
    fs [] >> metis_tac []) >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [CaseEq "list", CaseEq "option"] >>
   rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
   rw []
   >- (
    last_x_assum drule >>
    disch_then (qspec_then ‘ct’ mp_tac) >>
    cases_on ‘compile_exp ct e’ >> fs []) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e'’ >> fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
      CaseEq "word_lab"] >> rveq >>
  fs [compile_exp_def] >> rveq >>
  fs [CaseEq "list", CaseEq "option"] >>
  rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
  rw [] >> last_x_assum drule >>
  disch_then (qspec_then ‘ct’ mp_tac) >>
  cases_on ‘compile_exp ct e’ >> fs []
QED


Theorem compile_Assign:
  ^(get_goal "compile_prog _ (panLang$Assign _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  rename [‘Assign vr e’] >>
  fs [panSemTheory.evaluate_def, is_valid_value_def] >>
  fs [CaseEq "option", CaseEq "bool"] >> rveq >> fs [] >>
  rename [‘eval _ e = SOME ev’] >>
  rename [‘FLOOKUP _ vr = SOME v’] >>
  (* open compiler def *)
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  drule locals_rel_lookup_ctxt >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  fs [length_flatten_eq_size_of_shape] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   ‘ALL_DISTINCT ns’
     by metis_tac [locals_rel_def, no_overlap_def] >>
   drule eval_nested_assign_distinct_eq >>
   disch_then drule >>
   strip_tac >> fs [] >>
   conj_tac
   >- fs [state_rel_def] >>
   fs [locals_rel_def] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   cases_on ‘vr = vname’ >> fs [] >> rveq
   >- (
    pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
    fs [] >> rveq >>
    match_mp_tac opt_mmap_some_eq_zip_flookup >>
    fs [] >>
    metis_tac [all_distinct_flookup_all_distinct,
               length_flatten_eq_size_of_shape]) >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   rfs [] >>
   drule no_overlap_flookup_distinct >>
   disch_then drule_all >>
   strip_tac >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  (* non-distinct Assign  *)
  qmatch_goalsub_abbrev_tac ‘nested_decs temps es _’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  ‘ALL_DISTINCT ns’ by metis_tac [locals_rel_def, no_overlap_def] >>
  ‘distinct_lists ns temps’ by (
    unabbrev_all_tac >>
    once_rewrite_tac [distinct_lists_commutes] >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten ev’,
                          ‘nested_seq (MAP2 Assign ns (MAP Var temps))’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  ‘MAP (eval (t with locals := t.locals |++ ZIP (temps,flatten ev)))
   (MAP Var temps) = MAP SOME (flatten ev)’ by (
    fs [MAP_MAP_o, MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >> rfs [] >>
    ‘n < LENGTH temps’ by (
      unabbrev_all_tac >> fs [MAP_MAP_o, MAP_EQ_EVERY2]>>
      metis_tac []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
    disch_then (qspec_then ‘Var’ assume_tac) >> fs [] >>
    fs [eval_def] >>
    metis_tac [update_eq_zip_flookup]) >>
  drule eval_nested_assign_distinct_eq >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  disch_then (qspec_then ‘flatten v’ mp_tac) >>
  impl_tac
  >- (
   fs [map_var_cexp_eq_var] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  rveq >>
  fs [state_rel_def] >>
  fs [locals_rel_def] >>
  rw [] >> fs [] >>
  (* writing in this style for druling below *)
  ‘DISJOINT (set (MAP FST (ZIP (temps,flatten ev))))
   (set (MAP FST (ZIP (ns,flatten ev))))’ by (
    ‘LENGTH ns = LENGTH (flatten ev)’ by
      fs [length_flatten_eq_size_of_shape] >>
    fs [GSYM length_flatten_eq_size_of_shape, MAP_ZIP] >>
    fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
    metis_tac []) >>
  drule FUPDATE_LIST_APPEND_COMMUTES >>
  disch_then (qspec_then ‘t.locals’ assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  cases_on ‘vr = vname’ >> fs [] >> rveq
  >- (
   pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
   fs [] >> rveq >>
   fs [opt_mmap_eq_some] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten ev’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape] >>
   strip_tac >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >> rfs [] >>
   ‘n < LENGTH ns’ by metis_tac [] >>
   metis_tac [update_eq_zip_flookup]) >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  rfs [] >>
  fs [opt_mmap_eq_some] >>
  ‘distinct_lists temps ns'’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``]
         flookup_res_var_zip_distinct) >>
  disch_then (qspecl_then [‘flatten ev’,
                           ‘MAP (FLOOKUP t.locals) temps’,
                           ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule no_overlap_flookup_distinct >>
  disch_then drule_all >>
  strip_tac >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >> rfs [] >>
  qpat_x_assum ‘LENGTH _ = LENGTH _’ (assume_tac o GSYM) >>
  fs [] >>
  last_x_assum drule >> strip_tac >>
  ‘~MEM (EL n ns') ns’ by (
    fs [Once distinct_lists_commutes] >>
    fs [distinct_lists_def, EVERY_MEM, EL_MEM]) >>
  metis_tac [flookup_fupdate_zip_not_mem]
QED

Theorem not_mem_context_assigned_mem_gt:
  !ctxt p x.
   ctxt_max ctxt.max_var ctxt.var_nums /\
   (!v sh ns'. FLOOKUP ctxt.var_nums v = SOME (sh, ns') ==> ~MEM x ns') ∧
   x <= ctxt.max_var  ==>
   ~MEM x (assigned_vars (compile_prog ctxt p))
Proof
  ho_match_mp_tac compile_prog_ind >> rw []
  >- fs [compile_prog_def, assigned_vars_def]
  >- (
   fs [compile_prog_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   qmatch_goalsub_abbrev_tac ‘compile_prog nctxt p’ >>
   disch_then (qspec_then ‘compile_prog nctxt p’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   last_x_assum match_mp_tac >>
   rename [‘(vname,sh,dvs)’] >>
   conj_tac
   >- (
    fs [ctxt_max_def] >>
    rw [] >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs [] >> rveq >> res_tac >> fs [] >>
    fs [Abbr ‘dvs’, MEM_GENLIST]) >>
   rw [] >>
   fs [FLOOKUP_UPDATE] >>
   FULL_CASE_TAC >> rveq >> fs [] >> res_tac >> fs [])
  >- (
   fs [compile_prog_def, assigned_vars_def] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   FULL_CASE_TAC >> FULL_CASE_TAC >> fs []
   >- (
    FULL_CASE_TAC >> fs [assigned_vars_def] >>
    drule nested_seq_assigned_vars_eq >>
    fs [] >> res_tac >> fs []) >>
   FULL_CASE_TAC >> fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (MAP2 Assign r (MAP Var dvs))’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   ‘LENGTH r = LENGTH (MAP Var dvs)’ by fs [Abbr ‘dvs’, LENGTH_GENLIST] >>
   drule nested_seq_assigned_vars_eq >>
   fs [] >> res_tac >> fs [])
  >- (
   fs [compile_prog_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   pairarg_tac >> fs [] >>
   TOP_CASE_TAC >> fs [assigned_vars_def] >>
   fs [nested_decs_def] >>
   fs [assigned_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (stores (Var (ctxt.max_var + 1))
                                       (MAP Var dvs) 0w)’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   fs [assigned_vars_seq_store_empty]) >>
  TRY (fs [compile_prog_def, assigned_vars_def] >> every_case_tac >>
       fs [assigned_vars_def] >> metis_tac [] >> NO_TAC)
  >- (
   fs [compile_prog_def] >>
   pairarg_tac >> fs [] >>
   ntac 4 (TOP_CASE_TAC >> fs [assigned_vars_def]) >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (store_globals 0w (MAP Var dvs))’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   fs [assigned_vars_store_globals_empty])
  >- (
   fs [compile_prog_def] >>
   pairarg_tac >> fs [] >>
   ntac 4 (TOP_CASE_TAC >> fs [assigned_vars_def]) >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (store_globals 0w (MAP Var dvs))’ assume_tac) >>
   fs [] >>
   pop_assum kall_tac >>
   conj_asm1_tac
   >- (
    fs [Abbr ‘dvs’] >> fs[MEM_GENLIST]) >>
   fs [assigned_vars_store_globals_empty]) >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  rpt (TOP_CASE_TAC >> fs []) >>
  TRY (fs [assigned_vars_def]) >>
  TRY (
  cases_on ‘q’ >>
  fs [ret_var_def] >>
  TRY (TOP_CASE_TAC) >>
  fs [] >>
  TRY (
  fs [ret_hdl_def] >>
  cases_on ‘r’ >>
  fs [assigned_vars_def, wrap_rt_def,
      CaseEq "option", CaseEq "prod", CaseEq "shape",
      CaseEq "list"] >>
  res_tac >> fs []) >>
  TOP_CASE_TAC >>
  fs [assign_ret_def, nested_seq_def, assigned_vars_def] >>
  ‘LENGTH (h'::t') = LENGTH (load_globals 0w (SUC (LENGTH t')))’ by
    fs [GSYM length_load_globals_eq_read_size] >>
  drule nested_seq_assigned_vars_eq >>
  fs [] >> strip_tac >>
  res_tac >> fs [])
  >- (
   reverse conj_tac
   >- (
    first_x_assum match_mp_tac >>
    fs [] >> rw [] >>
    res_tac >> fs []) >>
   fs [exp_hdl_def] >>
   TOP_CASE_TAC >> fs [] >>
   fs [assigned_vars_def] >>
   TOP_CASE_TAC >> fs [] >>
   ‘LENGTH r' = LENGTH (load_globals 0w (LENGTH r'))’ by
     fs [GSYM length_load_globals_eq_read_size] >>
   drule nested_seq_assigned_vars_eq >>
   fs [] >> strip_tac >>
   res_tac >> fs []) >>
  cases_on ‘q’ >>
  fs [ret_var_def] >>
  TRY (TOP_CASE_TAC) >>
  fs [] >>
  TRY (
  fs [ret_hdl_def] >>
  cases_on ‘r’ >>
  fs [assigned_vars_def, wrap_rt_def,
      CaseEq "option", CaseEq "prod", CaseEq "shape",
      CaseEq "list"] >>
  res_tac >> fs []) >>
  TRY TOP_CASE_TAC >> fs [] >>
  fs [assign_ret_def, nested_seq_def, assigned_vars_def] >>
  fs [exp_hdl_def] >>
  rpt TOP_CASE_TAC >> fs [] >>
  fs [assigned_vars_def] >>
  TRY (
  ‘LENGTH r = LENGTH (load_globals 0w (LENGTH r))’ by
    fs [GSYM length_load_globals_eq_read_size]) >>
  TRY (
  ‘LENGTH (h'::t') = LENGTH (load_globals 0w (SUC (LENGTH t')))’ by
    fs [GSYM length_load_globals_eq_read_size]) >>
  imp_res_tac nested_seq_assigned_vars_eq >>
  fs [] >> strip_tac >>
  res_tac >> fs []
QED

Theorem rewritten_context_unassigned:
 !p nctxt v ctxt ns nvars sh sh'.
  nctxt = ctxt with
   <|var_nums := ctxt.var_nums |+ (v,sh,nvars);
     max_var  := ctxt.max_var + size_of_shape sh|> /\
  FLOOKUP ctxt.var_nums v = SOME (sh',ns) /\
  no_overlap ctxt.var_nums /\
  ctxt_max ctxt.max_var ctxt.var_nums /\
  no_overlap nctxt.var_nums ∧
  ctxt_max nctxt.max_var nctxt.var_nums /\
  distinct_lists nvars ns ==>
  distinct_lists ns (assigned_vars (compile_prog nctxt p))
Proof
  rw [] >> fs [] >>
  fs [distinct_lists_def] >>
  rw [] >>
  fs [EVERY_MEM] >> rw []>>
  CCONTR_TAC >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘compile_prog nctxt p’ >>
  assume_tac not_mem_context_assigned_mem_gt >>
  pop_assum (qspecl_then [‘nctxt’, ‘p’, ‘x’] mp_tac) >>
  impl_tac
  >- (
   unabbrev_all_tac >> fs[context_component_equality] >>
   rw [FLOOKUP_UPDATE]  >- metis_tac []
   >- (
    fs [no_overlap_def] >>
    first_x_assum (qspecl_then [‘v’, ‘v'’] mp_tac) >>
    fs [FLOOKUP_UPDATE] >>
    metis_tac [IN_DISJOINT]) >>
   fs [ctxt_max_def] >>
   res_tac >> fs [] >>
   DECIDE_TAC) >>
  fs []
QED

Theorem ctxt_max_el_leq:
  ctxt_max ctxt.max_var ctxt.var_nums /\
  FLOOKUP ctxt.var_nums v = SOME (sh,ns) /\
  n < LENGTH ns ==> EL n ns <= ctxt.max_var
Proof
  rw [ctxt_max_def] >>
  first_x_assum drule >>
  disch_then (qspec_then ‘EL n ns’ assume_tac) >>
  drule EL_MEM >>
  fs []
QED


Theorem compile_Dec:
  ^(get_goal "compile_prog _ (panLang$Dec _ _ _)")
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [CaseEq "option"] >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >>
  rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  qmatch_goalsub_abbrev_tac ‘nested_decs nvars es _’ >>
  ‘ALL_DISTINCT nvars ∧ LENGTH nvars = LENGTH es’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST]) >>
  ‘distinct_lists nvars (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘nvars’, ‘t’,
                          ‘flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  last_x_assum (qspecl_then [‘t with locals := t.locals |++ ZIP (nvars,flatten value)’,
                             ‘ctxt with <|var_nums := ctxt.var_nums |+ (v,shape_of value,nvars);
                               max_var := ctxt.max_var + size_of_shape (shape_of value)|>’ ]
                mp_tac) >>
  impl_tac
  >- (
   fs [state_rel_def] >>
   conj_tac >- fs [code_rel_def] >>
   conj_tac >- (fs [excp_rel_def] >> rw [] >> last_x_assum drule_all >> fs []) >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [no_overlap_def] >>
    conj_tac
    >- (
     rw [] >>
     cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >>
     metis_tac []) >>
    rw [] >>
    cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
    rveq
    >- (
     qsuff_tac ‘distinct_lists nvars ys’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    qsuff_tac ‘distinct_lists nvars xs’
    >- (
     fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
     metis_tac []) >>
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    fs [ctxt_max_def] >> res_tac >> fs []) >>
   conj_tac
   >- (
    fs [ctxt_max_def]  >> rw [] >>
    cases_on ‘v = v'’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rw [] >>
   cases_on ‘v = vname’ >>  fs [FLOOKUP_UPDATE] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``]
           opt_mmap_some_eq_zip_flookup) >>
    disch_then (qspecl_then [‘t.locals’, ‘flatten v'’] mp_tac) >>
    fs [length_flatten_eq_size_of_shape]) >>
   res_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten value’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape])  >>
  strip_tac >> unabbrev_all_tac >> fs [] >> rveq >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac >- fs [code_rel_def] >>
  conj_tac >- (fs [excp_rel_def] >> rw [] >> last_x_assum drule_all >> fs []) >>
  cases_on ‘res = NONE ∨ res = SOME Continue ∨ res = SOME Break’ >>
  fs [] >> rveq >> rfs [] >>
  TRY
  (qmatch_goalsub_abbrev_tac ‘ZIP (nvars, _)’ >>
   qmatch_asmsub_abbrev_tac ‘locals_rel nctxt st.locals r.locals’ >>
   rewrite_tac [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   rw [] >>
   reverse (cases_on ‘v = vname’) >> fs [] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:mlstring``,
                      ``:'b``|->``:'a v``] flookup_res_var_diff_eq_org) >>
    disch_then (qspecl_then [‘FLOOKUP s.locals v’, ‘st.locals’] (mp_tac o GSYM)) >>
    fs [] >> strip_tac >>
    fs [locals_rel_def] >> rfs [] >>
    first_x_assum drule_all >> strip_tac >> fs [] >>
    fs [Abbr ‘nctxt’] >>
    fs [FLOOKUP_UPDATE] >> rfs [] >>
    fs [opt_mmap_eq_some] >>
    ‘distinct_lists nvars ns’ by (
      fs [Abbr ‘nvars’] >> ho_match_mp_tac genlist_distinct_max >>
      rw [] >> fs [ctxt_max_def] >> res_tac >> fs []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``] flookup_res_var_distinct) >>
    disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                             ‘r.locals’] mp_tac) >>
    fs [LENGTH_MAP]) >>
   drule flookup_res_var_some_eq_lookup >>
   strip_tac >>
   qpat_x_assum ‘locals_rel ctxt s.locals t.locals’ mp_tac >>
   rewrite_tac [locals_rel_def] >>
   strip_tac >> fs [] >>
   pop_assum drule  >>
   strip_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   fs [opt_mmap_eq_some] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_distinct) >>
   disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                            ‘r.locals’] mp_tac) >>
   fs [LENGTH_MAP] >>
   strip_tac >>
   pop_assum kall_tac >>
   assume_tac rewritten_context_unassigned >>
   fs [] >>
   first_x_assum drule >>
   disch_then (qspecl_then [‘prog’, ‘nvars’,
                            ‘shape_of value’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    conj_tac
    >- (
     fs [no_overlap_def] >>
     rw []
     >- (cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >> metis_tac []) >>
     rw [] >>
     cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
     rveq
     >- (
      qsuff_tac ‘distinct_lists nvars ys’
      >- (
       fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
       metis_tac []) >>
      unabbrev_all_tac >>
      ho_match_mp_tac genlist_distinct_max >>
      rw [] >>
      fs [ctxt_max_def] >> res_tac >> fs []) >>
     qsuff_tac ‘distinct_lists nvars xs’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    fs [ctxt_max_def] >> rw [] >>
    cases_on ‘v = v''’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rewrite_tac [distinct_lists_def] >>
   strip_tac >> fs [EVERY_MEM] >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   first_x_assum (qspec_then ‘EL n ns’ mp_tac) >>
   fs [EL_MEM] >>
   strip_tac >>
   drule unassigned_vars_evaluate_same >> fs [] >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [] >>
   ‘LENGTH nvars = LENGTH (flatten value)’ by (
     unabbrev_all_tac >> fs [LENGTH_GENLIST]) >>
   drule flookup_fupdate_zip_not_mem >>
   fs [Once distinct_lists_commutes] >>
   disch_then (qspecl_then [‘t.locals’, ‘EL n ns’] mp_tac) >>
   fs [distinct_lists_def, EVERY_MEM] >>
   impl_tac >- metis_tac [EL_MEM] >> fs [] >> NO_TAC) >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >> fs [globals_lookup_def]
QED



Theorem compile_Store:
  ^(get_goal "compile_prog _ (panLang$Store _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘stores (Var ad) (MAP Var temps) _’ >>
  ‘ALL_DISTINCT (ad::temps) ∧ LENGTH (ad::temps) = LENGTH (h::es)’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST, MEM_GENLIST]) >>
  ‘distinct_lists (ad::temps) (FLAT (MAP var_cexp (h::es)))’ by (
    unabbrev_all_tac >> fs [MAP] >>
    ‘ctxt.max_var + 1:: GENLIST (λx. SUC x + (ctxt.max_var + 1)) (LENGTH es) =
     GENLIST (λx. SUC x + ctxt.max_var) (SUC(LENGTH es))’ by (
     fs [GENLIST_CONS, o_DEF] >> fs [GENLIST_FUN_EQ])>>
    fs [] >> pop_assum kall_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw []
    >- (
     qpat_x_assum ‘compile_exp _ src = (_,_)’ mp_tac >>
     qpat_x_assum ‘eval _ src = _’ mp_tac >>
     drule eval_var_cexp_present_ctxt >>
     ntac 3 (disch_then drule) >>
     fs [MAP] >> disch_then drule >>
     rw [] >> fs [] >>
     rfs [] >>
     fs [locals_rel_def, ctxt_max_def] >>
     first_x_assum drule >> fs []) >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘h::es’, ‘ad::temps’, ‘t’,
                          ‘Word addr::flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  fs [state_rel_def] >>
  fs [Abbr ‘p’] >>
  assume_tac evaluate_seq_stores_mem_state_rel >>
  pop_assum (qspecl_then [‘temps’, ‘flatten value’, ‘ad’ ,‘0w’, ‘t’,
                          ‘q’, ‘r’, ‘addr’, ‘m’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule evaluate_seq_stroes_locals_eq >> strip_tac >> fs [] >>
  rfs [] >>
  fs [GSYM length_flatten_eq_size_of_shape] >>
  cases_on ‘FLOOKUP t.locals ad’
  >- (
   fs [res_var_def] >>
   fs [FUPDATE_LIST_THM] >>
   ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
     drule MAP_ZIP >>
     strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘Word addr’, ‘t.locals’] assume_tac) >>
   fs []  >>
   qpat_x_assum ‘~MEM ad temps’ assume_tac >>
   drule_all domsub_commutes_fupdate >>
   disch_then (qspec_then ‘t.locals’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [flookup_thm] >>
   drule DOMSUB_NOT_IN_DOM >> strip_tac >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []) >>
  fs [res_var_def] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
    drule MAP_ZIP >>
    strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘x’, ‘t.locals |+ (ad,Word addr)’] assume_tac o GSYM) >>
   fs [flookup_thm] >>
   drule_all FUPDATE_ELIM >>
   strip_tac >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []
QED

Theorem compile_StoreByte:
  ^(get_goal "compile_prog _ (panLang$StoreByte _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  TOP_CASE_TAC >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  fs [flatten_def] >> rveq >>
  fs [evaluate_def] >> TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [state_rel_def]
QED


Theorem compile_exp_not_mem_load_glob:
  ∀s e v (t :('a, 'b) state) ct es sh ad.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
  locals_rel ct s.locals t.locals ∧
  compile_exp ct e = (es, sh) ==>
  ~MEM (LoadGlob ad) (FLAT (MAP exps es))
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def, compile_exp_def] >> rveq >>
   fs [exps_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >>
   CCONTR_TAC >> fs [] >>
   FULL_CASE_TAC >> fs [] >> rveq >> fs [exps_def] >>
   FULL_CASE_TAC >> fs [] >> rveq >>
   fs [MEM_FLAT, MEM_MAP] >> rveq >> fs [exps_def])
  >- (
   fs [compile_exp_def] >>
   CCONTR_TAC >> fs [] >>
   rveq >> fs [exps_def])
  >- (
   rpt strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> rw [] >>
   fs [OPT_MMAP_def] >> rveq
   >- (
    CCONTR_TAC >> fs [] >>
    cases_on ‘compile_exp ct h’ >> fs [] >>
    first_x_assum (qspec_then ‘h’ assume_tac) >> fs [] >>
    metis_tac []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   strip_tac >> fs [] >> rfs [] >> rveq >>
   last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >> rfs [] >>
   disch_then drule >> disch_then drule >>
   cases_on ‘FST (compile_exp ct h)’ >> fs [] >> rveq >>
   cases_on ‘compile_exp ct h’ >> fs [])
  >- (
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >- fs [exps_def] >>
   first_x_assum drule >> disch_then drule >>
   disch_then drule >>  disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >>
   CCONTR_TAC >> fs [] >>
   ‘!m. MEM m (FLAT (MAP exps es)) ==> MEM m (FLAT (MAP exps cexp))’
   suffices_by metis_tac [] >>
   pop_assum kall_tac >>  pop_assum kall_tac >>
   rw [] >> fs [MEM_FLAT, MEM_MAP] >> rveq >>
   drule mem_comp_field >>
   disch_then (qspecl_then [‘shapes’, ‘cexp’, ‘sh’, ‘y’, ‘es’] mp_tac) >>
   impl_tac
   >- (
    drule compile_exp_val_rel >> disch_then drule_all >> fs [] >>
    strip_tac >> rfs []) >>
   strip_tac >> metis_tac [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   FULL_CASE_TAC >> fs [] >> rveq >- fs [exps_def] >>
   first_x_assum drule >> disch_then drule >>
   disch_then drule >> disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >>
   CCONTR_TAC >> fs [] >>
   metis_tac [load_glob_not_mem_load])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
   every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
   drule compile_exp_val_rel >> disch_then drule_all >> fs [] >>
   strip_tac >> fs [panLangTheory.size_of_shape_def] >> rveq >>
   last_x_assum drule >> disch_then drule >> disch_then drule >>
   disch_then drule >>
   disch_then (qspec_then ‘ad’ mp_tac) >> fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   FULL_CASE_TAC >> fs [] >> rveq >- fs [exps_def] >>
   fs [exps_def] >>
   fs [cexp_heads_eq] >>
   fs [cexp_heads_simp_def] >>
   CCONTR_TAC >> fs [] >>
   fs [MAP_MAP_o] >>
   fs [EVERY_MEM] >>
   ‘EVERY (\x. LENGTH x = 1) (MAP (FST ∘ compile_exp ct) es)’ by (
     fs [EVERY_MEM] >>
     rw [] >>
     fs [MEM_MAP] >>
     cases_on ‘compile_exp ct y’ >> fs [] >>
     rveq >> drule opt_mmap_mem_func >>
     disch_then drule >>
     strip_tac >> fs [] >>
     drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
     drule opt_mmap_mem_defined >> disch_then drule >> fs [] >> strip_tac >>
     first_x_assum drule >>
     TOP_CASE_TAC >> fs [] >>  TOP_CASE_TAC >>
     fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
     fs [panLangTheory.size_of_shape_def]) >>
   ntac 7 (pop_assum mp_tac) >>
   ntac 2 (pop_assum kall_tac) >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘x’ ,‘ws’, ‘es’] >>
   Induct >> rpt gen_tac >> rpt strip_tac >>
   fs [OPT_MMAP_def] >> rveq >> fs []
   >- (
    last_x_assum mp_tac >>
    impl_tac >- metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >>
    impl_tac >- fs [] >>
    ntac 3 (disch_then drule) >>
    cases_on ‘compile_exp ct h’ >> fs [] >>
    cases_on ‘q’ >> fs [] >> metis_tac []) >>
   last_x_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   impl_tac >- fs [] >>
   fs [EVERY_MEM])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
   cases_on ‘compile_exp ct e'’ >>
   cases_on ‘compile_exp ct e’ >> fs [] >> rveq >>
   drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
   qpat_x_assum ‘eval s e = SOME (ValWord w1)’ assume_tac >>
   drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
   fs [flatten_def] >>
   rveq >> fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
   last_x_assum drule >> last_x_assum drule >>
   rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
   strip_tac >>
   rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
   fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
      CaseEq "word_lab"] >> rveq >>
  fs [compile_exp_def] >> rveq >>
  every_case_tac >> fs [] >> rveq >> fs [exps_def] >>
  cases_on ‘compile_exp ct e’ >> fs [] >> rveq >>
  drule compile_exp_val_rel >> disch_then drule_all >> strip_tac >>
  qpat_x_assum ‘eval s e = SOME (ValWord w)’ assume_tac >>
  fs [flatten_def] >>
  rveq >> fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
  last_x_assum drule >>
  rpt (disch_then drule) >>  disch_then (qspec_then ‘ad’ mp_tac) >>
  fs []
QED


Theorem compile_Return:
  ^(get_goal "compile_prog _ (panLang$Return _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "bool"] >>
  rveq >> fs [] >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> rveq >> rfs [] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   fs [evaluate_def, eval_def] >>
   fs [state_rel_def,panSemTheory.empty_locals_def,
       empty_locals_def, state_component_equality]) >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   fs [evaluate_def, eval_def] >>
   fs [state_rel_def,panSemTheory.empty_locals_def,
       empty_locals_def, state_component_equality]) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def] >>
  qmatch_asmsub_abbrev_tac ‘nested_decs temps es p’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    fs [Abbr ‘temps’] >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten value’,
                          ‘nested_seq (store_globals 0w (MAP Var temps))’] mp_tac) >>
  impl_tac >- (unabbrev_all_tac >> fs []) >>
  fs [] >> pairarg_tac >> fs [] >> rveq >> strip_tac >> rveq >>
  fs [Abbr ‘p’] >>
  drule evaluate_seq_store_globals_res >>
  disch_then (qspecl_then [‘flatten value’, ‘t’, ‘0w’] mp_tac) >>
  fs [Abbr ‘es’, length_flatten_eq_size_of_shape] >>
  strip_tac >> fs [] >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``] res_var_lookup_original_eq) >>
  disch_then (qspecl_then [‘flatten value’, ‘t.locals’] assume_tac) >>
  rfs [length_flatten_eq_size_of_shape] >> rveq >>
  conj_tac
  >- fs [state_rel_def,panSemTheory.empty_locals_def,
         empty_locals_def, state_component_equality] >>
  conj_tac >- fs [empty_locals_def, panSemTheory.empty_locals_def] >>
  conj_tac
  >- (
   fs [empty_locals_def, panSemTheory.empty_locals_def, excp_rel_def] >>
   rw [] >> last_x_assum drule_all >> fs []) >>
  fs [empty_locals_def] >>
  qmatch_goalsub_abbrev_tac ‘t with <|locals := _; globals := g|>’ >>
  cases_on ‘flatten value’ >> fs [] >>
  fs [globals_lookup_def, Abbr ‘g’] >>
  qpat_x_assum ‘LENGTH temps = _’ (assume_tac o GSYM) >>
  fs [opt_mmap_eq_some] >>
  fs [] >>
  cases_on ‘temps = []’ >> fs [] >>
  ‘GENLIST (λx. (n2w x):word5) (LENGTH temps) = MAP n2w (0 :: [1 .. (LENGTH temps)-1])’ by (
    fs [GENLIST_eq_MAP] >>
    fs [listRangeINC_def] >> rw [] >>
    cases_on ‘0 < x’ >> fs [NOT_LT_ZERO_EQ_ZERO] >>
    drule (INST_TYPE [``:'a``|->``:num``] el_reduc_tl) >>
    disch_then (qspec_then ‘0::GENLIST (λi. i + 1) (LENGTH temps - 1)’ assume_tac) >> fs []) >>
  fs [] >> conj_tac
  >- (
   fs [FUPDATE_LIST_THM] >>
   ‘~MEM (0w:word5) (MAP FST (ZIP (MAP n2w [1 .. LENGTH temps - 1],t'')))’ by (
     once_rewrite_tac [listRangeINC_def] >> fs [] >>
     ‘LENGTH temps - 1 = LENGTH t''’ by rfs [GSYM length_flatten_eq_size_of_shape] >>
     fs [] >>
     qmatch_goalsub_abbrev_tac ‘ZIP (gn,_)’ >>
     ‘MAP FST (ZIP (gn,t'')) = gn’ by fs [Abbr ‘gn’, MAP_ZIP, LENGTH_GENLIST] >>
     fs [] >> fs [Abbr ‘gn’] >>
     match_mp_tac zero_not_mem_genlist_offset >> DECIDE_TAC) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘t.globals’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  fs [MAP_EQ_EVERY2] >> conj_tac >- fs [listRangeINC_def] >>
  fs [LIST_REL_EL_EQN] >> conj_tac >- fs [listRangeINC_def] >>
  fs [FUPDATE_LIST_THM] >> rw [] >>
  match_mp_tac update_eq_zip_flookup >>
  fs [] >> fs [listRangeINC_def] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw [] >> fs [ALL_DISTINCT_GENLIST] >>
  fs [MEM_GENLIST] >> rveq  >>
  ‘i < 32 ∧ i' < 32’ by fs [] >>
  rfs []
QED


Theorem compile_Raise:
  ^(get_goal "compile_prog _ (panLang$Raise _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "bool"] >>
  rveq >> fs [] >>
  fs [compile_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> rveq >> rfs [] >>
  TOP_CASE_TAC
  >- (fs [excp_rel_def] >> first_x_assum drule_all >> fs []) >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   ‘LENGTH (flatten value) = 0’ by (
     fs [excp_rel_def] >> res_tac >> fs []) >>
   fs [evaluate_def, eval_def] >>
   rfs [state_rel_def,panSemTheory.empty_locals_def,
        empty_locals_def, state_component_equality,
        globals_lookup_def]) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘nested_decs temps es p’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    fs [Abbr ‘temps’] >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten value’,
                          ‘nested_seq (store_globals 0w (MAP Var temps))’] mp_tac) >>
  impl_tac >- (unabbrev_all_tac >> fs []) >>
  fs [] >> pairarg_tac >> fs [] >> rveq >> strip_tac >> rveq >>
  fs [Abbr ‘p’] >>
  drule evaluate_seq_store_globals_res >>
  disch_then (qspecl_then [‘flatten value’, ‘t’, ‘0w’] mp_tac) >>
  fs [Abbr ‘es’, length_flatten_eq_size_of_shape] >>
  strip_tac >> fs [] >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``] res_var_lookup_original_eq) >>
  disch_then (qspecl_then [‘flatten value’, ‘t.locals’] assume_tac) >>
  rfs [length_flatten_eq_size_of_shape] >> rveq >>
  conj_tac
  >- fs [state_rel_def,panSemTheory.empty_locals_def,
         empty_locals_def, state_component_equality] >>
  conj_tac >- fs [empty_locals_def, panSemTheory.empty_locals_def] >>
  conj_tac
  >- (
   fs [empty_locals_def, panSemTheory.empty_locals_def, excp_rel_def] >>
   rw [] >> last_x_assum drule_all >> fs []) >>
  strip_tac >>
  fs [empty_locals_def] >>
  fs [globals_lookup_def] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘ALL_DISTINCT (GENLIST (λx. (n2w x): word5) (LENGTH (flatten value)))’ by (
    fs [ALL_DISTINCT_GENLIST] >>
    rw [] >> rfs []) >>
  drule (INST_TYPE [``:'a``|->``:word5``,
                    ``:'b``|->``:'a word_lab``] update_eq_zip_flookup) >>
  disch_then (qspecl_then [‘t.globals’, ‘flatten value’, ‘n’] mp_tac) >>
  fs []
QED


Theorem compile_Seq:
  ^(get_goal "compile_prog _ (panLang$Seq _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [compile_prog_def] >>
  fs [panSemTheory.evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘res' = NONE’ >> fs [] >>
  rveq  >> fs []
  >- (
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >>
   first_x_assum drule_all >> fs []) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  first_x_assum drule_all >> strip_tac >>
  fs [] >> rveq >>

  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  TRY (cases_on ‘FLOOKUP ctxt.eid_map m’ >> fs [] >> cases_on ‘x’ >> fs []) >>
  cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
  cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
QED


Theorem compile_If:
  ^(get_goal "compile_prog _ (panLang$If _ _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_prog_def] >>
  cases_on ‘eval s e’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  cases_on ‘w’ >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [flatten_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  last_x_assum drule_all >>
  strip_tac >> fs [] >>
  rfs [] >>
  cases_on ‘res’ >> fs [] >>
  rveq  >> fs [] >>
  cases_on ‘c = 0w’ >> fs []
QED

Theorem compile_While:
  ^(get_goal "compile_prog _ (panLang$While _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum ‘evaluate (While e c,s) = (res,s1)’ mp_tac >>
  once_rewrite_tac [panSemTheory.evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  strip_tac >>
  fs [compile_prog_def] >>
  TOP_CASE_TAC >> fs [] >>
  drule_all compile_exp_val_rel >>
  once_rewrite_tac [shape_of_def] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  TOP_CASE_TAC >> fs [panLangTheory.size_of_shape_def, flatten_def] >>
  rveq >> fs [MAP] >>
  reverse (cases_on ‘c' ≠ 0w’) >> fs [] >> rveq
  >- fs [Once evaluate_def] >>
  pairarg_tac >> fs [] >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq >> fs []
  >- (
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   fs [state_rel_def] >> rveq >>
   fs [empty_locals_def, panSemTheory.empty_locals_def]) >>
  ‘t.clock <> 0’ by fs [state_rel_def] >>
  reverse (cases_on ‘res'’) >> fs []
  >- (
   cases_on ‘x’ >> fs [] >> rveq >>
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   last_x_assum (qspecl_then [‘dec_clock t’, ‘ctxt’] mp_tac) >>
   impl_tac >>
   TRY (
   fs [dec_clock_def, panSemTheory.dec_clock_def, state_rel_def] >>
   NO_TAC)
   >- (
    strip_tac >> fs [] >> rveq >>
    fs [] >>
    last_x_assum drule_all >>
    strip_tac >> fs [] >> rfs [])
   >- (
    strip_tac >> fs [] >> rveq >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []) >>
   strip_tac >> fs [] >> rveq >>
   cases_on ‘FLOOKUP ctxt.eid_map m’ >> fs [] >>
   cases_on ‘x’ >> fs [] >>
   cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
   cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []) >>
  fs [Once evaluate_def] >>
  pairarg_tac >> fs [] >>
  last_x_assum (qspecl_then [‘dec_clock t’, ‘ctxt’] mp_tac) >>
  impl_tac
  >- (
   fs [dec_clock_def, panSemTheory.dec_clock_def, state_rel_def]) >>
  strip_tac >> fs [] >> rveq >> fs [] >> rfs [] >>
  last_x_assum drule_all >>
  fs [] >>
  strip_tac >> fs [] >> rveq >> rfs []
QED


Theorem eval_map_comp_exp_flat_eq:
  !argexps args s t ctxt. MAP (eval s) argexps = MAP SOME args /\
  state_rel s t ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt s.locals t.locals ==>
   MAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) =
        MAP SOME (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs []) >>
  cases_on ‘args’ >> fs [] >>
  fs [MAP_APPEND] >>
  cases_on ‘compile_exp ctxt h’ >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  last_x_assum (qspecl_then [‘t'’] mp_tac) >>
  fs [] >>
  disch_then drule_all >>
  fs []
QED


Theorem local_rel_gt_max_var_preserved:
  !ct l l' n v.
  locals_rel ct l l' /\ ct.max_var < n ==>
  locals_rel ct l (l' |+ (n,v))
Proof
  rw [] >>
  fs [locals_rel_def] >>
  rw [] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' ns <= ct.max_var’ by (
    drule ctxt_max_el_leq >> metis_tac []) >>
  fs [FLOOKUP_UPDATE]
QED

Theorem local_rel_le_zip_update_preserved:
  !ct l l' x v sh ns v'.
  locals_rel ct l l' /\
  FLOOKUP l x = SOME v /\
  FLOOKUP ct.var_nums x = SOME (sh,ns) /\
  shape_of v = shape_of v' ∧ ALL_DISTINCT ns  ==>
  locals_rel ct (l |+ (x,v')) (l' |++ ZIP (ns,flatten v'))
Proof
  rw [] >>
  drule_all locals_rel_lookup_ctxt >>
  strip_tac >> fs [] >>
  fs [locals_rel_def] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  first_x_assum drule_all >> fs []
  >- (
   match_mp_tac opt_mmap_some_eq_zip_flookup >>
   fs [opt_mmap_eq_some, MAP_EQ_EVERY2,
       length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  match_mp_tac opt_mmap_disj_zip_flookup >>
  fs [length_flatten_eq_size_of_shape] >>
  fs [no_overlap_def] >>
  first_x_assum (qspecl_then [‘x’, ‘vname’, ‘shape_of v’,
                              ‘shape_of v''’, ‘ns’, ‘ns''’] mp_tac) >>
  fs []  >> fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
  metis_tac []
QED

Theorem ctxt_fc_code_vars_eq:
    (ctxt_fc cvs em vs shs ns).code_vars = cvs
Proof
  rw [ctxt_fc_def]
QED

Theorem ctxt_fc_eid_map_eq:
    (ctxt_fc cvs em vs shs ns).eid_map = em
Proof
  rw [ctxt_fc_def]
QED

Theorem ctxt_fc_max_var:
    (ctxt_fc ctxt.code_vars em vs shs ns).max_var = list_max ns
Proof
  rw [ctxt_fc_def]
QED

Definition slc_def:
  slc vshs args = FEMPTY |++ ZIP (MAP FST vshs,args)
End

Definition tlc_def:
  tlc ns args = FEMPTY |++ ZIP (ns,FLAT (MAP flatten args))
End

Theorem slc_tlc_rw:
  FEMPTY |++ ZIP (MAP FST vsh,args) = slc vsh args ∧
  FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)) = tlc ns args
Proof
  rw [slc_def, tlc_def]
QED

Theorem call_preserve_state_code_locals_rel:
   ALL_DISTINCT (MAP FST vshs) /\
   LIST_REL (λvshape arg. SND vshape = shape_of arg) vshs args /\
   state_rel s t /\
   code_rel ctxt s.code t.code  /\
   excp_rel ctxt s.eshapes t.eids  /\
   locals_rel ctxt s.locals t.locals  /\
   FLOOKUP s.code fname = SOME (vshs,prog)  /\
   FLOOKUP ctxt.code_vars fname = SOME (vshs,ns)  /\
   ALL_DISTINCT ns  /\
   size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))  /\
   FLOOKUP t.code fname = SOME (ns, compile_prog
      (ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns) prog)  /\
    LENGTH ns = LENGTH (FLAT (MAP flatten args)) ==>
   state_rel (dec_clock s with locals := slc vshs args) (dec_clock t with locals := tlc ns args) ∧
   code_rel (ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns)
            (dec_clock s).code (dec_clock t).code ∧
   excp_rel (ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns)
             (dec_clock s).eshapes (dec_clock t).eids ∧
   locals_rel (ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns) (slc vshs args) (tlc ns args)
Proof
  strip_tac >> fs [] >>
  conj_tac >- fs [state_rel_def, dec_clock_def, panSemTheory.dec_clock_def] >>
  conj_tac
  >- (
   fs [code_rel_def, ctxt_fc_def] >>
   rw [] >>
   fs [panSemTheory.dec_clock_def] >>
   last_x_assum drule_all >>
   fs [dec_clock_def]) >>
  conj_tac
  >- (
   fs [excp_rel_def, ctxt_fc_def, panSemTheory.dec_clock_def, dec_clock_def] >> rw [] >>
   last_x_assum drule_all >> fs []) >>
  fs [locals_rel_def] >>
  conj_tac (* replicating because needs to preserve fm in the third conjunct *)
  >- (
   ‘(ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns).var_nums =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     fs [ctxt_fc_def] >>
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [] >>
   metis_tac [all_distinct_alist_no_overlap, LENGTH_MAP]) >>
  conj_tac
  >- (
   ‘(ctxt_fc ctxt.code_vars ctxt.eid_map (MAP FST vshs) (MAP SND vshs) ns).var_nums =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     fs [ctxt_fc_def] >>
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [ctxt_fc_max_var] >>
   match_mp_tac all_distinct_alist_ctxt_max >> fs []) >>
  rw [] >> fs [locals_rel_def, ctxt_fc_def, slc_def, tlc_def] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by (drule LIST_REL_LENGTH >> fs []) >>
  drule fm_empty_zip_flookup >> fs [] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  qexists_tac ‘EL n (with_shape (MAP SND vshs) ns)’ >>
  conj_tac
  >- (  (* could be neater *)
   ‘FLOOKUP (FEMPTY |++ ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns))) vname =
    SOME (EL n (MAP SND vshs),EL n (with_shape (MAP SND vshs) ns))’ by (
     match_mp_tac fm_empty_zip_flookup_el >>
     fs [] >> ‘LENGTH ns = size_of_shape (Comb (MAP SND vshs))’ by fs [] >>
     drule length_with_shape_eq_shape >> fs [] >> strip_tac >>
     ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
     disch_then (qspec_then ‘n’ mp_tac) >> fs []) >>
   fs [] >>
   ‘n < LENGTH (MAP FST vshs)’ by fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >>
   drule EL_ZIP >>
   disch_then (qspec_then ‘n’ assume_tac) >>
   rfs [] >> rveq >>
   fs [LIST_REL_EL_EQN] >>
   last_x_assum drule >> fs [EL_MAP]) >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rewrite_tac [LIST_REL_EL_EQN] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rw [] >> match_mp_tac list_rel_flatten_with_shape_flookup >> fs [] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
  disch_then (qspec_then ‘n’ mp_tac) >> fs [] >> strip_tac >>
  fs [EVERY2_MAP] >>
  match_mp_tac list_rel_flatten_with_shape_length >>
  qexists_tac ‘args’ >> fs [] >>
  fs [EVERY2_MAP]
QED


val clock_zero_tail_rt_tac =
    fs [evaluate_def] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >>
    strip_tac >>
    drule code_rel_empty_locals >>
    fs [state_rel_def, panSemTheory.empty_locals_def, empty_locals_def]

val clock_zero_nested_seq_rt_tac =
    fs [nested_seq_def] >>
    fs [evaluate_def] >>
    pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >> rveq >>
    fs [panSemTheory.lookup_code_def] >>
    cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    strip_tac >> fs [] >>
    fs [state_rel_def] >> rveq >> rfs [] >>
    rveq >> fs [] >>
    drule code_rel_empty_locals >> fs [panSemTheory.empty_locals_def, empty_locals_def]

val rels_empty_tac =
    fs [Abbr ‘nctxt’, state_rel_def, ctxt_fc_code_vars_eq, ctxt_fc_eid_map_eq,
        excp_rel_def, empty_locals_def, panSemTheory.empty_locals_def, code_rel_def,
        globals_lookup_def]

val tail_call_tac =
   fs [evaluate_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def] >>
   cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
   disch_then (qspec_then ‘ns’ mp_tac) >>
   fs [] >>
   strip_tac >>
   TOP_CASE_TAC >- fs [state_rel_def] >>
   cases_on ‘evaluate
             (prog,
              dec_clock s with locals := FEMPTY |++ ZIP (MAP FST q,args))’ >>
   fs [] >>
   cases_on ‘q'’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
   first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
   impl_tac >>
   TRY (
   fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
   match_mp_tac call_preserve_state_code_locals_rel >>
   fs [])
   >- (strip_tac >> fs [] >> rels_empty_tac)
   >- (
    strip_tac >> fs [] >>
    TOP_CASE_TAC >> fs [] >> TOP_CASE_TAC >> fs [] >> rels_empty_tac)
   >- (
    strip_tac >> fs [] >>
    cases_on ‘FLOOKUP nctxt.eid_map m’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    rels_empty_tac) >>
   strip_tac >> rels_empty_tac


val call_tail_ret_impl_tac =
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >> rveq >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >> strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs []) >>
     strip_tac >> fs [] >>
     fs [state_rel_def, Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq,
         panSemTheory.empty_locals_def, empty_locals_def, ctxt_fc_eid_map_eq, excp_rel_def]

val ret_call_shape_retv_one_tac =
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs []) >>
     strip_tac >> fs [] >>
     ‘size_of_shape (shape_of x) = 1’ by (
       fs [locals_rel_def] >>
       last_x_assum drule >> fs [shape_of_def] >> strip_tac >>
       qpat_x_assum ‘One = shape_of x’ (assume_tac o GSYM) >>
       fs [panLangTheory.size_of_shape_def]) >>
     fs [shape_of_def] >>
     drule locals_rel_lookup_ctxt >>
     disch_then drule >> strip_tac >> fs [] >>
     rveq >> fs [OPT_MMAP_def] >> rveq >>
     fs [state_rel_def, panSemTheory.set_var_def,set_var_def,
         Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
         panSemTheory.set_var_def,set_var_def] >>
     conj_tac
     >- (
      fs [excp_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
          panSemTheory.set_var_def,set_var_def]) >>
     fs [length_flatten_eq_size_of_shape] >>
     rfs [panLangTheory.size_of_shape_def] >>
     fs [locals_rel_def, panSemTheory.set_var_def,set_var_def] >>
     rw [] >> rveq >>
     fs [FLOOKUP_UPDATE] >>
     FULL_CASE_TAC >> fs [] >> rveq
     >- (
      fs [OPT_MMAP_def, FLOOKUP_UPDATE] >> rveq >>
      fs [length_flatten_eq_size_of_shape, panLangTheory.size_of_shape_def]) >>
     res_tac >> fs [] >>
     match_mp_tac opt_mmap_flookup_update >>
     fs [] >>
     drule no_overlap_flookup_distinct >>
     disch_then drule_all >> fs [distinct_lists_def]


val ret_call_shape_retv_comb_zero_tac =
     fs [ret_var_def, ret_hdl_def] >>
     fs [evaluate_def] >>
     cases_on ‘eval t x0’ >> fs [] >>
     cases_on ‘x'’ >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >> strip_tac >>
     cases_on ‘t.clock = 0’ >- fs [state_rel_def] >>
     fs [] >> rveq >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs []) >>
     strip_tac >> fs [] >>
     cases_on ‘res1’ >> fs [] >>
     cases_on ‘x'’ >> fs [] >> rveq >> fs [] >>
     fs [shape_of_def, panLangTheory.size_of_shape_def,
         panSemTheory.set_var_def, set_var_def] >>
     conj_tac >- fs [state_rel_def] >>
     conj_tac >- fs [Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq, ctxt_fc_eid_map_eq] >>
     conj_tac
     >- (
      fs [Abbr ‘nctxt’, excp_rel_def, ctxt_fc_code_vars_eq, ctxt_fc_eid_map_eq]) >>
     fs [locals_rel_def] >> rw [] >>
     fs [FLOOKUP_UPDATE] >> FULL_CASE_TAC >> fs [] >> rveq
     >- (
      conj_asm1_tac
      >- (
       fs [locals_rel_def] >> res_tac >> fs []) >>
      ‘LENGTH (flatten v) = 0 /\ LENGTH r' = 0’ suffices_by fs [OPT_MMAP_def] >>
      conj_asm1_tac
      >- (
       rewrite_tac [length_flatten_eq_size_of_shape] >>
       metis_tac [panLangTheory.size_of_shape_def]) >>
      last_x_assum drule_all >> strip_tac >> fs [] >> rveq >>
      ‘flatten v = flatten x’ by (
        ‘size_of_shape (shape_of v) = size_of_shape (shape_of x)’ by fs [] >>
        fs [GSYM length_flatten_eq_size_of_shape] >>
        cases_on ‘flatten v’ >> fs []) >>
      fs [] >> cases_on ‘ns'’ >> rfs [OPT_MMAP_def]) >>
     first_x_assum drule >> strip_tac >> fs [] >>
     fs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
     rw [] >> fs [FLOOKUP_UPDATE] >>
     TOP_CASE_TAC >> fs [] >>
     drule ctxt_max_el_leq >>
     qpat_x_assum ‘LENGTH _ = LENGTH (flatten _)’ (assume_tac o GSYM) >>
     fs [] >> disch_then drule_all >> fs []

val ret_call_shape_retv_comb_one_tac =
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs []) >>
     strip_tac >> fs [] >>
     ‘size_of_shape (shape_of x) = 1’ by (
       fs [locals_rel_def] >>
       last_x_assum drule >> fs [shape_of_def] >>
       strip_tac >> qpat_x_assum ‘Comb l = shape_of x’ (assume_tac o GSYM) >>
       fs [panLangTheory.size_of_shape_def, shape_of_def]) >> fs [] >>
     drule locals_rel_lookup_ctxt >>
     disch_then drule >> strip_tac >> fs [] >>
     rveq >> fs [OPT_MMAP_def] >> rveq >>
     cases_on ‘ns'’ >> fs []
     >- (
      fs [OPT_MMAP_def] >>
      pop_assum (assume_tac o GSYM) >>
      fs [GSYM length_flatten_eq_size_of_shape]) >>
     fs [OPT_MMAP_def] >> rveq >>
     fs [state_rel_def, panSemTheory.set_var_def,set_var_def,
         Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
         panSemTheory.set_var_def,set_var_def] >>
     conj_tac
     >- (
      fs [excp_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
          panSemTheory.set_var_def,set_var_def]) >>
     ‘size_of_shape (shape_of v) = 1’ by fs [] >>
      rveq >> fs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [locals_rel_def, panSemTheory.set_var_def,set_var_def] >>
      rw [] >> rveq >>
      fs [FLOOKUP_UPDATE] >>
      FULL_CASE_TAC >> fs [] >> rveq
      >- (
       fs [OPT_MMAP_def, FLOOKUP_UPDATE] >>
       fs [length_flatten_eq_size_of_shape,
           panLangTheory.size_of_shape_def, shape_of_def,
           OPT_MMAP_def]) >>
      res_tac >> fs [] >>
      match_mp_tac opt_mmap_flookup_update >>
      fs [OPT_MMAP_def] >> rveq >>
      drule no_overlap_flookup_distinct >>
      disch_then drule_all >>
      cases_on ‘ns'’ >>
      fs [distinct_lists_def]


val ret_call_shape_retv_comb_gt_one_tac =
    fs [ret_var_def, ret_hdl_def] >>
    fs [evaluate_def, assign_ret_def] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
    disch_then (qspec_then ‘ns’ mp_tac) >>
    fs [] >> strip_tac >>
    cases_on ‘t.clock = 0’ >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
     match_mp_tac call_preserve_state_code_locals_rel >>
     fs []) >>
    strip_tac >> fs [] >>
    cases_on ‘res1’ >> fs [] >>
    cases_on ‘x'’ >> fs [] >> rveq >> fs [] >>
    fs [shape_of_def, panLangTheory.size_of_shape_def,
        panSemTheory.set_var_def, set_var_def] >>
    ‘1 < size_of_shape (shape_of x)’ by (
      drule locals_rel_lookup_ctxt >>
      disch_then drule >>
      strip_tac >> fs [] >> rfs [] >>
      fs [panLangTheory.size_of_shape_def] >>
      DECIDE_TAC) >>
    fs [] >>
    ‘ALL_DISTINCT r'’ by
      (fs [locals_rel_def] >> imp_res_tac all_distinct_flookup_all_distinct) >>
    fs [globals_lookup_def] >>
    drule evaluate_seq_assign_load_globals >>
    disch_then (qspecl_then [‘t1 with locals :=
                              t.locals’, ‘0w’] mp_tac) >>
    impl_tac
    >- (
     conj_tac
     >- (
      fs [word_0_n2w] >>
      imp_res_tac locals_rel_lookup_ctxt >> rveq >>
      fs [length_flatten_eq_size_of_shape] >> rfs []) >>
     conj_tac
     >- (
      rw [] >> CCONTR_TAC >>
      drule locals_rel_lookup_ctxt >>
      disch_then drule_all >>
      strip_tac >> fs [] >> rveq >>
      fs [opt_mmap_eq_some] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL] >>
      rveq >> fs [] >> rfs [] >>
      res_tac >> rfs []) >>
     rw [] >> rfs [] >>
     drule locals_rel_lookup_ctxt >>
     ‘size_of_shape (shape_of x) = LENGTH r'’ by (
       drule locals_rel_lookup_ctxt >>
       disch_then drule >>
       strip_tac >> fs [] >> rveq >>
       fs [length_flatten_eq_size_of_shape] >> rfs []) >>
     fs [] >> drule opt_mmap_mem_func >>
     disch_then drule >> strip_tac >> fs []) >>
    strip_tac >> fs [] >>
    conj_tac >- fs [state_rel_def] >>
    conj_tac >- fs [Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq, ctxt_fc_eid_map_eq] >>
    conj_tac
    >- (
     fs [Abbr ‘nctxt’, excp_rel_def, ctxt_fc_code_vars_eq, ctxt_fc_eid_map_eq]) >>
    ‘MAP (λn. THE (FLOOKUP t1.globals n)) (GENLIST (λx. n2w x) (LENGTH r')) =
     flatten v’ by (
      fs [opt_mmap_eq_some] >>
      ‘size_of_shape (shape_of v) = LENGTH r'’ by (
        drule locals_rel_lookup_ctxt >>
        disch_then drule >>
        strip_tac >> fs [] >> rveq >>
        fs [length_flatten_eq_size_of_shape] >> rfs []) >>
      fs [] >> drule map_some_the_map >> fs []) >>
    fs [] >>
    match_mp_tac local_rel_le_zip_update_preserved >> fs [] >>
    match_mp_tac local_rel_gt_max_var_preserved >>
    fs []


val eval_call_impl_only_tac =
     fs [evaluate_def] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule (INST_TYPE [``:'c``|->``:num``] list_rel_length_shape_of_flatten) >>
     disch_then (qspec_then ‘ns’ mp_tac) >>
     fs [] >>
     strip_tac >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile_prog nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs [])


val ret_call_excp_reult_handle_none_tac =
    (* exception value with ret call *)
     TOP_CASE_TAC >> fs [] >>
     fs [CaseEq "option", CaseEq "prod",
         CaseEq "shape", CaseEq "list"] >>
     rveq >> fs [ret_var_def, ret_hdl_def] >>
    qpat_x_assum ‘1 = _’ (assume_tac o GSYM) >> fs [] >>
    pop_assum kall_tac
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eid_map = ctxt.eid_map’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
     cases_on ‘FLOOKUP ctxt.eid_map m'’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac)
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eid_map = ctxt.eid_map’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
     cases_on ‘FLOOKUP ctxt.eid_map m'’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac)
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eid_map = ctxt.eid_map’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
     cases_on ‘FLOOKUP ctxt.eid_map m'’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac) >>
    eval_call_impl_only_tac >>
    strip_tac >> fs [] >>
    ‘nctxt.eid_map = ctxt.eid_map’ by
      fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
    cases_on ‘FLOOKUP ctxt.eid_map m'’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    cases_on ‘res1’ >> fs [] >> rveq >> fs [] >>
    TRY (cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
    cases_on ‘FLOOKUP ctxt.eid_map m'’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
    >- rels_empty_tac >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
    >- (
     fs [shape_of_def, panLangTheory.size_of_shape_def] >>
     rels_empty_tac) >>
    rels_empty_tac

val ret_call_excp_reult_handle_uneq_exp_tac =
    rveq >> fs [] >>
    cases_on ‘FLOOKUP ctxt.eid_map m0’ >> fs []
    >- ret_call_excp_reult_handle_none_tac >>
    cases_on ‘x’ >> fs [] >>
    rename [‘geid <> eid’] >>
    qpat_x_assum ‘1 = _’ (assume_tac o GSYM) >> fs [] >>
    pop_assum kall_tac >>
    TOP_CASE_TAC >> fs [] >>
    fs [CaseEq "option", CaseEq "prod",
        CaseEq "shape", CaseEq "list"] >>
    rveq >> fs [ret_var_def, ret_hdl_def] >>
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eid_map = ctxt.eid_map’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
     cases_on ‘FLOOKUP ctxt.eid_map geid’ >> fs [] >>
     cases_on ‘x’ >> fs [] >>
     rename [‘res1 = SOME (Exception er)’] >>
     ‘er <> r'’ by (
       CCONTR_TAC >>
       fs [excp_rel_def]) >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >> rveq
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- rels_empty_tac >>
     rels_empty_tac


val ret_call_excp_handler_tac =
    TRY (
    first_x_assum drule >>
    strip_tac >> rfs []) >>
    TOP_CASE_TAC >> fs [] >>
    fs [CaseEq "option", CaseEq "prod",
        CaseEq "shape", CaseEq "list"] >>
    rveq >> fs [ret_var_def, ret_hdl_def] >>
    (
    eval_call_impl_only_tac >>
    strip_tac >> fs [] >>
    ‘nctxt.eid_map = ctxt.eid_map’ by
      fs [Abbr ‘nctxt’, ctxt_fc_eid_map_eq] >>
    fs [] >>
    cases_on ‘FLOOKUP ctxt.eid_map eid’ >> fs [] >>
    rename [‘FLOOKUP ctxt.eid_map eid = SOME ed’] >>
    cases_on ‘ed’ >> fs [] >> rveq >> fs [] >>
    ‘MEM r' t.eids’ by (
      fs [excp_rel_def] >>
      ‘r' ∈ (IMAGE SND (FRANGE ctxt.eid_map))’
      suffices_by metis_tac [set_eq_membership] >>
      fs [IN_IMAGE, FRANGE_FLOOKUP] >>
      qexists_tac ‘(q, r')’ >> fs [] >>
      qexists_tac ‘eid’ >> fs []) >>
    fs [] >>
    ‘q = shape_of v’ by (
      fs [excp_rel_def] >> res_tac >> rfs []) >>
    qpat_x_assum ‘1 = _’ (assume_tac o GSYM) >> fs [] >>
    pop_assum kall_tac >>
    fs [is_valid_value_def] >>
    cases_on ‘FLOOKUP s.locals m''’ >> fs [] >>
    drule locals_rel_lookup_ctxt >>
    disch_then drule_all >>
    strip_tac >> fs [] >> rveq >>
    rename [‘OPT_MMAP (FLOOKUP t.locals) _ = SOME (flatten ex)’] >>
    fs [exp_hdl_def] >>
    pairarg_tac >> fs [] >>
    ‘ALL_DISTINCT ns'’ by
      (fs [locals_rel_def] >> imp_res_tac all_distinct_flookup_all_distinct) >>
    drule evaluate_seq_assign_load_globals >>
    disch_then (qspecl_then [‘t1 with locals :=
                              t.locals’, ‘0w’] mp_tac) >>
    impl_tac
    >- (
     conj_tac
     >- (
      fs [word_0_n2w] >>
      imp_res_tac locals_rel_lookup_ctxt >> rveq >>
      fs [length_flatten_eq_size_of_shape] >> rfs [] >>
      cases_on ‘size_of_shape (shape_of ex)’ >> fs []) >>
     conj_tac
     >- (
      rw [] >> CCONTR_TAC >>
      drule locals_rel_lookup_ctxt >>
      disch_then drule_all >>
      strip_tac >> fs [] >> rveq >>
      fs [opt_mmap_eq_some] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL] >>
      rveq >> fs [] >> rfs [] >>
      res_tac >> rfs []) >>
     rw [] >> rfs [] >>
     CCONTR_TAC >> fs [] >>
     reverse (cases_on ‘1 ≤ size_of_shape (shape_of ex)’) >>
     fs []
     >- fs [MEM_GENLIST, length_flatten_eq_size_of_shape] >>
     rfs [globals_lookup_def] >>
     fs [GSYM length_flatten_eq_size_of_shape] >>
     qpat_x_assum ‘OPT_MMAP (FLOOKUP t1.globals) _ = _’  assume_tac >>
     drule opt_mmap_mem_func >>
     disch_then drule >> strip_tac >> fs []) >>
    strip_tac >> fs [] >>
    rfs [] >> rveq >>
    qmatch_goalsub_abbrev_tac ‘evaluate (compile_prog ctxt p,tt)’ >>
    first_x_assum (qspecl_then [‘tt’, ‘ctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘tt’, panSemTheory.set_var_def] >>
     fs [state_rel_def, panSemTheory.set_var_def,set_var_def,
         Abbr ‘nctxt’, code_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
         panSemTheory.set_var_def,set_var_def] >>
     conj_tac
     >- (
      fs [excp_rel_def, ctxt_fc_code_vars_eq,ctxt_fc_eid_map_eq,
          panSemTheory.set_var_def,set_var_def]) >>
     fs [locals_rel_def] >>
     rw [] >> rveq >>
     fs [FLOOKUP_UPDATE] >>
     reverse FULL_CASE_TAC >> fs [] >> rveq
     >- (
      res_tac >> fs [] >>
      qpat_x_assum  ‘OPT_MMAP _ ns'' = _’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac opt_mmap_disj_zip_flookup >>
      conj_tac
      >- (
       pop_assum (assume_tac o GSYM) >>
       fs [no_overlap_def] >>
       res_tac >> fs [] >> rveq >>
       fs []  >> fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
       metis_tac []) >>
      res_tac >> fs []) >>
     reverse (cases_on ‘1 ≤ size_of_shape (shape_of ex)’) >>
     fs [] >> rveq >>
     fs [length_flatten_eq_size_of_shape]
     >- (
      qpat_x_assum ‘shape_of v = shape_of ex’ (assume_tac o GSYM) >>
      fs [] >>
      ‘size_of_shape (shape_of v) = 0’ by fs [] >>
      fs [OPT_MMAP_def, GSYM length_flatten_eq_size_of_shape]) >>
     fs [globals_lookup_def, opt_mmap_eq_some] >>
     simp [Once (GSYM o_DEF),MAP_o] >>
     rewrite_tac [ETA_AX] >>
     rfs [ETA_AX] >>
     fs [MAP_o, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
     rw [] >>
     fs [MAP_MAP_o] >>
     ‘MAP (THE ∘ SOME) (flatten v) = flatten v’ by fs [map_the_some_cancel] >>
     fs [] >> pop_assum kall_tac >>
     match_mp_tac update_eq_zip_flookup >>
     fs []) >>
    strip_tac >> fs [])


Theorem compile_Call:
  ^(get_goal "compile_prog _ (panLang$Call _ _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_prog_def] >>
  fs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [flatten_def] >> rveq >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq
  (* s = 0 case *)
  >- (
   TRY (rpt TOP_CASE_TAC) >> fs [] >> clock_zero_tail_rt_tac) >>
  (* s <> 0 case *)
  TOP_CASE_TAC >> fs []
  (* Tail call *)
  >- tail_call_tac >>
  (* Return case *)
  cases_on ‘evaluate (prog,dec_clock s with locals := newlocals)’ >>
  cases_on ‘q’ >> fs [] >>
  cases_on ‘x’ >> fs [] >> rveq >>
  TRY (cases_on ‘FLOOKUP s.locals m’ >> fs [] >> NO_TAC)
  (* timed-out in Ret call *)
  >- (TRY (rpt TOP_CASE_TAC) >> fs [] >> call_tail_ret_impl_tac)
  (* return in Ret call *)
  >- (
   cases_on ‘is_valid_value s.locals m v’ >> fs [] >> rveq >>
   fs [is_valid_value_def] >>
   cases_on ‘FLOOKUP s.locals m’ >> fs [] >>
   fs [wrap_rt_def] >>
   TOP_CASE_TAC >> fs []
   >- (
    fs [CaseEq "option"]
    >- (fs [locals_rel_def] >> first_x_assum drule >> fs []) >>
    fs [CaseEq "prod", CaseEq "shape", CaseEq "list"] >> rveq >> fs [] >>
    qpat_x_assum ‘1 = _’ (assume_tac o GSYM) >> fs [] >>
    pop_assum kall_tac >>
    TOP_CASE_TAC >> fs [] >>
    drule locals_rel_lookup_ctxt >>
    disch_then drule >> strip_tac >> fs [] >>
    rveq >> fs [OPT_MMAP_def] >> rveq >>
    pop_assum (assume_tac o GSYM) >>
    ‘size_of_shape (shape_of x) = 1’ by
      fs [panLangTheory.size_of_shape_def] >>
    rfs [GSYM length_flatten_eq_size_of_shape]) >>
   fs [CaseEq "option"] >>
   fs [CaseEq "prod", CaseEq "shape", CaseEq "list"] >> rveq >>
   fs [ret_var_def, ret_hdl_def]
   >- (
    (* shape-rtv: One *)
    TRY (rpt TOP_CASE_TAC) >> fs [] >> ret_call_shape_retv_one_tac) >>
   qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.var_nums m = SOME (Comb l,r')’ >>
   cases_on ‘size_of_shape (Comb l) = 0’ >> fs []
   >- (TRY (rpt TOP_CASE_TAC) >> fs [] >> ret_call_shape_retv_comb_zero_tac) >>
   cases_on ‘size_of_shape (Comb l) = 1’ >> fs []
   (* size-shape-ret = 1 *)
   >- (TRY (rpt TOP_CASE_TAC) >> fs [] >> ret_call_shape_retv_comb_one_tac) >>
   (* 1 < size-shape-ret *)
   TRY (rpt TOP_CASE_TAC) >> fs [] >> ret_call_shape_retv_comb_gt_one_tac)
  >- (
   (* Exception result *)
   fs [wrap_rt_def] >>
   fs [] >> cases_on ‘o'’ >> fs []
   (* NONE exp-handler *)
   >- ret_call_excp_reult_handle_none_tac >>
   cases_on ‘x’ >> fs [] >> rveq >>
   reverse (cases_on ‘m' = m0’) >> fs []
   (* eids mismatch *)
   >- ret_call_excp_reult_handle_uneq_exp_tac >>
   (* handling exception *)
   rename [‘geid = eid’] >>
   cases_on ‘FLOOKUP s.eshapes eid’ >> fs [] >> rveq >>
   cases_on ‘shape_of v = x’ >> fs [] >>
   cases_on ‘is_valid_value s.locals m'' v’ >> fs [] >>
   cases_on ‘FLOOKUP ctxt.eid_map eid’ >> fs []
   >- (
    fs [excp_rel_def] >> res_tac >> fs []) >>
   cases_on ‘x'’ >> fs [] >> rveq >>
   TOP_CASE_TAC >> fs []
   >- ret_call_excp_handler_tac >>
   TOP_CASE_TAC >> fs [] >>
   ret_call_excp_handler_tac) >>
  (* FFI *)
  cases_on ‘o'’ >> fs []
  >- (TRY (rpt TOP_CASE_TAC) >> fs [] >> call_tail_ret_impl_tac) >>
  cases_on ‘x’ >>
  TRY (rpt TOP_CASE_TAC) >> fs [] >> call_tail_ret_impl_tac
QED


Theorem compile_ExtCall:
  ^(get_goal "compile_prog _ (panLang$ExtCall _ _ _ _ _)")
Proof
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_prog_def] >>
  fs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod"] >>
  rveq >> fs [] >>
  imp_res_tac locals_rel_lookup_ctxt >> fs [flatten_def] >> rveq >>
  TOP_CASE_TAC >> fs [shape_of_def, OPT_MMAP_def] >>
  TOP_CASE_TAC >> fs [shape_of_def, OPT_MMAP_def] >>
  TOP_CASE_TAC >> fs [shape_of_def, OPT_MMAP_def] >>
  TOP_CASE_TAC >> fs [shape_of_def, OPT_MMAP_def] >> rveq >>
  fs [evaluate_def] >>
  ‘t.memory = s.memory ∧ t.memaddrs = s.memaddrs ∧ t.be = s.be ∧ t.ffi = s.ffi’ by
    fs [state_rel_def] >>
  fs [] >>
  TOP_CASE_TAC >> fs []
  >- (TOP_CASE_TAC >> fs [] >> rveq >> fs [state_rel_def, code_rel_def]) >>
  rveq >> fs [state_rel_def, code_rel_def, excp_rel_def, panSemTheory.empty_locals_def]
QED


Theorem pc_compile_correct:
   ^(compile_prog_tm ())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [compile_Skip_Break_Continue, compile_Dec,
          compile_Assign, compile_Store, compile_StoreByte, compile_Seq,
          compile_If, compile_While, compile_Call, compile_ExtCall,
          compile_Raise, compile_Return, compile_Tick]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED


Theorem compile_correct:
  ^fgoal (p,s)
Proof
  rw [] >>
  ‘FST (evaluate (p,s)) <> SOME Error’ by fs [] >>
  drule pan_simpProofTheory.compile_correct >>
  fs [] >> strip_tac >>
  fs [compile_def] >>
  metis_tac [pc_compile_correct]
QED

val _ = export_theory();
