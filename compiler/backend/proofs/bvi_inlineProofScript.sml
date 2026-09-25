(*
  Correctness of the CPR worker-wrapper BVI inliner. The cache [cs] is
  persistent across incremental compilation: a cache hit causes the
  matching call to be inlined, and cache entries are trusted only when
  their bodies and arities agree with the compiled code table.
*)
Theory bvi_inlineProof
Ancestors
  bvi_inline bviSem bviProps backendProps
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "fromAList_def"]

Theorem inline_exps_LENGTH[simp]:
  ∀cs es. LENGTH (inline_exps cs es) = LENGTH es
Proof
  Induct_on ‘es’ >> rw [inline_exp_def]
QED

Theorem remove_ticks_exps_LENGTH[simp]:
  ∀es. LENGTH (remove_ticks_exps es) = LENGTH es
Proof
  Induct_on ‘es’ >> rw [remove_ticks_exp_def]
QED

Theorem inline_exps_CONS[simp]:
  inline_exps cs (x::xs) = inline_exp cs x :: inline_exps cs xs
Proof
  rw [inline_exp_def]
QED

Theorem inline_exps_MAP:
  ∀cs es. inline_exps cs es = MAP (inline_exp cs) es
Proof
  Induct_on ‘es’ >> simp [inline_exp_def]
QED

Theorem inline_exps_REVERSE[simp]:
  ∀cs es. inline_exps cs (REVERSE es) = REVERSE (inline_exps cs es)
Proof
  simp [inline_exps_MAP, MAP_REVERSE]
QED

Theorem inline_exps_MAP_Var[simp]:
  ∀cs ns. inline_exps cs (MAP Var ns) = MAP Var ns
Proof
  Induct_on ‘ns’ >> simp [inline_exp_def]
QED

Theorem inline_exps_GENLIST_Var[simp]:
  ∀cs n. inline_exps cs (GENLIST Var n) = GENLIST Var n
Proof
  rpt gen_tac
  >> ‘GENLIST bvi$Var n = MAP bvi$Var (GENLIST I n)’
       by simp [MAP_GENLIST, o_DEF]
  >> pop_assum SUBST1_TAC
  >> simp []
QED

Theorem incremental_wrapper_example:
  ∃cs p1 p2.
    compile_inc LN
      [(10,0,LetCall 0 0 11 []
        (Op (BlockOp (Cons 7)) []))] = (cs,p1) ∧
    compile_inc cs
      [(12,0,Call 0 (SOME 10) [] NONE)] = (cs,p2) ∧
    p2 = [(12,0,
      Let [] (LetCall 0 0 11 [] (Op (BlockOp (Cons 7)) [])))]
Proof
  qexistsl
    [‘insert 10 (0,LetCall 0 0 11 []
        (Op (BlockOp (Cons 7)) [])) LN’,
     ‘[(10,0,LetCall 0 0 11 [] (Op (BlockOp (Cons 7)) []))]’,
     ‘[(12,0,Let []
        (LetCall 0 0 11 [] (Op (BlockOp (Cons 7)) [])))]’]
  >> EVAL_TAC
QED

Theorem canonical_wrapper_thm:
  ∀name arity body.
    canonical_wrapper name arity body ⇔
      ∃rets ticks worker tag.
        worker ≠ name ∧
        body =
          bvi$LetCall rets ticks worker (GENLIST bvi$Var arity)
            (bvi$Op (BlockOp (Cons tag))
               (REVERSE (GENLIST bvi$Var rets)))
Proof
  recInduct canonical_wrapper_ind
  >> simp [canonical_wrapper_def]
  >> metis_tac []
QED

Theorem wrapper_ok_inline_exp[simp]:
  wrapper_ok name arity body ⇒ inline_exp cs body = body
Proof
  rw [wrapper_ok_def, canonical_wrapper_thm]
  >> gvs [inline_exp_def]
QED

Theorem inline_all_MAP_FST:
  ∀cs prog. MAP FST (SND (inline_all cs prog)) = MAP FST prog
Proof
  Induct_on ‘prog’
  >> simp [inline_all_def, FORALL_PROD, UNCURRY]
QED

Theorem MAP_FST_remove_ticks_prog[simp]:
  ∀prog.
    MAP FST (MAP (λ(name,arity,body).
      (name,arity,remove_ticks_exp body)) prog) = MAP FST prog
Proof
  Induct_on ‘prog’ >> fs [FORALL_PROD]
QED

Theorem compile_inc_MAP_FST:
  compile_inc cs prog = (cs1,prog1) ⇒ MAP FST prog1 = MAP FST prog
Proof
  rw [compile_inc_def, UNCURRY]
  >> gvs [inline_all_MAP_FST]
QED

Theorem compile_inc_ALL_DISTINCT:
  compile_inc cs prog = (cs1,prog1) ∧ ALL_DISTINCT (MAP FST prog) ⇒
  ALL_DISTINCT (MAP FST prog1)
Proof
  metis_tac [compile_inc_MAP_FST]
QED

Theorem remove_ticks_get_code_labels:
  (∀e. get_code_labels (remove_ticks_exp e) = get_code_labels e) ∧
  (∀es. BIGUNION (set (MAP get_code_labels (remove_ticks_exps es))) =
        BIGUNION (set (MAP get_code_labels es)))
Proof
  ho_match_mp_tac remove_ticks_exp_ind
  >> rw [remove_ticks_exp_def, bviPropsTheory.get_code_labels_def]
  >> Cases_on ‘handler’
  >> gvs [bviPropsTheory.get_code_labels_def]
QED

Theorem remove_ticks_prog_code_labels:
  ∀prog.
    BIGUNION (set (MAP (get_code_labels o SND o SND)
      (MAP (λ(name,arity,body).
        (name,arity,remove_ticks_exp body)) prog))) =
    BIGUNION (set (MAP (get_code_labels o SND o SND) prog))
Proof
  Induct_on ‘prog’
  >> simp [FORALL_PROD, remove_ticks_get_code_labels]
QED

Theorem compile_inc_code_labels:
  compile_inc cs prog = (cs1,prog1) ⇒
  BIGUNION (set (MAP (get_code_labels o SND o SND) prog1)) =
  BIGUNION (set (MAP (get_code_labels o SND o SND)
    (SND (inline_all cs prog))))
Proof
  rw [compile_inc_def]
  >> pairarg_tac >> gvs [remove_ticks_prog_code_labels]
QED

Definition cache_code_labels_def:
  cache_code_labels (cs : (num # bvi$exp) num_map) =
    BIGUNION (set (MAP (bviProps$get_code_labels ∘ SND)
      (toList cs)))
End

Theorem lookup_cache_code_labels:
  lookup n cs = SOME (arity,body) ⇒
  bviProps$get_code_labels body ⊆ cache_code_labels cs
Proof
  rw [cache_code_labels_def, SUBSET_DEF]
  >> fs [MEM_MAP, MEM_toList]
  >> metis_tac [PAIR, FST, SND]
QED

Theorem cache_code_labels_insert:
  ∀name arity body cs.
    cache_code_labels (insert name (arity,body) cs) ⊆
      get_code_labels body ∪ cache_code_labels cs
Proof
  rw [cache_code_labels_def, SUBSET_DEF]
  >> fs [MEM_MAP, MEM_toList]
  >> Cases_on ‘k = name’
  >> gvs [lookup_insert]
  >> metis_tac [PAIR, FST, SND]
QED

Theorem bvi_mk_tick_get_code_labels[simp]:
  ∀n e. get_code_labels (bvi_mk_tick n e) = get_code_labels e
Proof
  Induct_on ‘n’
  >> fs [bvi_mk_tick_def, FUNPOW_SUC,
         bviPropsTheory.get_code_labels_def]
QED

Theorem inline_exp_code_labels:
  (∀cs e.
     get_code_labels (inline_exp cs e) ⊆
       get_code_labels e ∪ cache_code_labels cs) ∧
  (∀cs es.
     BIGUNION (set (MAP get_code_labels (inline_exps cs es))) ⊆
       BIGUNION (set (MAP get_code_labels es)) ∪ cache_code_labels cs)
Proof
  ho_match_mp_tac inline_exp_ind
  >> rw [inline_exp_def, bviPropsTheory.get_code_labels_def]
  >> rpt (TOP_CASE_TAC
          >> gvs [bviPropsTheory.get_code_labels_def])
  >> imp_res_tac lookup_cache_code_labels
  >> fs [SUBSET_DEF]
  >> metis_tac []
QED

Theorem inline_all_code_labels:
  ∀cs prog.
    BIGUNION (set (MAP (get_code_labels ∘ SND ∘ SND)
      (SND (inline_all cs prog)))) ⊆
      BIGUNION (set (MAP (get_code_labels ∘ SND ∘ SND) prog)) ∪
      cache_code_labels cs
Proof
  Induct_on ‘prog’
  >> simp [inline_all_def, FORALL_PROD, UNCURRY]
  >> qx_genl_tac [‘name’,‘arity’,‘body’,‘cs’]
  >> qmatch_goalsub_abbrev_tac ‘inline_all cs1 prog’
  >> ‘cache_code_labels cs1 ⊆
        get_code_labels body ∪ cache_code_labels cs’
       by (qspecl_then [‘cs’,‘body’] mp_tac
             (CONJUNCT1 inline_exp_code_labels)
           >> qspecl_then [‘name’,‘arity’,‘inline_exp cs body’,‘cs’]
                mp_tac cache_code_labels_insert
           >> rw [Abbr ‘cs1’, SUBSET_DEF]
           >> metis_tac [])
  >> first_x_assum (qspec_then ‘cs1’ mp_tac)
  >> qspecl_then [‘cs’,‘body’] mp_tac (CONJUNCT1 inline_exp_code_labels)
  >> fs [SUBSET_DEF]
  >> metis_tac []
QED

Theorem compile_prog_code_labels:
  compile_prog prog = (cs1,prog1) ⇒
  BIGUNION (set (MAP (get_code_labels ∘ SND ∘ SND) prog1)) ⊆
    BIGUNION (set (MAP (get_code_labels ∘ SND ∘ SND) prog))
Proof
  rw [compile_prog_def, compile_inc_def, UNCURRY]
  >> qspecl_then [‘LN’,‘prog’] mp_tac inline_all_code_labels
  >> gvs [remove_ticks_prog_code_labels, cache_code_labels_def,
          EVAL “toList LN”]
QED

Theorem subspt_insert_union_fresh:
  ∀cs old name value.
    subspt cs old ∧ name ∉ domain old ⇒
    subspt (insert name value cs)
      (union old (insert name value LN))
Proof
  rw [subspt_lookup]
  >> qmatch_assum_rename_tac
       ‘lookup key (insert name value cs) = SOME cached_value’
  >> Cases_on ‘key = name’
  >- gvs [lookup_insert, lookup_union, GSYM lookup_NONE_domain]
  >> gvs [lookup_insert]
  >> res_tac
  >> fs [lookup_union]
QED

Theorem inline_all_cache_subspt:
  ∀prog cs old final_cache out.
    inline_all cs prog = (final_cache,out) ∧
    subspt cs old ∧
    DISJOINT (set (MAP FST prog)) (domain old) ∧
    ALL_DISTINCT (MAP FST prog) ⇒
    subspt final_cache (union old (fromAList out))
Proof
  Induct_on ‘prog’
  >- simp [inline_all_def, fromAList_def, union_LN]
  >> simp [FORALL_PROD]
  >> qx_genl_tac
       [‘name’,‘arity’,‘body’,‘cs’,‘old’,‘final_cache’,‘out’]
  >> simp [inline_all_def, UNCURRY]
  >> strip_tac
  >> gvs []
  >> qmatch_goalsub_abbrev_tac ‘inline_all cs1 prog’
  >> ‘subspt cs1 (union old (insert name (arity,inline_exp cs body) LN))’
       by (rw [Abbr ‘cs1’]
           >- (irule subspt_insert_union_fresh
               >> fs [DISJOINT_DEF, EXTENSION]
               >> metis_tac [])
           >> irule subspt_trans
           >> qexists ‘old’
           >> fs [subspt_union])
  >> ‘DISJOINT (set (MAP FST prog))
        (domain (union old (insert name (arity,inline_exp cs body) LN)))’
       by (fs [domain_union, DISJOINT_DEF, EXTENSION]
           >> metis_tac [])
  >> once_rewrite_tac [fromAList_def]
  >> once_rewrite_tac [GSYM union_insert_LN]
  >> rewrite_tac [union_assoc]
  >> first_x_assum
       (qspecl_then
          [‘cs1’,‘union old (insert name (arity,inline_exp cs body) LN)’,
           ‘FST (inline_all cs1 prog)’,‘SND (inline_all cs1 prog)’] mp_tac)
  >> gvs []
QED

(* [exp_rel c] relates a source expression to its image under the inlining
   phase, where [c] is the transformed target code table.
   [exp_rel_inline] is the only rule that removes a Call boundary. *)
Inductive exp_rel:
[~Var:]
  (∀c n. exp_rel c (Var n) (Var n))
[~Force:]
  (∀c loc n. exp_rel c (Force loc n) (Force loc n))
[~If:]
  (∀c x1 x2 x3 y1 y2 y3.
     exp_rel c x1 y1 ∧ exp_rel c x2 y2 ∧ exp_rel c x3 y3 ⇒
     exp_rel c (If x1 x2 x3) (If y1 y2 y3))
[~Let:]
  (∀c xs ys x y.
     LIST_REL (exp_rel c) xs ys ∧ exp_rel c x y ⇒
     exp_rel c (Let xs x) (Let ys y))
[~Raise:]
  (∀c x y. exp_rel c x y ⇒ exp_rel c (Raise x) (Raise y))
[~Tick:]
  (∀c x y. exp_rel c x y ⇒ exp_rel c (Tick x) (Tick y))
[~Op:]
  (∀c op xs ys. LIST_REL (exp_rel c) xs ys ⇒
     exp_rel c (Op op xs) (Op op ys))
[~Call:]
  (∀c ticks dest xs ys handler handler1.
     LIST_REL (exp_rel c) xs ys ∧ OPTREL (exp_rel c) handler handler1 ⇒
     exp_rel c (bvi$Call ticks dest xs handler)
       (bvi$Call ticks dest ys handler1))
[~LetCall:]
  (∀c rets ticks dest xs ys x y.
     LIST_REL (exp_rel c) xs ys ∧ exp_rel c x y ⇒
     exp_rel c (LetCall rets ticks dest xs x)
       (LetCall rets ticks dest ys y))
[~Return:]
  (∀c xs ys. LIST_REL (exp_rel c) xs ys ⇒
     exp_rel c (Return xs) (Return ys))
[~inline:]
  (∀c ticks n xs ys arity body.
     LIST_REL (exp_rel c) xs ys ∧ lookup n c = SOME (arity,body) ∧
     LENGTH ys = arity ⇒
     exp_rel c (bvi$Call ticks (SOME n) xs NONE)
       (Let ys (bvi_mk_tick (SUC ticks) body)))
End

Theorem exp_rel_mono:
  ∀c x y. exp_rel c x y ⇒ ∀c1. subspt c c1 ⇒ exp_rel c1 x y
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> simp [Once exp_rel_cases]
  >> gvs [LIST_REL_EL_EQN, OPTREL_def]
  >> metis_tac [subspt_lookup]
QED

Theorem exp_rel_mono_list:
  LIST_REL (exp_rel c) xs ys ∧ subspt c c1 ⇒ LIST_REL (exp_rel c1) xs ys
Proof
  gvs [LIST_REL_EL_EQN]
  >> metis_tac [exp_rel_mono]
QED

Theorem exp_rel_evaluate_mono[local]:
  (evaluate (es,env,t) = (res,t1) ∧ exp_rel t.code x y ⇒
     exp_rel t1.code x y) ∧
  (evaluate (es,env,t) = (res,t1) ∧ LIST_REL (exp_rel t.code) xs ys ⇒
     LIST_REL (exp_rel t1.code) xs ys)
Proof
  rw []
  >> imp_res_tac evaluate_code_mono
  >> metis_tac [exp_rel_mono, exp_rel_mono_list]
QED

Theorem exp_rel_refl[simp]:
  ∀c x. exp_rel c x x
Proof
  qsuff_tac
    ‘(∀e c. exp_rel c e e) ∧
     (∀handler c. OPTREL (exp_rel c) handler handler) ∧
     (∀xs c. LIST_REL (exp_rel c) xs xs)’
  >- metis_tac []
  >> ho_match_mp_tac bviTheory.exp_induction
  >> rpt strip_tac
  >> gvs [OPTREL_THM]
  >> metis_tac [exp_rel_rules]
QED

Theorem inline_call_none_exp_rel:
  subspt cs c ∧ LIST_REL (exp_rel c) es (inline_exps cs es) ⇒
  exp_rel c (Call ticks dest es NONE)
    (inline_exp cs (Call ticks dest es NONE))
Proof
  strip_tac
  >> once_rewrite_tac [inline_exp_def]
  >> namedCases_on ‘dest’ ["", "name"]
  >> simp []
  >- metis_tac [exp_rel_rules, OPTREL_THM]
  >> namedCases_on ‘lookup name cs’ ["", "cached"]
  >> simp []
  >- metis_tac [exp_rel_rules, OPTREL_THM]
  >> PairCases_on ‘cached’
  >> qmatch_assum_rename_tac ‘lookup name cs = SOME (arity,body)’
  >> simp []
  >> IF_CASES_TAC
  >- (irule exp_rel_inline
      >> simp []
      >> metis_tac [subspt_lookup])
  >> metis_tac [exp_rel_rules, OPTREL_THM]
QED

Theorem inline_exp_rel:
  subspt cs c ⇒
    (∀e. exp_rel c e (inline_exp cs e)) ∧
    (∀es. LIST_REL (exp_rel c) es (inline_exps cs es))
Proof
  qsuff_tac
    ‘(∀cs e. subspt cs c ⇒ exp_rel c e (inline_exp cs e)) ∧
     (∀cs es. subspt cs c ⇒
       LIST_REL (exp_rel c) es (inline_exps cs es))’
  >- metis_tac []
  >> ho_match_mp_tac inline_exp_ind
  >> rpt strip_tac
  >~ [‘bvi$Call _ _ _ handler’]
  >- (Cases_on ‘handler’
      >- (irule inline_call_none_exp_rel
          >> fs [])
      >> once_rewrite_tac [inline_exp_def]
      >> fs []
      >> metis_tac [exp_rel_rules, OPTREL_THM])
  >> once_rewrite_tac [inline_exp_def]
  >> gvs []
  >> metis_tac [exp_rel_rules]
QED

Theorem evaluate_bvi_mk_tick:
  ∀exp env s n.
    evaluate ([bvi_mk_tick n exp],env,s) =
      if s.clock < n then
        (Rerr (Rabort Rtimeout_error),s with clock := 0)
      else evaluate ([exp],env,dec_clock n s)
Proof
  Induct_on `n`
  >- simp [bvi_mk_tick_def, dec_clock_def, FUNPOW]
  >> rpt gen_tac
  >> simp [bvi_mk_tick_def, FUNPOW_SUC, Once evaluate_def]
  >> Cases_on `s.clock = 0`
  >- fs [state_component_equality]
  >> qpat_x_assum `∀exp env s. _`
       (qspecl_then [`exp`,`env`,`dec_clock 1 s`] assume_tac)
  >> fs [bvi_mk_tick_def, dec_clock_def]
  >> `(s.clock < n + 1 ∧ 0 < n) ⇔ s.clock < SUC n`
       by (qpat_x_assum `s.clock ≠ 0` mp_tac >> simp [ADD1] >> decide_tac)
  >> fs [ADD1]
QED

Theorem evaluate_expand_env:
  ∀xs a s env.
    FST (evaluate (xs,a,s)) ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate (xs,a ++ env,s) = evaluate (xs,a,s)
Proof
  recInduct evaluate_ind
  >> rpt strip_tac
  >> pop_assum mp_tac
  >> once_rewrite_tac [evaluate_def]
  >> asm_simp_tac std_ss []
  >> rpt (TOP_CASE_TAC >> gvs [rich_listTheory.EL_APPEND1])
QED

Definition in_cc_def:
  in_cc cc =
    (λ(cs,cfg) prog.
       let (cs1,prog1) = inline_all cs prog in
         case cc cfg prog1 of
         | NONE => NONE
         | SOME (code,data,cfg1) => SOME (code,data,(cs1,cfg1)))
End

Definition in_co_def:
  in_co co =
    (λn.
       let ((cs,cfg),prog) = co n in
       let (cs1,prog1) = inline_all cs prog in
         (cfg,prog1))
End

Definition in_state_rel_def:
  in_state_rel s (t:('c,'ffi) bviSem$state) ⇔
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = in_co s.compile_oracle ∧
    subspt (FST (FST (s.compile_oracle 0))) t.code ∧
    s.compile = in_cc t.compile ∧
    domain t.code = domain s.code ∧
    (∀k arity exp.
       lookup k s.code = SOME (arity,exp) ⇒
       ∃exp1. lookup k t.code = SOME (arity,exp1) ∧
              exp_rel t.code exp exp1)
End

Theorem in_state_rel_find_code[local]:
  ∀s t dest vs args exp.
    in_state_rel s t ∧
    find_code dest vs s.code = SOME (args,exp) ⇒
    ∃exp1. find_code dest vs t.code = SOME (args,exp1) ∧
      exp_rel t.code exp exp1
Proof
  rpt strip_tac
  >> Cases_on ‘dest’
  >> fs [bvlSemTheory.find_code_def, in_state_rel_def, AllCaseEqs()]
  >> metis_tac []
QED

Theorem inline_all_ALOOKUP:
  ∀prog cs old_target final_cache out k wanted_arity wanted_body.
    inline_all cs prog = (final_cache,out) ∧
    subspt cs old_target ∧
    DISJOINT (set (MAP FST prog)) (domain old_target) ∧
    ALL_DISTINCT (MAP FST prog) ∧
    ALOOKUP prog k = SOME (wanted_arity,wanted_body) ⇒
    ∃body1.
      ALOOKUP out k = SOME (wanted_arity,body1) ∧
      exp_rel (union old_target (fromAList out)) wanted_body body1
Proof
  Induct_on ‘prog’
  >- simp [inline_all_def]
  >> simp [FORALL_PROD]
  >> qx_genl_tac
       [‘head_name’,‘head_arity’,‘head_body’,‘cs’,‘old_target’,
        ‘final_cache’,‘out’,‘k’,‘wanted_arity’,‘wanted_body’]
  >> simp [inline_all_def, UNCURRY]
  >> strip_tac
  >> gvs []
  >> qmatch_goalsub_abbrev_tac ‘inline_all cs1 prog’
  >> Cases_on ‘k = head_name’
  >- (gvs []
      >> ‘subspt cs
            (union old_target
              (fromAList
                ((head_name,head_arity,inline_exp cs head_body)::
                 SND (inline_all cs1 prog))))’
           by (irule subspt_trans
               >> qexists ‘old_target’
               >> simp [subspt_union])
      >> drule inline_exp_rel
      >> simp [])
  >> ‘subspt cs1
        (union old_target
          (insert head_name (head_arity,inline_exp cs head_body) LN))’
       by (rw [Abbr ‘cs1’]
           >- (irule subspt_insert_union_fresh
               >> fs [DISJOINT_DEF, EXTENSION]
               >> metis_tac [])
           >> irule subspt_trans
           >> qexists ‘old_target’
           >> fs [subspt_union])
  >> ‘DISJOINT (set (MAP FST prog))
        (domain
          (union old_target
            (insert head_name (head_arity,inline_exp cs head_body) LN)))’
       by (fs [domain_union, DISJOINT_DEF, EXTENSION]
           >> metis_tac [])
  >> once_rewrite_tac [fromAList_def]
  >> once_rewrite_tac [GSYM union_insert_LN]
  >> rewrite_tac [union_assoc]
  >> first_x_assum
       (qspecl_then
          [‘cs1’,
           ‘union old_target
             (insert head_name (head_arity,inline_exp cs head_body) LN)’,
           ‘FST (inline_all cs1 prog)’,‘SND (inline_all cs1 prog)’,
           ‘k’,‘wanted_arity’,‘wanted_body’] mp_tac)
  >> gvs []
QED

Theorem do_app_state_swap[local]:
  op ≠ Install ⇒
    ((do_app op args s = Rval (value,s1) ∧
      domain s.code ⊆ domain t.code ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rval
        (value,
         t with <| refs := s1.refs; clock := s1.clock;
                   global := s1.global; ffi := s1.ffi |>)) ∧
     (do_app op args s = Rerr error ∧
      (domain t.code ⊆ domain s.code ∨
       error ≠ Rabort Rtype_error) ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rerr error))
Proof
  strip_tac
  >> Cases_on `op`
  >> gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def, bvl_to_bvi_def,
          bvlSemTheory.do_app_def, AllCaseEqs(), state_component_equality,
          SUBSET_DEF, pairTheory.ELIM_UNCURRY]
  >> rpt strip_tac
  >> gvs []
  >- metis_tac []
  >> qmatch_asmsub_rename_tac
       `s.refs |+ (global_ptr,
                   ValueArray (LUPDATE new_value set_index global_values)) =
        s1.refs`
  >> qexists_tac
       `SOME (Unit,
              t with
                <| refs := s.refs |+ (global_ptr,
                     ValueArray (LUPDATE new_value set_index global_values));
                   clock := s1.clock; global := s1.global; ffi := s1.ffi |>)`
  >> conj_tac
  >- (qexists_tac `global_ptr` >> gvs [])
  >> disj2_tac
  >> gvs []
QED

Theorem do_app_state_swap_Rval[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (source_state:('c,'ffi) bviSem$state)
      (t:('d,'ffi) bviSem$state) value.
    op ≠ Install ∧
    do_app op args s = Rval (value,source_state) ∧
    domain s.code ⊆ domain t.code ⇒
    do_app op args
      (t with <| refs := s.refs; clock := s.clock;
                 global := s.global; ffi := s.ffi |>) =
    Rval
      (value,
       t with <| refs := source_state.refs; clock := source_state.clock;
                  global := source_state.global; ffi := source_state.ffi |>)
Proof
  rpt strip_tac
  >> metis_tac [do_app_state_swap]
QED

Theorem do_app_state_swap_Rerr[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (t:('d,'ffi) bviSem$state) error.
    op ≠ Install ∧
    do_app op args s = Rerr error ∧
    (domain t.code ⊆ domain s.code ∨ error ≠ Rabort Rtype_error) ⇒
    do_app op args
      (t with <| refs := s.refs; clock := s.clock;
                 global := s.global; ffi := s.ffi |>) = Rerr error
Proof
  rpt strip_tac
  >> metis_tac [do_app_state_swap]
QED

Theorem inline_all_head_names[local]:
  inline_all cs ((name,arity,body)::rest) = (final_cache,out) ⇒
  ∃tail.
    out = (name,arity,inline_exp cs body)::tail ∧
    MAP FST tail = MAP FST rest
Proof
  rw [inline_all_def]
  >> pairarg_tac
  >> gvs []
  >> qspecl_then [`cs`,`(name,arity,body)::rest`] mp_tac inline_all_MAP_FST
  >> simp [inline_all_def, UNCURRY]
QED

Theorem inline_all_lookup_union[local]:
  inline_all cs prog = (final_cache,out) ∧
  subspt cs target ∧
  domain target = domain source ∧
  (∀k arity exp. lookup k source = SOME (arity,exp) ⇒
     ∃exp1. lookup k target = SOME (arity,exp1) ∧
            exp_rel target exp exp1) ∧
  DISJOINT (set (MAP FST prog)) (domain target) ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  ∀k arity exp.
    lookup k (union source (fromAList prog)) = SOME (arity,exp) ⇒
    ∃exp1.
      lookup k (union target (fromAList out)) = SOME (arity,exp1) ∧
      exp_rel (union target (fromAList out)) exp exp1
Proof
  rpt strip_tac
  >> namedCases_on `lookup k source` ["", "entry"]
  >- (gvs [lookup_union, lookup_fromAList]
      >> `DISJOINT (set (MAP FST prog)) (domain target)` by gvs []
      >> drule_all inline_all_ALOOKUP
      >> strip_tac
      >> `lookup k target = NONE` by gvs [lookup_NONE_domain]
      >> gvs [lookup_union, lookup_fromAList])
  >> gvs [lookup_union]
  >> first_x_assum drule
  >> strip_tac
  >> gvs [lookup_union]
  >> metis_tac [exp_rel_mono, subspt_union]
QED

Theorem do_install_Rerr_type[local]:
  ∀args (s:('c,'ffi) bviSem$state) error.
    do_install args s = Rerr error ⇒
    error = Rabort Rtype_error
Proof
  rpt strip_tac
  >> fs [do_install_def, case_eq_thms, UNCURRY]
QED

Theorem in_state_rel_do_install[local]:
  in_state_rel s1 t1 ⇒
    case do_install a s1 of
    | Rerr err =>
        (err ≠ Rabort Rtype_error ⇒ do_install a t1 = Rerr err)
    | Rval (v,s2) =>
        ∃t2. in_state_rel s2 t2 ∧ do_install a t1 = Rval (v,t2)
Proof
  strip_tac
  >> reverse TOP_CASE_TAC
  >- (strip_tac >> imp_res_tac do_install_Rerr_type >> gvs [])
  >> rename1 `do_install a s1 = Rval install_res`
  >> PairCases_on `install_res`
  >> gvs [do_install_def, AllCaseEqs(), UNCURRY]
  >> qexists_tac
       `t1 with <| compile_oracle := shift_seq 1 t1.compile_oracle;
                   code := union t1.code
                             (fromAList (SND (t1.compile_oracle 0))) |>`
  >> gvs [in_state_rel_def, in_co_def, in_cc_def, shift_seq_def, o_DEF]
  >> `∃oracle_cs oracle_cfg oracle_progs.
        s1.compile_oracle 0 = ((oracle_cs,oracle_cfg),oracle_progs)`
       by metis_tac [PAIR]
  >> gvs []
  >> pairarg_tac
  >> gvs []
  >> `∃prog_arity prog_body. prog = (prog_arity,prog_body)` by metis_tac [PAIR]
  >> gvs []
  >> drule inline_all_head_names
  >> strip_tac
  >> gvs [domain_fromAList, AllCaseEqs()]
  >> `∃next_cs next_cfg next_progs.
        s1.compile_oracle 1 = ((next_cs,next_cfg),next_progs)`
       by metis_tac [PAIR]
  >> gvs [UNCURRY]
  >> conj_tac
  >- (irule inline_all_cache_subspt
      >> qexistsl [`oracle_cs`,`(k,prog_arity,prog_body)::v7`]
      >> gvs [DISJOINT_SYM])
  >> rpt gen_tac
  >> strip_tac
  >> irule inline_all_lookup_union
  >> qexistsl [`oracle_cs`,`cs1`,`(k,prog_arity,prog_body)::v7`,`s1.code`]
  >> gvs [DISJOINT_SYM]
QED

Theorem in_do_app_lemma[local]:
  in_state_rel s1 t1 ⇒
    case do_app op a s1 of
    | Rerr err =>
        (err ≠ Rabort Rtype_error ⇒ do_app op a t1 = Rerr err)
    | Rval (v,s2) =>
        ∃t2. in_state_rel s2 t2 ∧ do_app op a t1 = Rval (v,t2)
Proof
  strip_tac
  >> Cases_on `op = Install`
  >- gvs [do_app_def, in_state_rel_do_install]
  >> `t1 with <| refs := s1.refs; clock := s1.clock; global := s1.global;
                 ffi := s1.ffi |> = t1`
       by gvs [in_state_rel_def, state_component_equality]
  >> `domain s1.code ⊆ domain t1.code ∧ domain t1.code ⊆ domain s1.code`
       by gvs [in_state_rel_def]
  >> reverse TOP_CASE_TAC
  >- (rename1 `do_app op a s1 = Rerr app_err`
      >> strip_tac
      >> qspecl_then [`op`,`a`,`s1`,`t1`,`app_err`] mp_tac do_app_state_swap_Rerr
      >> gvs [])
  >> rename1 `do_app op a s1 = Rval app_res`
  >> PairCases_on `app_res`
  >> gvs []
  >> drule_all do_app_state_swap_Rval
  >> gvs []
  >> strip_tac
  >> imp_res_tac do_app_code
  >> imp_res_tac do_app_oracle
  >> gvs [in_state_rel_def]
QED

(* Inversion of [exp_rel] on each source constructor. [~inline] is why the
   Call clause has a second disjunct. *)
Theorem exp_rel_inv[local,simp]:
  (exp_rel c (Var n) y ⇔ y = Var n) ∧
  (exp_rel c (Force loc n) y ⇔ y = Force loc n) ∧
  (exp_rel c (If x1 x2 x3) y ⇔
     ∃y1 y2 y3. y = If y1 y2 y3 ∧ exp_rel c x1 y1 ∧ exp_rel c x2 y2 ∧
       exp_rel c x3 y3) ∧
  (exp_rel c (Let xs x) y ⇔
     ∃ys y1. y = Let ys y1 ∧ LIST_REL (exp_rel c) xs ys ∧ exp_rel c x y1) ∧
  (exp_rel c (Raise x) y ⇔ ∃y1. y = Raise y1 ∧ exp_rel c x y1) ∧
  (exp_rel c (Tick x) y ⇔ ∃y1. y = Tick y1 ∧ exp_rel c x y1) ∧
  (exp_rel c (Op op xs) y ⇔
     ∃ys. y = Op op ys ∧ LIST_REL (exp_rel c) xs ys) ∧
  (exp_rel c (Return xs) y ⇔
     ∃ys. y = Return ys ∧ LIST_REL (exp_rel c) xs ys) ∧
  (exp_rel c (LetCall rets ticks target xs x) y ⇔
     ∃ys y1. y = LetCall rets ticks target ys y1 ∧
       LIST_REL (exp_rel c) xs ys ∧ exp_rel c x y1) ∧
  (exp_rel c (bvi$Call ticks dest xs handler) y ⇔
     (∃ys handler1. y = bvi$Call ticks dest ys handler1 ∧
        LIST_REL (exp_rel c) xs ys ∧ OPTREL (exp_rel c) handler handler1) ∨
     (∃n ys arity body.
        dest = SOME n ∧ handler = NONE ∧
        y = Let ys (bvi_mk_tick (SUC ticks) body) ∧
        LIST_REL (exp_rel c) xs ys ∧ lookup n c = SOME (arity,body) ∧
        LENGTH ys = arity))
Proof
  rpt conj_tac
  >> simp [Once exp_rel_cases]
  >> metis_tac []
QED

(* The inlined form of a Call evaluates exactly like the Call it replaces:
   the extra environment entries are unreachable, and the two differ on a
   [Ret]-raise only, which the side condition excludes. *)
Theorem evaluate_inlined_call[local]:
  lookup n t.code = SOME (LENGTH ys,body) ∧
  FST (evaluate ([Call ticks (SOME n) ys NONE],env,t)) ≠
    Rerr (Rabort Rtype_error) ⇒
  evaluate ([Let ys (bvi_mk_tick (SUC ticks) body)],env,t) =
  evaluate ([Call ticks (SOME n) ys NONE],env,t)
Proof
  strip_tac
  >> gvs [evaluate_def, evaluate_bvi_mk_tick, bvlSemTheory.find_code_def]
  >> namedCases_on `evaluate (ys,env,t)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> drule bviPropsTheory.evaluate_IMP_LENGTH
  >> imp_res_tac evaluate_code_mono
  >> strip_tac
  >> `lookup n args_state.code = SOME (LENGTH args_vals,body)`
       by gvs [subspt_lookup]
  >> gvs [ADD1]
  >> IF_CASES_TAC
  >- simp []
  >> qspecl_then [`[body]`,`args_vals`,`dec_clock (ticks + 1) args_state`,`env`]
       mp_tac evaluate_expand_env
  >> namedCases_on
       `evaluate ([body],args_vals,dec_clock (ticks + 1) args_state)`
       ["body_res body_state"]
  >> namedCases_on `body_res` ["body_vals", "body_err"]
  >> gvs []
  >> namedCases_on `body_err` ["raised", "abort_kind"]
  >> gvs []
  >> namedCases_on `raised` ["exn_val", "ret_vals"]
  >> gvs []
QED

Theorem evaluate_inline:
  ∀es env s res s1 t es1.
    in_state_rel s t ∧ LIST_REL (exp_rel t.code) es es1 ∧
    evaluate (es,env,s) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t1. evaluate (es1,env,t) = (res,t1) ∧ in_state_rel s1 t1
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >- gvs [evaluate_def]
  >- suspend "CONS"
  >- suspend "Var"
  >- suspend "If"
  >- suspend "Let"
  >- suspend "Raise"
  >- suspend "Return"
  >- suspend "Op"
  >- suspend "Tick"
  >- suspend "Force"
  >- suspend "Call"
  >- suspend "LetCall"
QED

Resume evaluate_inline[CONS]:
  Cases_on `es1`
  >- gvs []
  >> gvs []
  >> qmatch_asmsub_rename_tac `exp_rel t.code x y1`
  >> qmatch_asmsub_rename_tac `exp_rel t.code y y2`
  >> qmatch_asmsub_rename_tac `LIST_REL (exp_rel t.code) xs ys2`
  >> qpat_x_assum `evaluate (_::_::_,_,_) = _` mp_tac
  >> once_rewrite_tac [evaluate_CONS]
  >> namedCases_on `evaluate ([x],env,s)` ["head_res head_state"]
  >> namedCases_on `head_res` ["head_vals", "head_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> namedCases_on `evaluate (y::xs,env,head_state)`
       ["tail_res tail_state"]
  >> namedCases_on `tail_res` ["tail_vals", "tail_err"]
  >> gvs []
  >> `exp_rel t1.code y y2 ∧ LIST_REL (exp_rel t1.code) xs ys2` by
       metis_tac [exp_rel_evaluate_mono]
  >> qpat_x_assum `∀t1 es. in_state_rel head_state t1 ∧ _ ⇒ _`
       (qspecl_then [`t1`,`y2::ys2`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED


Resume evaluate_inline[Var]:
  gvs [evaluate_def, AllCaseEqs()]
QED


Resume evaluate_inline[If]:
  gvs []
  >> qpat_x_assum `evaluate ([If _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate ([x1],env,s)` ["cond_res cond_state"]
  >> namedCases_on `cond_res` ["cond_vals", "cond_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `exp_rel t1.code x2 y2 ∧ exp_rel t1.code x3 y3` by
       metis_tac [exp_rel_evaluate_mono]
  >> Cases_on `HD cond_vals = Boolv T`
  >> gvs []
  >> Cases_on `HD cond_vals = Boolv F`
  >> gvs []
  >> metis_tac []
QED


Resume evaluate_inline[Let]:
  gvs []
  >> qpat_x_assum `evaluate ([Let _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["binds_res binds_state"]
  >> namedCases_on `binds_res` ["binds_vals", "binds_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `exp_rel t1.code x2 y1` by metis_tac [exp_rel_evaluate_mono]
  >> metis_tac []
QED


Resume evaluate_inline[Raise]:
  gvs []
  >> qpat_x_assum `evaluate ([Raise _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate ([x1],env,s)` ["sub_res sub_state"]
  >> namedCases_on `sub_res` ["sub_vals", "sub_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED


Resume evaluate_inline[Return]:
  gvs []
  >> qpat_x_assum `evaluate ([Return _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["ret_res ret_state"]
  >> namedCases_on `ret_res` ["ret_vals", "ret_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED


Resume evaluate_inline[Op]:
  gvs []
  >> qpat_x_assum `evaluate ([Op _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs [AllCaseEqs()]
  >> drule (Q.GEN `a` in_do_app_lemma)
  >> disch_then (qspecl_then [`op`,`REVERSE args_vals`] mp_tac)
  >> gvs []
  >> strip_tac
  >> gvs []
QED


Resume evaluate_inline[Tick]:
  gvs []
  >> `s.clock = t.clock` by gvs [in_state_rel_def]
  >> qpat_x_assum `evaluate ([Tick _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> IF_CASES_TAC
  >> gvs []
  >> strip_tac
  >> gvs []
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> qpat_x_assum `∀t1 es. in_state_rel (dec_clock 1 s) t1 ∧ _ ⇒ _`
       (qspecl_then [`dec_clock 1 t`,`[y1]`] mp_tac)
  >> simp []
QED


Resume evaluate_inline[Force]:
  gvs []
  >> `s.refs = t.refs ∧ s.clock = t.clock` by gvs [in_state_rel_def]
  >> gvs [AllCaseEqs(), evaluate_def, oneline dest_thunk_def, PULL_EXISTS]
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >- gvs [in_state_rel_def]
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> qpat_x_assum `∀t1 y. in_state_rel (dec_clock 1 s) t1 ∧ _ ⇒ _`
       (qspecl_then [`dec_clock 1 t`,`exp1`] mp_tac)
  >> gvs [dec_clock_def]
  >> metis_tac []
QED


Resume evaluate_inline[Call]:
  qsuff_tac
    `∀ys handler1.
       LIST_REL (exp_rel t.code) xs ys ∧
       OPTREL (exp_rel t.code) handler handler1 ⇒
       ∃t1. evaluate ([Call ticks dest ys handler1],env,t) = (res,t1) ∧
            in_state_rel s1' t1`
  >- (strip_tac
      >> gvs []
      >> first_x_assum (qspec_then `ys` mp_tac)
      >> simp []
      >> strip_tac
      >> `FST (evaluate ([Call ticks (SOME n) ys NONE],env,t)) ≠
            Rerr (Rabort Rtype_error)` by simp []
      >> drule_all evaluate_inlined_call
      >> strip_tac
      >> gvs [])
  >> rpt strip_tac
  >> qpat_x_assum `LIST_REL _ [Call _ _ _ _] _` kall_tac
  >> `IS_SOME handler ⇔ IS_SOME handler1` by gvs [OPTREL_def]
  >> qpat_x_assum `evaluate ([Call _ _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on `evaluate (xs,env,s1)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s1 t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `t1.clock = args_state.clock` by gvs [in_state_rel_def]
  >> namedCases_on `find_code dest args_vals args_state.code`
       ["", "code_entry"]
  >> gvs []
  >> PairCases_on `code_entry`
  >> qmatch_asmsub_rename_tac
       `find_code dest args_vals args_state.code = SOME (body_args,body_exp)`
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >> `in_state_rel (args_state with clock := 0) (t1 with clock := 0) ∧
      in_state_rel (dec_clock (ticks + 1) args_state)
        (dec_clock (ticks + 1) t1)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on
       `evaluate ([body_exp],body_args,dec_clock (ticks + 1) args_state)`
       ["body_res body_state"]
  >> `body_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum
       `∀res1 st t' es. in_state_rel (dec_clock (ticks + 1) args_state) t' ∧
          _ ⇒ _`
       (qspecl_then
          [`body_res`,`body_state`,`dec_clock (ticks + 1) t1`,`[exp1]`] mp_tac)
  >> simp [dec_clock_def]
  >> strip_tac
  >> gvs []
  >> namedCases_on `body_res` ["body_vals", "body_err"]
  >> gvs []
  >> namedCases_on `body_err` ["raised", "abort_kind"]
  >> gvs []
  >> namedCases_on `raised` ["exn_val", "ret_vals"]
  >> gvs []
  >> namedCases_on `handler` ["", "handler_exp"]
  >> gvs [OPTREL_def]
  >> qmatch_asmsub_rename_tac `exp_rel t.code handler_exp handler_exp1`
  >> `subspt t.code t1'.code` by
       (imp_res_tac evaluate_code_mono
        >> gvs []
        >> metis_tac [subspt_trans])
  >> `exp_rel t1'.code handler_exp handler_exp1` by metis_tac [exp_rel_mono]
  >> namedCases_on `evaluate ([handler_exp],exn_val::env,body_state)`
       ["h_res h_state"]
  >> `h_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum `∀res1 st t' es. in_state_rel body_state t' ∧ _ ⇒ _`
       (qspecl_then [`h_res`,`h_state`,`t1'`,`[handler_exp1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> namedCases_on `h_res` ["h_vals", "h_err"]
  >> gvs []
  >> namedCases_on `h_err` ["h_raised", "h_abort"]
  >> gvs []
  >> namedCases_on `h_raised` ["h_exn", "h_ret"]
  >> gvs []
QED

Resume evaluate_inline[LetCall]:
  gvs []
  >> qpat_x_assum `evaluate ([LetCall _ _ _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s1)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s1 t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `t1.clock = args_state.clock` by gvs [in_state_rel_def]
  >> namedCases_on `find_code (SOME dest) args_vals args_state.code`
       ["", "code_entry"]
  >> gvs []
  >> PairCases_on `code_entry`
  >> qmatch_asmsub_rename_tac
       `find_code (SOME dest) args_vals args_state.code =
          SOME (body_args,body_exp)`
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >> `in_state_rel (args_state with clock := 0) (t1 with clock := 0) ∧
      in_state_rel (dec_clock (ticks + 1) args_state)
        (dec_clock (ticks + 1) t1)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on
       `evaluate ([body_exp],body_args,dec_clock (ticks + 1) args_state)`
       ["body_res body_state"]
  >> `body_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum
       `∀res1 st t' es. in_state_rel (dec_clock (ticks + 1) args_state) t' ∧
          _ ⇒ _`
       (qspecl_then
          [`body_res`,`body_state`,`dec_clock (ticks + 1) t1`,`[exp1]`] mp_tac)
  >> simp [dec_clock_def]
  >> strip_tac
  >> gvs []
  >> namedCases_on `body_res` ["body_vals", "body_err"]
  >> gvs []
  >> namedCases_on `body_err` ["raised", "abort_kind"]
  >> gvs []
  >> namedCases_on `raised` ["exn_val", "ret_vals"]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> `subspt t.code t1'.code` by
       (imp_res_tac evaluate_code_mono
        >> gvs []
        >> metis_tac [subspt_trans])
  >> `exp_rel t1'.code y y1` by metis_tac [exp_rel_mono]
  >> qpat_x_assum `∀t' es. in_state_rel body_state t' ∧ _ ⇒ _`
       (qspecl_then [`t1'`,`[y1]`] mp_tac)
  >> simp []
QED


Finalise evaluate_inline;

Definition clean_prog_def:
  clean_prog prog =
    MAP (λ(name,arity,body). (name,arity,remove_ticks_exp body)) prog
End

Definition remove_ticks_cc_def:
  remove_ticks_cc cc = (λcfg prog. cc cfg (clean_prog prog))
End

Definition remove_ticks_co_def:
  remove_ticks_co = (I ## clean_prog)
End

Definition remove_state_rel_def:
  remove_state_rel (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) ⇔
    t.refs = s.refs ∧ t.clock = s.clock ∧ t.global = s.global ∧ t.ffi = s.ffi ∧
    t.code = map (I ## remove_ticks_exp) s.code ∧
    t.compile_oracle = remove_ticks_co ∘ s.compile_oracle ∧
    s.compile = remove_ticks_cc t.compile
End

Theorem remove_ticks_exps_NIL[simp]:
  remove_ticks_exps [] = []
Proof
  EVAL_TAC
QED

Theorem remove_state_rel_find_code_eq[local]:
  ∀s (t:('c,'ffi) bviSem$state).
    remove_state_rel s t ⇒
    ∀dest vs.
      find_code dest vs t.code =
        OPTION_MAP (I ## remove_ticks_exp) (find_code dest vs s.code)
Proof
  rpt strip_tac
  >> gvs [remove_state_rel_def]
  >> Cases_on `dest`
  >> gvs [bvlSemTheory.find_code_def, lookup_map]
  >> every_case_tac
  >> gvs []
QED

Theorem clock_sub_lt[local]:
  ∀x k:num. x ≠ 0 ∧ x ≤ k ⇒ x - 1 < k
Proof
  rpt strip_tac
  >> fs [NOT_ZERO]
  >> irule SUB_LESS
  >> fs []
QED

Theorem evaluate_add_extra_clock[local]:
  ∀xs env (s:('c,'ffi) bviSem$state) res s1 extra extra'.
    evaluate (xs,env,s with clock := extra + s.clock) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (xs,env,s with clock := extra + extra' + s.clock) =
      (res,s1 with clock := extra' + s1.clock)
Proof
  rpt strip_tac
  >> drule_all evaluate_add_clock
  >> disch_then (qspec_then `extra'` mp_tac)
  >> simp [inc_clock_def]
QED

Theorem clean_prog_CONS[local,simp]:
  clean_prog [] = [] ∧
  clean_prog (p::ps) = (I ## I ## remove_ticks_exp) p :: clean_prog ps
Proof
  simp [clean_prog_def, PAIR_MAP, ELIM_UNCURRY]
QED

Theorem clean_prog_simps[local,simp]:
  MAP FST (clean_prog prog) = MAP FST prog ∧
  map (I ## remove_ticks_exp) (fromAList prog) = fromAList (clean_prog prog)
Proof
  conj_tac
  >> Induct_on `prog`
  >> simp [clean_prog_def, fromAList_def, map_insert, FORALL_PROD]
QED

Theorem remove_state_rel_do_install[local]:
  ∀args (s:('c,'ffi) bviSem$state) t.
    remove_state_rel s t ⇒
      case do_install args s of
      | Rval (value,s1) =>
          ∃t1. do_install args t = Rval (value,t1) ∧ remove_state_rel s1 t1
      | Rerr err => do_install args t = Rerr err
Proof
  rpt strip_tac
  >> namedCases_on `s.compile_oracle 0` ["cfg progs"]
  >> TOP_CASE_TAC
  >> gvs [remove_state_rel_def, do_install_def, AllCaseEqs(), remove_ticks_co_def,
          remove_ticks_cc_def, shift_seq_def, domain_map, map_union, o_DEF]
QED

Theorem remove_state_rel_do_app[local]:
  ∀op args (s:('c,'ffi) bviSem$state) t.
    remove_state_rel s t ⇒
      case do_app op args s of
      | Rval (value,s1) =>
          ∃t1. do_app op args t = Rval (value,t1) ∧ remove_state_rel s1 t1
      | Rerr err => do_app op args t = Rerr err
Proof
  rpt strip_tac
  >> Cases_on `op = Install`
  >- gvs [do_app_def, remove_state_rel_do_install]
  >> `t with <| refs := s.refs; clock := s.clock; global := s.global;
                ffi := s.ffi |> = t`
       by gvs [remove_state_rel_def, state_component_equality]
  >> `domain s.code ⊆ domain t.code ∧ domain t.code ⊆ domain s.code`
       by gvs [remove_state_rel_def, domain_map]
  >> reverse (namedCases_on `do_app op args s` ["app_res", "app_err"])
  >- (gvs []
      >> qspecl_then [`op`,`args`,`s`,`t`,`app_err`] mp_tac do_app_state_swap_Rerr
      >> gvs [])
  >> PairCases_on `app_res`
  >> gvs []
  >> drule_all do_app_state_swap_Rval
  >> strip_tac
  >> imp_res_tac do_app_code
  >> imp_res_tac do_app_oracle
  >> gvs [remove_state_rel_def]
QED

Theorem evaluate_remove_ticks_mutual[local]:
  ∀k.
    (∀e env (t:('c,'ffi) bviSem$state) s res t1.
       remove_state_rel s t ∧ t.clock ≤ k ∧
       evaluate ([remove_ticks_exp e],env,t) = (res,t1) ⇒
       ∃extra s1.
         evaluate ([e],env,s with clock := s.clock + extra) =
           (res,s1) ∧ remove_state_rel s1 t1) ∧
    (∀es env (t:('c,'ffi) bviSem$state) s res t1.
       remove_state_rel s t ∧ t.clock ≤ k ∧
       evaluate (remove_ticks_exps es,env,t) = (res,t1) ⇒
       ∃extra s1.
         evaluate (es,env,s with clock := s.clock + extra) =
           (res,s1) ∧ remove_state_rel s1 t1)
Proof
  strip_tac
  >> completeInduct_on `k`
  >> fs [AND_IMP_INTRO]
  >> ho_match_mp_tac remove_ticks_exp_ind
  >> rw []
  >- suspend "Var"
  >- suspend "If"
  >- suspend "Let"
  >- suspend "Raise"
  >- suspend "Tick"
  >- suspend "Call"
  >- suspend "Force"
  >- suspend "Op"
  >- suspend "LetCall"
  >- suspend "Return"
  >- suspend "NIL"
  >- suspend "CONS"
QED

Resume evaluate_remove_ticks_mutual[Var]:
  gvs [remove_ticks_exp_def, evaluate_def, AllCaseEqs()]
  >> qexists_tac `0`
  >> gvs [remove_state_rel_def]
QED

Resume evaluate_remove_ticks_mutual[If]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
       ["cond_res cond_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`cond_res`,`cond_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`cond_extra`,`cond_src`] strip_assume_tac)
  >> reverse (namedCases_on `cond_res` ["cond_vals", "cond_err"])
  >- (gvs [] >> qexistsl [`cond_extra`,`cond_src`] >> gvs [])
  >> gvs []
  >> reverse (Cases_on `HD cond_vals = Boolv T ∨ HD cond_vals = Boolv F`)
  >- (gvs [] >> qexistsl [`cond_extra`,`cond_src`] >> gvs [])
  >> pop_assum strip_assume_tac
  >> gvs []
  >> `cond_state.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`extra1`,`src1`] strip_assume_tac)
  >> qspecl_then
       [`[e]`,`env`,`s`,`Rval cond_vals`,`cond_src`,`cond_extra`,`extra1`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`cond_extra + extra1`,`src1`]
  >> gvs []
QED

Resume evaluate_remove_ticks_mutual[Let]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`] strip_assume_tac)
  >> reverse (namedCases_on `args_res` ["args_vals", "args_err"])
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> gvs []
  >> `args_state.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`] strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval args_vals`,`args_src`,`args_extra`,`body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`args_extra + body_extra`,`body_src`]
  >> gvs []
QED

Resume evaluate_remove_ticks_mutual[Raise]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)` ["sub_res sub_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`sub_res`,`sub_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`sub_extra`,`sub_src`] strip_assume_tac)
  >> namedCases_on `sub_res` ["sub_vals", "sub_err"]
  >> gvs []
  >> qexistsl [`sub_extra`,`sub_src`]
  >> gvs []
QED

Resume evaluate_remove_ticks_mutual[Tick]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`sub_extra`,`sub_src`] strip_assume_tac)
  >> qexistsl [`SUC sub_extra`,`sub_src`]
  >> gvs [ADD1, dec_clock_def]
QED

Resume evaluate_remove_ticks_mutual[Call]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def, IS_SOME_MAP]
  >> IF_CASES_TAC
  >- (strip_tac >> qexists_tac `0` >> gvs [remove_state_rel_def])
  >> qpat_x_assum `¬(_ = NONE ∧ IS_SOME _)` kall_tac
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`] strip_assume_tac)
  >> imp_res_tac remove_state_rel_find_code_eq
  >> reverse (namedCases_on `args_res` ["arg_vals", "arg_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> strip_tac
  >> namedCases_on `find_code dest arg_vals args_src.code` ["", "callee"]
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> PairCases_on `callee`
  >> `args_src.clock = args_st.clock` by gvs [remove_state_rel_def]
  >> gvs []
  >> Cases_on `args_st.clock = 0`
  >- (gvs []
      >> qexistsl [`args_extra`,`args_src with clock := 0`]
      >> gvs [remove_state_rel_def])
  >> gvs []
  >> namedCases_on
       `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1 args_st)`
       ["body_res body_st"]
  >> `args_st.clock - 1 < k`
       by (irule clock_sub_lt >> imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `args_st.clock - 1` mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 args_src) (dec_clock 1 args_st) ∧
      (dec_clock 1 args_st).clock ≤ args_st.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`] strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> reverse (Cases_on `∃exn_val handle_exp.
                body_res = Rerr (Rraise (Exn exn_val)) ∧
                handler = SOME handle_exp`)
  >- (qexistsl [`args_extra + (ticks + body_extra)`,`body_src`]
      >> gvs [dec_clock_def, AllCaseEqs()])
  >> gvs []
  >> namedCases_on `evaluate ([remove_ticks_exp handle_exp],exn_val::env,body_st)`
       ["handler_res handler_st"]
  >> `body_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1.
          _ ∧ _ ∧ evaluate ([remove_ticks_exp handle_exp],_,_) = _ ⇒ _`
       (qspecl_then
          [`exn_val::env`,`body_st`,`body_src`,`handler_res`,`handler_st`] mp_tac)
  >> simp []
  >> disch_then
       (qx_choosel_then [`handler_extra`,`handler_src`] strip_assume_tac)
  >> qspecl_then
       [`[callee1]`,`callee0`,`dec_clock 1 args_src`,
        `Rerr (Rraise (Exn exn_val))`,`body_src`,`body_extra`,`handler_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra + handler_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl
       [`args_extra + (ticks + body_extra + handler_extra)`,`handler_src`]
  >> gvs [dec_clock_def, AllCaseEqs()]
QED

Resume evaluate_remove_ticks_mutual[Force]:
  `t.refs = s.refs ∧ t.clock = s.clock` by gvs [remove_state_rel_def]
  >> drule remove_state_rel_find_code_eq
  >> strip_tac
  >> qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> strip_tac
  >> reverse (Cases_on `n < LENGTH env ∧
                        ∃thunk_val callee_env callee_body.
                          dest_thunk (EL n env) s.refs =
                            IsThunk NotEvaluated thunk_val ∧
                          find_code (SOME loc) [EL n env; thunk_val] s.code =
                            SOME (callee_env,callee_body)`)
  >- (gvs [AllCaseEqs()] >> qexists_tac `0` >> gvs [remove_state_rel_def])
  >> gvs [AllCaseEqs()]
  >- (qexistsl [`0`,`s with clock := 0`] >> gvs [remove_state_rel_def])
  >> `s.clock - 1 < k` by (irule clock_sub_lt >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `s.clock - 1` mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 s) (dec_clock 1 t) ∧
      (dec_clock 1 t).clock ≤ s.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`] strip_assume_tac)
  >> qexistsl [`body_extra`,`body_src`]
  >> gvs [dec_clock_def]
QED

Resume evaluate_remove_ticks_mutual[Op]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`] strip_assume_tac)
  >> reverse (namedCases_on `args_res` ["args_vals", "args_err"])
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> gvs []
  >> qspecl_then [`op`,`REVERSE args_vals`,`args_src`,`args_st`]
       mp_tac remove_state_rel_do_app
  >> simp []
  >> namedCases_on `do_app op (REVERSE args_vals) args_src`
       ["app_res", "app_err"]
  >- (PairCases_on `app_res`
      >> gvs []
      >> strip_tac
      >> qexists_tac `args_extra`
      >> gvs [])
  >> gvs []
  >> strip_tac
  >> qexistsl [`args_extra`,`args_src`]
  >> gvs []
QED

Resume evaluate_remove_ticks_mutual[LetCall]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`] strip_assume_tac)
  >> imp_res_tac remove_state_rel_find_code_eq
  >> reverse (namedCases_on `args_res` ["arg_vals", "arg_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> strip_tac
  >> namedCases_on `find_code (SOME dest) arg_vals args_src.code` ["", "callee"]
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> PairCases_on `callee`
  >> `args_src.clock = args_st.clock` by gvs [remove_state_rel_def]
  >> gvs []
  >> Cases_on `args_st.clock = 0`
  >- (gvs []
      >> qexistsl [`args_extra`,`args_src with clock := 0`]
      >> gvs [remove_state_rel_def])
  >> gvs []
  >> namedCases_on
       `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1 args_st)`
       ["body_res body_st"]
  >> `args_st.clock - 1 < k`
       by (irule clock_sub_lt >> imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `args_st.clock - 1` mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 args_src) (dec_clock 1 args_st) ∧
      (dec_clock 1 args_st).clock ≤ args_st.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`] strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> reverse (Cases_on `∃ret_vals.
                body_res = Rerr (Rraise (Ret ret_vals)) ∧
                LENGTH ret_vals = rets`)
  >- (qexistsl [`args_extra + (ticks + body_extra)`,`body_src`]
      >> gvs [dec_clock_def, AllCaseEqs()])
  >> gvs []
  >> namedCases_on `evaluate ([remove_ticks_exp e],ret_vals ++ env,body_st)`
       ["cont_res cont_st"]
  >> `body_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
       (qspecl_then
          [`ret_vals ++ env`,`body_st`,`body_src`,`cont_res`,`cont_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`cont_extra`,`cont_src`] strip_assume_tac)
  >> qspecl_then
       [`[callee1]`,`callee0`,`dec_clock 1 args_src`,
        `Rerr (Rraise (Ret ret_vals))`,`body_src`,`body_extra`,`cont_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra + cont_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl
       [`args_extra + (ticks + body_extra + cont_extra)`,`cont_src`]
  >> gvs [dec_clock_def, AllCaseEqs()]
QED


Resume evaluate_remove_ticks_mutual[Return]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`] strip_assume_tac)
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> qexistsl [`args_extra`,`args_src`]
  >> gvs []
QED

Resume evaluate_remove_ticks_mutual[NIL]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> qexists_tac `0`
  >> gvs [remove_state_rel_def]
QED

Resume evaluate_remove_ticks_mutual[CONS]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def]
  >> namedCases_on `es` ["", "tail_head tail_rest"]
  >- (strip_tac
      >> qpat_x_assum
           `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
      >> gvs [])
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)` ["head_res head_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _ ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`head_res`,`head_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`head_extra`,`head_src`] strip_assume_tac)
  >> reverse (namedCases_on `head_res` ["head_vals", "head_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`head_extra`,`head_src`] >> gvs [])
  >> strip_tac
  >> namedCases_on
       `evaluate (remove_ticks_exps (tail_head::tail_rest),env,head_st)`
       ["tail_res tail_st"]
  >> `head_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1.
          _ ∧ _ ∧ evaluate (remove_ticks_exps (tail_head::tail_rest),_,_) = _ ⇒ _`
       (qspecl_then [`env`,`head_st`,`head_src`,`tail_res`,`tail_st`] mp_tac)
  >> simp [remove_ticks_exp_def]
  >> disch_then (qx_choosel_then [`tail_extra`,`tail_src`] strip_assume_tac)
  >> qspecl_then
       [`[e]`,`env`,`s`,`Rval head_vals`,`head_src`,`head_extra`,`tail_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`head_extra + tail_extra`,`tail_src`]
  >> gvs [remove_ticks_exp_def, AllCaseEqs()]
QED


Finalise evaluate_remove_ticks_mutual;

Theorem evaluate_remove_ticks:
  ∀k es env (t:('c,'ffi) bviSem$state) s res t1.
    remove_state_rel s t ∧ t.clock = k ∧
    evaluate (remove_ticks_exps es,env,t) = (res,t1) ⇒
    ∃extra s1.
      evaluate (es,env,s with clock := s.clock + extra) =
        (res,s1) ∧ remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> qspec_then `k` strip_assume_tac evaluate_remove_ticks_mutual
  >> qpat_x_assum
       `∀es env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _ ⇒ _`
       (qspecl_then [`es`,`env`,`t`,`s`,`res`,`t1`] mp_tac)
  >> simp []
QED

Theorem state_cc_compile_inc_eq:
  state_cc compile_inc cc = state_cc inline_all (remove_ticks_cc cc)
Proof
  rw [state_cc_def, compile_inc_def, remove_ticks_cc_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> gvs [clean_prog_def])
QED

Theorem state_co_compile_inc_eq:
  state_co compile_inc co = remove_ticks_co ∘ state_co inline_all co
Proof
  rw [state_co_def, compile_inc_def, remove_ticks_co_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> gvs [clean_prog_def])
QED

Theorem in_cc_eq_state_cc[local]:
  in_cc cc = state_cc inline_all cc
Proof
  rw [in_cc_def, state_cc_def, FUN_EQ_THM, FORALL_PROD]
  >> rpt (pairarg_tac >> fs [])
QED

Theorem in_co_eq_state_co[local]:
  in_co co = state_co inline_all co
Proof
  rw [in_co_def, state_co_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> fs [])
QED

Theorem evaluate_add_clock_io_events_mono[local]:
  ∀exps env (s:('c,'ffi) bviSem$state) k extra.
    (SND (evaluate (exps,env,s with clock := k))).ffi.io_events ≼
    (SND (evaluate (exps,env,s with clock := k + extra))).ffi.io_events
Proof
  rpt strip_tac
  >> qspecl_then [`exps`,`env`,`s with clock := k`,`extra`] mp_tac
       evaluate_add_to_clock_io_events_mono
  >> simp [inc_clock_def]
QED

Theorem inline_initial_state_rel[local]:
  ∀prog cs1 prog1 co ffi cc clk.
  inline_all LN prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  in_state_rel
    (initial_state ffi (fromAList prog) co (state_cc inline_all cc) clk)
    (initial_state ffi (fromAList prog1) (state_co inline_all co) cc clk)
Proof
  rpt strip_tac
  >> `MAP FST prog1 = MAP FST prog`
       by (qspecl_then [`LN`,`prog`] mp_tac inline_all_MAP_FST >> fs [])
  >> `subspt cs1 (fromAList prog1)`
       by (qspecl_then [`prog`,`LN`,`LN`,`cs1`,`prog1`] mp_tac
             inline_all_cache_subspt
           >> fs [union_LN])
  >> fs [in_state_rel_def, initial_state_def, domain_fromAList,
          GSYM in_co_eq_state_co, GSYM in_cc_eq_state_cc]
  >> rpt strip_tac
  >> qspecl_then [`prog`,`LN`,`LN`,`cs1`,`prog1`] mp_tac
       inline_all_ALOOKUP
  >> fs [lookup_fromAList, union_LN]
QED

Theorem evaluate_inline_compile[local]:
  ∀prog cs1 prog1 co ffi cc k start r s.
  inline_all LN prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ∧
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList prog) co (state_cc inline_all cc) k) =
      (r,s) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog1) (state_co inline_all co) cc k) =
        (r,s2) ∧
    in_state_rel s s2
Proof
  rpt strip_tac
  >> qspecl_then [`prog`,`cs1`,`prog1`,`co`,`ffi`,`cc`,`k`] mp_tac
       inline_initial_state_rel
  >> fs []
  >> strip_tac
  >> qspecl_then
       [`[Call 0 (SOME start) [] NONE]`,`[]`,
        `initial_state ffi (fromAList prog) co (state_cc inline_all cc) k`,
        `r`,`s`,
        `initial_state ffi (fromAList prog1) (state_co inline_all co) cc k`,
        `[Call 0 (SOME start) [] NONE]`] mp_tac evaluate_inline
  >> fs [exp_rel_refl]
QED

Theorem evaluate_remove_ticks_compile[local]:
  ∀prog co ffi cc k start r s.
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList (clean_prog prog))
      (remove_ticks_co ∘ co) cc k) = (r,s) ⇒
  ∃ck s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog) co (remove_ticks_cc cc) (k + ck)) =
        (r,s2) ∧
    s2.ffi = s.ffi
Proof
  rpt strip_tac
  >> qspecl_then
       [`k`,`[Call 0 (SOME start) [] NONE]`,`[]`,
        `initial_state ffi (fromAList (clean_prog prog))
           (remove_ticks_co ∘ co) cc k`,
        `initial_state ffi (fromAList prog) co (remove_ticks_cc cc) k`,
        `r`,`s`] mp_tac evaluate_remove_ticks
  >> fs [remove_ticks_exp_def, remove_state_rel_def, initial_state_def]
  >> disch_then (qx_choosel_then [`extra`,`s2`] strip_assume_tac)
  >> qexistsl [`extra`,`s2`]
  >> gvs [remove_state_rel_def]
QED

Theorem semantics_not_Fail_cond[local]:
  ∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ¬∃j e. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j)) = Rerr e ∧
      e ≠ Rabort Rtimeout_error ∧ ∀f. e ≠ Rabort (Rffi_error f)
Proof
  rpt strip_tac
  >> qpat_x_assum `semantics _ _ _ _ _ ≠ Fail` mp_tac
  >> simp [semantics_def]
  >> IF_CASES_TAC
  >- simp []
  >> fs []
  >> qpat_x_assum `∀a b. _` (qspecl_then [`j`,`e`] mp_tac)
  >> fs []
QED

Theorem semantics_error_cases[local]:
  ∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ∀j e t. evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j) = (Rerr e,t) ⇒
      e = Rabort Rtimeout_error ∨ ∃f. e = Rabort (Rffi_error f)
Proof
  rpt strip_tac
  >> drule semantics_not_Fail_cond
  >> rw []
  >> first_x_assum (qspecl_then [`j`,`e`] mp_tac)
  >> gvs []
QED

Theorem semantics_terminate_unique[local]:
  ∀ffi code co cc start k1 r1 t1 k2 r2 t2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc k1) = (r1,t1) ∧
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc k2) = (r2,t2) ∧
    r1 ≠ Rerr (Rabort Rtimeout_error) ∧
    r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
    r1 = r2 ∧ t1.ffi = t2.ffi
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ k1) = _` assume_tac
  >> drule evaluate_add_clock
  >> fs [inc_clock_def]
  >> disch_then (qspec_then `k2` assume_tac)
  >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ k2) = _` assume_tac
  >> drule evaluate_add_clock
  >> fs [inc_clock_def]
  >> disch_then (qspec_then `k1` assume_tac)
  >> fs [state_component_equality]
QED

Theorem semantics_no_type_error[local]:
  ∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ∀j. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j)) ≠ Rerr (Rabort Rtype_error)
Proof
  rpt strip_tac
  >> drule semantics_not_Fail_cond
  >> simp []
  >> qexistsl [`j`,`Rabort Rtype_error`]
  >> gvs []
QED

Theorem evaluate_compile_prog[local]:
  ∀prog cs1 prog1 co ffi cc k start r s.
  compile_prog prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ∧
  (∀j. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
         initial_state ffi (fromAList prog) co
           (state_cc compile_inc cc) j)) ≠ Rerr (Rabort Rtype_error)) ∧
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList prog1) (state_co compile_inc co) cc k) =
      (r,s) ⇒
  ∃ck s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog) co
        (state_cc compile_inc cc) (k + ck)) = (r,s2) ∧
    s2.ffi = s.ffi
Proof
  rpt strip_tac
  >> gvs [compile_prog_def, compile_inc_def]
  >> pairarg_tac
  >> gvs [state_co_compile_inc_eq, state_cc_compile_inc_eq]
  >> qspecl_then
       [`prog1'`,`state_co inline_all co`,`ffi`,`cc`,`k`,`start`,`r`,`s`]
       mp_tac evaluate_remove_ticks_compile
  >> fs [clean_prog_def]
  >> strip_tac
  >> namedCases_on
       `evaluate ([Call 0 (SOME start) [] NONE],[],
          initial_state ffi (fromAList prog) co
            (state_cc inline_all (remove_ticks_cc cc)) (k + ck))`
       ["src_res src_st"]
  >> `src_res ≠ Rerr (Rabort Rtype_error)`
       by (qpat_x_assum `∀j. FST _ ≠ _` (qspec_then `k + ck` mp_tac)
           >> fs [])
  >> qspecl_then
       [`prog`,`FST (FST (co 0))`,`prog1'`,`co`,`ffi`,`remove_ticks_cc cc`,
        `k + ck`,`start`,`src_res`,`src_st`] mp_tac evaluate_inline_compile
  >> fs []
  >> strip_tac
  >> qexistsl [`ck`,`src_st`]
  >> fs [in_state_rel_def]
QED

Theorem compile_prog_semantics:
  compile_prog prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  semantics ffi (fromAList prog) co (state_cc compile_inc cc) start ≠ Fail ⇒
  semantics ffi (fromAList prog1) (state_co compile_inc co) cc start =
  semantics ffi (fromAList prog) co (state_cc compile_inc cc) start
Proof
  rpt strip_tac
  >> imp_res_tac semantics_no_type_error
  >> imp_res_tac semantics_not_Fail_cond
  >> `∀k r s.
        evaluate ([Call 0 (SOME start) [] NONE],[],
          initial_state ffi (fromAList prog1)
            (state_co compile_inc co) cc k) = (r,s) ⇒
        ∃ck s2.
          evaluate ([Call 0 (SOME start) [] NONE],[],
            initial_state ffi (fromAList prog) co
              (state_cc compile_inc cc) (k + ck)) = (r,s2) ∧ s2.ffi = s.ffi`
       by (rpt strip_tac >> drule_all evaluate_compile_prog >> simp [])
  >> simp [Once semantics_def]
  >> IF_CASES_TAC
  >- (fs []
      >> namedCases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
           initial_state ffi (fromAList prog1) (state_co compile_inc co) cc k)`
           ["tgt_res tgt_st"]
      >> fs []
      >> `∃ck s2. evaluate ([Call 0 (SOME start) [] NONE],[],
            initial_state ffi (fromAList prog) co
              (state_cc compile_inc cc) (k + ck)) = (Rerr e,s2) ∧
            s2.ffi = tgt_st.ffi`
           by (qpat_assum `∀k r s. _`
                 (qspecl_then [`k`,`Rerr e`,`tgt_st`] mp_tac)
               >> fs [])
      >> fs []
      >> imp_res_tac semantics_error_cases
      >> fs [])
  >> DEEP_INTRO_TAC some_intro
  >> simp []
  >> conj_tac
  >- (rpt strip_tac
      >> rveq
      >> `∃ck s2. evaluate ([Call 0 (SOME start) [] NONE],[],
            initial_state ffi (fromAList prog) co
              (state_cc compile_inc cc) (k + ck)) = (r,s2) ∧ s2.ffi = s.ffi`
           by (qpat_assum `∀k r s. _` (qspecl_then [`k`,`r`,`s`] mp_tac)
               >> fs [])
      >> fs []
      >> simp [semantics_def]
      >> IF_CASES_TAC
      >- (qpat_x_assum `∃j e. _` mp_tac
          >> qpat_x_assum
               `∀j e. FST (evaluate (_,_,
                  initial_state _ _ _ (state_cc compile_inc cc) _)) ≠ _ ∨ _` mp_tac
          >> rpt (pop_assum kall_tac)
          >> simp []
          >> metis_tac [])
      >> DEEP_INTRO_TAC some_intro
      >> simp []
      >> conj_tac
      >- (gen_tac
          >> disch_then (qx_choosel_then
               [`alt_clk`,`alt_st`,`alt_res`,`alt_outcome`] strip_assume_tac)
          >> rveq
          >> `r ≠ Rerr (Rabort Rtimeout_error) ∧
              alt_res ≠ Rerr (Rabort Rtimeout_error)`
               by (rpt conj_tac >> strip_tac >> gvs [])
          >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ (ck + k)) = _`
               assume_tac
          >> drule semantics_terminate_unique
          >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ alt_clk) = _`
               assume_tac
          >> disch_then drule
          >> fs []
          >> rpt strip_tac
          >> gvs []
          >> every_case_tac
          >> gvs [])
      >> qexistsl [`ck + k`,`s2`,`r`,`outcome`]
      >> fs [])
  >> strip_tac
  >> simp [semantics_def]
  >> DEEP_INTRO_TAC some_intro
  >> simp []
  >> conj_tac
  >- (rpt strip_tac
      >> `r ≠ Rerr (Rabort Rtimeout_error)` by (strip_tac >> gvs [])
      >> namedCases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
           initial_state ffi (fromAList prog1)
             (state_co compile_inc co) cc k)` ["tgt_res tgt_st"]
      >> qpat_x_assum `∀k r s. _` (qspecl_then [`k`,`tgt_res`,`tgt_st`] mp_tac)
      >> fs []
      >> strip_tac
      >> qpat_x_assum `evaluate (_,_,
           initial_state _ (fromAList prog) _ _ k) = _` assume_tac
      >> drule evaluate_add_clock
      >> fs [inc_clock_def, initial_state_def]
      >> disch_then (qspec_then `ck` assume_tac)
      >> CCONTR_TAC
      >> fs []
      >> qpat_x_assum `∀a b c d. _`
           (qspecl_then [`k`,`tgt_st`,`r`,`outcome`] mp_tac)
      >> fs [])
  >> strip_tac
  >> qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  >> `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
       suffices_by metis_tac [build_lprefix_lub_thm, lprefix_lub_new_chain,
                              unique_lprefix_lub]
  >> conj_asm1_tac
  >- (unabbrev_all_tac
      >> conj_tac
      >> Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
      >> REWRITE_TAC [IMAGE_COMPOSE]
      >> match_mp_tac prefix_chain_lprefix_chain
      >> simp [prefix_chain_def, PULL_EXISTS]
      >> qx_genl_tac [`k1`,`k2`]
      >> qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
      >> metis_tac [LESS_EQ_EXISTS, initial_state_with_simp,
                    evaluate_add_clock_io_events_mono])
  >> simp [equiv_lprefix_chain_thm]
  >> unabbrev_all_tac
  >> simp [PULL_EXISTS]
  >> simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  >> rpt gen_tac
  >> namedCases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
       initial_state ffi (fromAList prog1)
         (state_co compile_inc co) cc k)` ["tgt_res tgt_st"]
  >> qpat_x_assum `∀k r s. _` (qspecl_then [`k`,`tgt_res`,`tgt_st`] mp_tac)
  >> fs []
  >> strip_tac
  >> conj_tac
  >- (rw [] >> qexists_tac `ck + k` >> fs [])
  >> rw []
  >> qexists_tac `k`
  >> fs []
  >> qmatch_assum_abbrev_tac `_ < LENGTH (_ src_ffi)`
  >> `src_ffi.io_events ≼ s2.ffi.io_events`
       by (qunabbrev_tac `src_ffi`
           >> metis_tac [initial_state_with_simp, SND, ADD_SYM,
                         evaluate_add_clock_io_events_mono])
  >> fs [IS_PREFIX_APPEND]
  >> gvs [EL_APPEND1]
QED

