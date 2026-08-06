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
  >> impl_tac
  >- fs []
  >> simp []
QED

(* [exp_rel c] relates source expressions to expressions transformed by the
   inlining phase, where [c] is the transformed target code table.
   [exp_rel_inline] is the only rule that removes a Call boundary. *)
Inductive exp_rel:
[~Var:]
  (∀c n. exp_rel c [Var n] [Var n])
[~nil:]
  (∀c. exp_rel c [] [])
[~cons:]
  (∀c x y xs ys.
     exp_rel c [x] [y] ∧ exp_rel c xs ys ⇒
     exp_rel c (x::xs) (y::ys))
[~If:]
  (∀c x1 x2 x3 y1 y2 y3.
     exp_rel c [x1] [y1] ∧ exp_rel c [x2] [y2] ∧
     exp_rel c [x3] [y3] ⇒
     exp_rel c [If x1 x2 x3] [If y1 y2 y3])
[~Let:]
  (∀c xs ys x y.
     exp_rel c xs ys ∧ exp_rel c [x] [y] ⇒
     exp_rel c [Let xs x] [Let ys y])
[~Raise:]
  (∀c x y. exp_rel c [x] [y] ⇒
     exp_rel c [Raise x] [Raise y])
[~Tick:]
  (∀c x y. exp_rel c [x] [y] ⇒
     exp_rel c [Tick x] [Tick y])
[~Force:]
  (∀c loc n. exp_rel c [Force loc n] [Force loc n])
[~Op:]
  (∀c op xs ys. exp_rel c xs ys ⇒
     exp_rel c [Op op xs] [Op op ys])
[~Call:]
  (∀c ticks dest xs ys.
     exp_rel c xs ys ⇒
     exp_rel c [Call ticks dest xs NONE] [Call ticks dest ys NONE])
[~Call_handler:]
  (∀c ticks dest xs ys h h1.
     exp_rel c xs ys ∧ exp_rel c [h] [h1] ⇒
     exp_rel c [Call ticks dest xs (SOME h)]
       [Call ticks dest ys (SOME h1)])
[~LetCall:]
  (∀c rets ticks dest xs ys x y.
     exp_rel c xs ys ∧ exp_rel c [x] [y] ⇒
     exp_rel c [LetCall rets ticks dest xs x]
       [LetCall rets ticks dest ys y])
[~Return:]
  (∀c xs ys. exp_rel c xs ys ⇒
     exp_rel c [Return xs] [Return ys])
[~inline:]
  (∀c ticks n xs ys arity body.
     exp_rel c xs ys ∧ lookup n c = SOME (arity,body) ∧
     LENGTH ys = arity ⇒
     exp_rel c [Call ticks (SOME n) xs NONE]
       [Let ys (bvi_mk_tick (SUC ticks) body)])
End

Theorem exp_rel_mono:
  ∀c xs ys. exp_rel c xs ys ⇒
    ∀c1. subspt c c1 ⇒ exp_rel c1 xs ys
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> metis_tac [exp_rel_rules, subspt_lookup]
QED

Theorem exp_rel_refl:
  ∀c xs. exp_rel c xs xs
Proof
  qsuff_tac
    ‘(∀e c. exp_rel c [e] [e]) ∧
     (∀handler c.
        case handler of
        | NONE => T
        | SOME h => exp_rel c [h] [h]) ∧
     (∀xs c. exp_rel c xs xs)’
  >- metis_tac []
  >> ho_match_mp_tac bviTheory.exp_induction
  >> rpt strip_tac
  >> every_case_tac
  >> gvs []
  >> metis_tac [exp_rel_rules]
QED

Theorem inline_call_none_exp_rel:
  subspt cs c ∧ exp_rel c es (inline_exps cs es) ⇒
  exp_rel c [Call ticks dest es NONE]
    [inline_exp cs (Call ticks dest es NONE)]
Proof
  rpt strip_tac
  >> Cases_on ‘dest’
  >- (once_rewrite_tac [inline_exp_def]
      >> fs []
      >> metis_tac [exp_rel_rules])
  >> qmatch_goalsub_rename_tac ‘Call ticks (SOME name) es NONE’
  >> namedCases_on ‘lookup name cs’ ["", "cached"]
  >- (once_rewrite_tac [inline_exp_def]
      >> fs []
      >> metis_tac [exp_rel_rules])
  >> PairCases_on ‘cached’
  >> qmatch_assum_rename_tac ‘lookup name cs = SOME (arity,body)’
  >> Cases_on ‘LENGTH (inline_exps cs es) = arity’
  >- (‘lookup name c = SOME (arity,body)’ by fs [subspt_lookup]
      >> once_rewrite_tac [inline_exp_def]
      >> fs []
      >> irule exp_rel_inline
      >> fs [])
  >> once_rewrite_tac [inline_exp_def]
  >> fs []
  >> metis_tac [exp_rel_rules]
QED

Theorem inline_exp_rel:
  subspt cs c ⇒
    (∀e. exp_rel c [e] [inline_exp cs e]) ∧
    (∀es. exp_rel c es (inline_exps cs es))
Proof
  qsuff_tac
    ‘(∀cs e. subspt cs c ⇒
       exp_rel c [e] [inline_exp cs e]) ∧
     (∀cs es. subspt cs c ⇒
       exp_rel c es (inline_exps cs es))’
  >- metis_tac []
  >> ho_match_mp_tac inline_exp_ind
  >> rpt strip_tac
  >~ [‘bvi$Call _ _ _ handler’]
  >- (Cases_on ‘handler’
      >- (irule inline_call_none_exp_rel
          >> fs [])
      >> once_rewrite_tac [inline_exp_def]
      >> fs []
      >> metis_tac [exp_rel_rules])
  >> once_rewrite_tac [inline_exp_def]
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
  >- (rpt gen_tac
      >> simp [bvi_mk_tick_def, FUNPOW_SUC, Once evaluate_def]
      >- (Cases_on `s.clock = 0`
          >- fs [state_component_equality]
          >- (qpat_x_assum `∀exp env s. _`
                (qspecl_then [`exp`,`env`,`dec_clock 1 s`] assume_tac)
              >> fs [bvi_mk_tick_def, dec_clock_def]
              >> `(s.clock < n + 1 ∧ 0 < n) ⇔ s.clock < SUC n` by
                   (qpat_x_assum `s.clock ≠ 0` mp_tac
                    >> simp [ADD1]
                    >> decide_tac)
              >> fs [ADD1])))
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
              exp_rel t.code [exp] [exp1])
End

Theorem in_state_rel_find_code[local]:
  ∀s t dest vs args exp.
    in_state_rel s t ∧
    find_code dest vs s.code = SOME (args,exp) ⇒
    ∃exp1. find_code dest vs t.code = SOME (args,exp1) ∧
      exp_rel t.code [exp] [exp1]
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
      exp_rel (union old_target (fromAList out))
        [wanted_body] [body1]
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
  >> impl_tac
  >- gvs []
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
  >~ [`Label label`] >-
   (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
         bvl_to_bvi_def, bvlSemTheory.do_app_def,
         AllCaseEqs(), state_component_equality, SUBSET_DEF]
    >> rpt strip_tac
    >> gvs []
    >> metis_tac [])
  >~ [`BlockOp block_op`] >-
   (Cases_on `block_op`
    >~ [`Build parts`] >-
     (namedCases_on `do_build_const parts s.refs`
        ["built_value built_refs"]
      >> gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
              bvl_to_bvi_def, bvlSemTheory.do_app_def,
              AllCaseEqs(), state_component_equality, SUBSET_DEF]
      >> rpt strip_tac
      >> rveq
      >> gvs [])
    >> gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
            bvl_to_bvi_def, bvlSemTheory.do_app_def,
            AllCaseEqs(), state_component_equality, SUBSET_DEF]
    >> rpt strip_tac
    >> rveq
    >> gvs [])
  >~ [`GlobOp glob_op`] >-
   (namedCases_on `glob_op`
      ["global_index", "set_index", "", "", ""]
    >- (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
             bvl_to_bvi_def, bvlSemTheory.do_app_def,
             AllCaseEqs(), state_component_equality, SUBSET_DEF]
        >> rpt strip_tac
        >> rveq
        >> gvs [])
    >- (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
             bvl_to_bvi_def, bvlSemTheory.do_app_def,
             AllCaseEqs(), state_component_equality, SUBSET_DEF]
        >> rpt strip_tac
        >> rveq
        >> gvs []
        >> qmatch_assum_rename_tac
             `FLOOKUP s.refs global_ptr = SOME (ValueArray global_values)`
        >> qmatch_assum_rename_tac
             `s.refs |+ (global_ptr,
                ValueArray (LUPDATE new_value set_index global_values)) =
              s1.refs`
        >> qexists_tac
             `SOME
                (Unit,
                 t with
                   <| refs := s.refs |+
                          (global_ptr,
                           ValueArray
                             (LUPDATE new_value set_index global_values));
                      clock := s1.clock;
                      global := s1.global;
                      ffi := s1.ffi |>)`
        >> conj_tac
        >- (qexists_tac `global_ptr`
            >> simp [])
        >> disj2_tac
        >> simp [state_component_equality]
        >> qexists_tac
             `t with <| refs := s1.refs; clock := s1.clock;
                         global := s1.global; ffi := s1.ffi |>`
        >> simp [state_component_equality])
    >- (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
             bvl_to_bvi_def, bvlSemTheory.do_app_def,
             AllCaseEqs(), state_component_equality, SUBSET_DEF]
        >> rpt strip_tac
        >> rveq
        >> gvs [])
    >- (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
             bvl_to_bvi_def, bvlSemTheory.do_app_def,
             AllCaseEqs(), state_component_equality, SUBSET_DEF]
        >> rpt strip_tac
        >> rveq
        >> gvs [])
    >- (gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
             bvl_to_bvi_def, bvlSemTheory.do_app_def,
             AllCaseEqs(), state_component_equality, SUBSET_DEF]
        >> rpt strip_tac
        >> rveq
        >> gvs []))
  >> gvs [do_app_def, do_app_aux_def, bvi_to_bvl_def,
          bvl_to_bvi_def, bvlSemTheory.do_app_def,
          AllCaseEqs(), state_component_equality, SUBSET_DEF]
  >> rpt strip_tac
  >> rveq
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

Theorem inline_all_head[local]:
  inline_all cs ((name,arity,body)::rest) = (final_cache,out) ⇒
  ∃tail. out = (name,arity,inline_exp cs body)::tail
Proof
  rw [inline_all_def]
  >> pairarg_tac
  >> fs []
  >> rveq
  >> gvs []
  >> qexists_tac `prog2`
  >> gvs []
QED

Theorem inline_all_head_names[local]:
  inline_all cs ((name,arity,body)::rest) = (final_cache,out) ⇒
  ∃tail.
    out = (name,arity,inline_exp cs body)::tail ∧
    MAP FST tail = MAP FST rest
Proof
  strip_tac
  >> drule inline_all_head
  >> strip_tac
  >> qexists_tac `tail'`
  >> conj_tac
  >- metis_tac []
  >- (qspecl_then
         [`cs`,`(name,arity,body)::rest`]
         mp_tac inline_all_MAP_FST
      >> fs []
      >> strip_tac
      >> metis_tac [])
QED

Theorem inline_all_lookup_union[local]:
  inline_all cs prog = (final_cache,out) ∧
  subspt cs target ∧
  domain target = domain source ∧
  (∀k arity exp. lookup k source = SOME (arity,exp) ⇒
     ∃exp1. lookup k target = SOME (arity,exp1) ∧
            exp_rel target [exp] [exp1]) ∧
  DISJOINT (set (MAP FST prog)) (domain target) ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  ∀k arity exp.
    lookup k (union source (fromAList prog)) = SOME (arity,exp) ⇒
    ∃exp1.
      lookup k (union target (fromAList out)) = SOME (arity,exp1) ∧
      exp_rel (union target (fromAList out)) [exp] [exp1]
Proof
  rpt strip_tac
  >> Cases_on `lookup k source`
  >- (fs [lookup_union,lookup_fromAList]
      >> qspecl_then
           [`prog`,`cs`,`target`,`final_cache`,`out`,`k`,`arity`,`exp`]
           mp_tac inline_all_ALOOKUP
      >> impl_tac
      >- metis_tac [lookup_fromAList]
      >> strip_tac
      >> `lookup k target = NONE` by
           (Cases_on `lookup k target`
            >- fs []
            >- (fs [domain_lookup,DISJOINT_DEF,EXTENSION,MEM_MAP]
                >> imp_res_tac ALOOKUP_MEM
                >> qpat_x_assum `∀x. _` (qspec_then `k` mp_tac)
                >> fs []
                >> qexists_tac `(k, (arity,exp))`
                >> fs []))
      >> qexists_tac `body1`
      >> fs [lookup_fromAList,lookup_union])
  >- (Cases_on `x`
      >> qpat_x_assum `∀k arity exp. _`
           (qspecl_then [`k`,`q`,`r`] mp_tac)
      >> impl_tac
      >- fs []
      >> strip_tac
      >> qexists_tac `exp1`
      >> fs [lookup_union]
      >> rveq
      >> irule exp_rel_mono
      >> fs [subspt_union]
      >> qexists_tac `target`
      >> conj_tac
      >- fs [subspt_union]
      >- fs [])
QED

Theorem in_do_app_lemma[local]:
  in_state_rel s1 t1 ⇒
    case do_app op a s1 of
    | Rerr err =>
        (err ≠ Rabort Rtype_error ⇒ do_app op a t1 = Rerr err)
    | Rval (v,s2) =>
        ∃t2. in_state_rel s2 t2 ∧ do_app op a t1 = Rval (v,t2)
Proof
  Cases_on `op = Install`
  >- (strip_tac
      >> rw [do_app_def]
      >> fs [do_install_def,case_eq_thms,UNCURRY]
      >> every_case_tac
      >> fs [PULL_EXISTS]
      >> fs [in_state_rel_def]
      >> fs [state_component_equality]
      >> fs [in_co_def,in_cc_def,shift_seq_def,o_DEF]
      >> rfs []
      >> Cases_on `s1.compile_oracle 0`
      >> fs []
      >> Cases_on `r`
      >> fs []
      >> Cases_on `h`
      >> fs []
      >> rveq
      >> fs []
      >> pairarg_tac
      >> fs []
      >> rveq
      >> fs [domain_union,domain_fromAList,in_cc_def]
      >> pairarg_tac
      >> fs [case_eq_thms]
      >> rveq
      >> fs []
      >> drule inline_all_head_names
      >> strip_tac
      >> qexists_tac `tail'`
      >> qexists_tac `(q'⁴',inline_exp cs r'³')`
      >> fs [domain_fromAList,fromAList_def,domain_union]
      >> fs [in_co_def,shift_seq_def,o_DEF]
      >> Cases_on `s1.compile_oracle 1`
      >> fs []
      >> pairarg_tac
      >> fs []
      >> rveq
      >> fs []
      >> pairarg_tac
      >> fs []
      >> conj_tac
      >- (rw [GSYM fromAList_def]
          >> match_mp_tac inline_all_cache_subspt
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `cs`
          >> conj_tac
          >- fs []
          >- (conj_tac
              >- fs []
              >- (conj_tac
                  >- fs [DISJOINT_SYM]
                  >- fs [])))
      >- (rw [GSYM fromAList_def]
          >> irule inline_all_lookup_union
          >> qexists_tac `cs`
          >> qexists_tac `cs'`
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `s1.code`
          >> fs [DISJOINT_SYM])
      >- (rw [GSYM fromAList_def]
          >> match_mp_tac inline_all_cache_subspt
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `cs`
          >> conj_tac
          >- fs []
          >- (conj_tac
              >- fs []
              >- (conj_tac
                  >- fs [DISJOINT_SYM]
                  >- fs [])))
      >- (rw [GSYM fromAList_def]
          >> irule inline_all_lookup_union
          >> qexists_tac `cs`
          >> qexists_tac `cs'`
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `s1.code`
          >> fs [DISJOINT_SYM])
      >- (rw [GSYM fromAList_def]
          >> match_mp_tac inline_all_cache_subspt
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `cs`
          >> conj_tac
          >- fs []
          >- (conj_tac
              >- fs []
              >- (conj_tac
                  >- fs [DISJOINT_SYM]
                  >- fs [])))
      >- (rw [GSYM fromAList_def]
          >> irule inline_all_lookup_union
          >> qexists_tac `cs`
          >> qexists_tac `cs'`
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `s1.code`
          >> fs [DISJOINT_SYM])
      >- (rw [GSYM fromAList_def]
          >> match_mp_tac inline_all_cache_subspt
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `cs`
          >> conj_tac
          >- fs []
          >- (conj_tac
              >- fs []
              >- (conj_tac
                  >- fs [DISJOINT_SYM]
                  >- fs [])))
      >- (rw [GSYM fromAList_def]
          >> irule inline_all_lookup_union
          >> qexists_tac `cs`
          >> qexists_tac `cs'`
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `s1.code`
          >> fs [DISJOINT_SYM])
      >- (rw [GSYM fromAList_def]
          >> match_mp_tac inline_all_cache_subspt
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `cs`
          >> conj_tac
          >- fs []
          >- (conj_tac
              >- fs []
              >- (conj_tac
                  >- fs [DISJOINT_SYM]
                  >- fs [])))
      >- (rw [GSYM fromAList_def]
          >> irule inline_all_lookup_union
          >> qexists_tac `cs`
          >> qexists_tac `cs'`
          >> qexists_tac `((q'',q'⁴',r'³')::t)`
          >> qexists_tac `s1.code`
          >> fs [DISJOINT_SYM]))
  >- (strip_tac
      >> namedCases_on `do_app op a s1`
           ["source_result", "source_error"]
      >- (namedCases_on `source_result`
             ["source_value source_state"]
          >> simp []
          >> qexists_tac
               `t1 with
                  <| refs := source_state.refs;
                     clock := source_state.clock;
                     global := source_state.global;
                     ffi := source_state.ffi |>`
          >> conj_tac
          >- (imp_res_tac do_app_code
              >> imp_res_tac do_app_oracle
              >> gvs [in_state_rel_def])
          >- (`do_app op a t1 =
                 do_app op a
                   (t1 with <| refs := s1.refs; clock := s1.clock;
                                global := s1.global; ffi := s1.ffi |>)` by
                (AP_TERM_TAC
                 >> gvs [in_state_rel_def, state_component_equality])
              >> qpat_assum
                   `do_app _ _ _ = do_app _ _ _`
                   (fn th => once_rewrite_tac [th])
              >> match_mp_tac do_app_state_swap_Rval
              >> gvs [in_state_rel_def]))
      >- (simp []
          >> strip_tac
          >> `do_app op a t1 =
                do_app op a
                  (t1 with <| refs := s1.refs; clock := s1.clock;
                               global := s1.global; ffi := s1.ffi |>)` by
               (AP_TERM_TAC
                >> fs [in_state_rel_def, state_component_equality])
          >> qpat_assum
               `do_app _ _ _ = do_app _ _ _`
               (fn th => once_rewrite_tac [th])
          >> match_mp_tac do_app_state_swap_Rerr
          >> gvs [in_state_rel_def]))
QED

Theorem exp_rel_length[local]:
  ∀c xs ys. exp_rel c xs ys ⇒ LENGTH xs = LENGTH ys
Proof
  ho_match_mp_tac exp_rel_ind
  >> rw []
  >> fs []
  >> res_tac
QED

Theorem exp_rel_singleton_var[local]:
  ∀c xs ys. exp_rel c xs ys ⇒
    LENGTH xs = LENGTH ys ∧
    (∀n. xs = [Var n] ⇒ ys = [Var n])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rw []
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_raise[local]:
  ∀c xs ys. exp_rel c xs ys ⇒
    LENGTH xs = LENGTH ys ∧
    (∀x. xs = [Raise x] ⇒ ∃z. ys = [Raise z])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
QED

Theorem exp_rel_raise_inv[local]:
  ∀c xs ys. exp_rel c xs ys ⇒
    exp_rel c xs ys ∧
    (∀x y. xs = [Raise x] ∧ ys = [Raise y] ⇒ exp_rel c [x] [y])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> rveq
  >> fs []
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_if[local]:
  ∀c xs ys. exp_rel c xs ys ⇒
    LENGTH xs = LENGTH ys ∧
    (∀x1 x2 x3. xs = [If x1 x2 x3] ⇒
       ∃y1 y2 y3. ys = [If y1 y2 y3])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
QED

Theorem exp_rel_if_inv[local]:
  ∀c xs ys. exp_rel c xs ys ⇒
    exp_rel c xs ys ∧
    (∀x1 x2 x3 y1 y2 y3.
       xs = [If x1 x2 x3] ∧ ys = [If y1 y2 y3] ⇒
       exp_rel c [x1] [y1] ∧ exp_rel c [x2] [y2] ∧
       exp_rel c [x3] [y3])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> rveq
  >> fs []
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_let[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀xs x. es = [Let xs x] ⇒
      ∃ys2 y2. out = [Let ys2 y2] ∧
        exp_rel c xs ys2 ∧ exp_rel c [x] [y2])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_return[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀xs. es = [Return xs] ⇒
      ∃ys. out = [Return ys] ∧ exp_rel c xs ys)
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_op[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀op xs. es = [Op op xs] ⇒
      ∃ys. out = [Op op ys] ∧ exp_rel c xs ys)
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_tick[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀x. es = [Tick x] ⇒
      ∃y. out = [Tick y] ∧ exp_rel c [x] [y])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_force[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀loc n. es = [Force loc n] ⇒
      out = [Force loc n])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_letcall[local]:
  ∀c es out. exp_rel c es out ⇒
    LENGTH es = LENGTH out ∧
    (∀rets ticks dest xs y.
      es = [LetCall rets ticks dest xs y] ⇒
      ∃ys y1.
        out = [LetCall rets ticks dest ys y1])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
QED

Theorem exp_rel_letcall_inv[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧
    (∀rets ticks dest xs y ys y1.
      es = [LetCall rets ticks dest xs y] ∧
      out = [LetCall rets ticks dest ys y1] ⇒
      exp_rel c xs ys ∧ exp_rel c [y] [y1])
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> rveq
  >> fs []
  >> metis_tac [exp_rel_rules]
QED

Theorem exp_rel_singleton_call[local]:
  ∀c es out. exp_rel c es out ⇒
    exp_rel c es out ∧ LENGTH es = LENGTH out ∧
    (∀ticks dest xs handler.
      es = [Call ticks dest xs handler] ⇒
      (∃ys.
         handler = NONE ∧
         out = [Call ticks dest ys NONE] ∧
         exp_rel c xs ys) ∨
      (∃ys h h1.
         handler = SOME h ∧
         out = [Call ticks dest ys (SOME h1)] ∧
         exp_rel c xs ys ∧ exp_rel c [h] [h1]) ∨
      (∃n ys arity body.
         dest = SOME n ∧ handler = NONE ∧
         out = [Let ys (bvi_mk_tick (SUC ticks) body)] ∧
         exp_rel c xs ys ∧ lookup n c = SOME (arity,body) ∧
         LENGTH ys = arity))
Proof
  ho_match_mp_tac exp_rel_ind
  >> rpt strip_tac
  >> fs []
  >> res_tac
  >> metis_tac [exp_rel_rules]
QED

Theorem evaluate_inline:
  ∀es env s res s1 t es1.
    in_state_rel s t ∧ exp_rel t.code es es1 ∧
    evaluate (es,env,s) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t1. evaluate (es1,env,t) = (res,t1) ∧ in_state_rel s1 t1
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >- (fs [evaluate_def]
      >> qpat_x_assum `exp_rel _ [] _` mp_tac
      >> once_rewrite_tac [exp_rel_cases]
      >> strip_tac
      >> fs []
      >> qexists_tac `t`
      >> fs [evaluate_def,in_state_rel_def])
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
  qpat_x_assum `exp_rel _ (x::y::xs) _` mp_tac
  >> once_rewrite_tac [exp_rel_cases]
  >> strip_tac
  >> fs []
  >> qpat_x_assum `evaluate (_::_,_,_) = _` mp_tac
  >> once_rewrite_tac [evaluate_CONS]
  >> strip_tac
  >> namedCases_on `evaluate ([x],env,s)` ["head_result head_state"]
  >> namedCases_on `head_result` ["head_value", "head_error"]
  >> fs [case_eq_thms]
  >> rveq
  >> fs []
  >- (first_x_assum drule
      >> strip_tac
      >> first_x_assum drule
      >> strip_tac
      >> qpat_x_assum
           `∀t' es1'.
              in_state_rel s2 t' ∧ exp_rel t'.code (y::xs) es1' ⇒ _`
           (qspecl_then [`t1`,`ys`] mp_tac)
      >> impl_tac
      >- (conj_tac
          >- fs []
          >- (imp_res_tac evaluate_code_mono
              >> drule exp_rel_mono
              >> fs []))
      >> strip_tac
      >> qexists_tac `t1'`
      >> conj_tac
      >- (qexists_tac `Rval v`
          >> qexists_tac `t1`
          >> conj_tac
          >- fs []
          >- (qexists_tac `v` >> fs []))
      >- fs [])
  >- (qpat_x_assum
           `∀t' es1'.
              in_state_rel s t' ∧ exp_rel t'.code [x] es1' ⇒ _`
           drule
      >> strip_tac
      >> first_x_assum drule
      >> strip_tac
      >> qpat_x_assum
           `∀t' es1'.
              in_state_rel s2 t' ∧ exp_rel t'.code (y::xs) es1' ⇒ _`
           (qspecl_then [`t1`,`ys`] mp_tac)
      >> impl_tac
      >- (conj_tac
          >- fs []
          >- (imp_res_tac evaluate_code_mono
              >> drule exp_rel_mono
              >> fs []))
      >> strip_tac
      >> qexists_tac `t1'`
      >> conj_tac
      >- (qexists_tac `FST ((Rval v : bvi_result),t1)`
          >> fs [])
      >- fs [])
  >- (qpat_x_assum
           `∀t' es1'.
              in_state_rel s t' ∧ exp_rel t'.code [x] es1' ⇒ _`
           (qspecl_then [`t`,`[y']`] mp_tac)
      >> impl_tac
      >- (conj_tac >> fs [])
      >> strip_tac
      >> qexists_tac `t1`
      >> conj_tac
      >- (qexists_tac `Rerr v10`
          >> qexists_tac `t1`
          >> fs [])
      >- fs [])
QED

Resume evaluate_inline[Var]:
  qpat_x_assum `exp_rel _ [Var n] _` mp_tac
  >> once_rewrite_tac [exp_rel_cases]
  >> strip_tac
  >> fs []
  >- (rveq
      >> qexists_tac `t`
      >> simp [evaluate_def]
      >> IF_CASES_TAC
      >- (fs [evaluate_def]
          >> rveq
          >> fs [in_state_rel_def])
      >- (fs [evaluate_def]
          >> rveq
          >> fs [in_state_rel_def]))
  >- (fs []
      >> rveq
      >> drule_at Any exp_rel_length
      >> fs []
      >> qmatch_assum_rename_tac `exp_rel t.code [Var n] [y1]`
      >> qspecl_then [`t.code`,`[Var n]`,`[y1]`] mp_tac
           exp_rel_singleton_var
      >> strip_tac
      >> first_x_assum drule
      >> fs []
      >> strip_tac
      >> fs []
      >> strip_tac
      >> fs []
      >> rveq
      >> qexists_tac `t`
      >> simp [evaluate_def]
      >> IF_CASES_TAC
      >- (fs [evaluate_def]
          >> rveq
          >> fs [in_state_rel_def])
      >- (fs [evaluate_def]
          >> rveq
          >> fs [in_state_rel_def]))
QED

Resume evaluate_inline[If]:
  qpat_x_assum `exp_rel _ [If x1 x2 x3] _` mp_tac
  >> once_rewrite_tac [exp_rel_cases]
  >> strip_tac
  >> fs []
  >> rveq
  >> qpat_x_assum `evaluate ([If x1 x2 x3],_,_) = _` mp_tac
  >> fs [evaluate_def,case_eq_thms]
  >> rveq
  >> fs []
  >- (rpt strip_tac
      >> drule_at Any exp_rel_length
      >> fs []
      >> strip_tac
      >> qspecl_then [`t.code`,`[If x1 x2 x3]`,`[y]`] mp_tac
           exp_rel_singleton_if
      >> disch_then drule
      >> fs []
      >> strip_tac
      >> fs []
      >> qspecl_then [`t.code`,`[If x1 x2 x3]`,`[If y1 y2 y3]`] mp_tac
           exp_rel_if_inv
      >> disch_then drule
      >> fs []
      >> strip_tac
      >> fs []
      >- (first_x_assum drule
          >> disch_then drule
          >> strip_tac
          >> fs [evaluate_def]
          >> first_x_assum drule
          >> strip_tac
          >> imp_res_tac evaluate_code_mono
          >> qpat_x_assum `exp_rel _ [x2] [y2]` mp_tac
          >> strip_tac
          >> drule exp_rel_mono
          >> strip_tac
          >> qpat_x_assum
               `∀es1. exp_rel t1.code [x2] es1 ⇒
                  ∃t1'. evaluate (es1,env,t1) = (res,t1') ∧
                         in_state_rel s1 t1'` mp_tac
          >> strip_tac
          >> first_x_assum drule
          >> fs [evaluate_def])
      >- (first_x_assum drule
          >> disch_then drule
          >> strip_tac
          >> fs [evaluate_def]
          >> qpat_x_assum `exp_rel _ [x3] [y3]` mp_tac
          >> strip_tac
          >> imp_res_tac evaluate_code_mono
          >> drule exp_rel_mono
          >> disch_then drule
          >> first_x_assum drule
          >> fs [evaluate_def])
      >- (first_x_assum drule
          >> disch_then drule
          >> strip_tac
          >> fs [evaluate_def]
          >> qexists_tac `t1`
          >> fs []
          >> rveq
          >> fs []))
  >- (rpt strip_tac
      >> fs [case_eq_thms]
      >> rveq
      >> rpt (qpat_x_assum `_ = bviSem$evaluate _` (assume_tac o GSYM))
      >> fs []
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> fs [evaluate_def]
      >> first_x_assum drule
      >> imp_res_tac evaluate_code_mono
      >> imp_res_tac exp_rel_mono
      >> metis_tac [])
QED

Resume evaluate_inline[Let]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qpat_x_assum `exp_rel _ [Let xs x2] _` mp_tac
  >> once_rewrite_tac [exp_rel_cases]
  >> strip_tac
  >> fs []
  >- (rveq
      >> drule_at Any exp_rel_length
      >> fs []
      >> qspecl_then [`t.code`,`[Let xs x2]`,`[y]`] mp_tac
           exp_rel_singleton_let
      >> disch_then drule
      >> strip_tac
      >> fs []
      >> strip_tac
      >> fs [evaluate_def,case_eq_thms]
      >> rveq
      >> fs []
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> fs [evaluate_def]
      >> first_x_assum drule
      >> imp_res_tac evaluate_code_mono
      >> drule exp_rel_mono
      >> disch_then drule
      >> rw []
      >> pop_assum drule
      >> rw []
      >> fs [])
  >- (fs [evaluate_def,case_eq_thms]
      >> rveq
      >> fs []
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> fs [evaluate_def]
      >> first_x_assum drule
      >> imp_res_tac evaluate_code_mono
      >> drule exp_rel_mono
      >> disch_then drule
      >> rw []
      >> pop_assum drule
      >> rw []
      >> fs [])
QED

Resume evaluate_inline[Raise]:
  qpat_x_assum `exp_rel _ [Raise _] _` mp_tac
  >> once_rewrite_tac [exp_rel_cases]
  >> strip_tac
  >> fs []
  >> rveq
  >> qpat_x_assum `evaluate ([Raise _],_,_) = _` mp_tac
  >> fs [evaluate_def,case_eq_thms]
  >> rveq
  >> fs []
  >- (rpt strip_tac
      >> drule_at Any exp_rel_length
      >> fs []
      >> strip_tac
      >> qspecl_then [`t.code`,`[Raise x1]`,`[y]`] mp_tac
           exp_rel_singleton_raise
      >> disch_then drule
      >> fs []
      >> strip_tac
      >> fs []
      >> rveq
      >> qspecl_then [`t.code`,`[Raise x1]`,`[Raise z]`] mp_tac
           exp_rel_raise_inv
      >> disch_then drule
      >> fs []
      >> strip_tac
      >> qpat_x_assum `∀t' es1. _` drule
      >> fs [evaluate_def]
      >> strip_tac
      >> first_x_assum drule
      >> fs [evaluate_def]
      >> strip_tac
      >> fs [])
  >- (rpt strip_tac
      >> fs []
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> fs [evaluate_def]
      >> qexists_tac `t1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `v7`
      >> fs [])
QED

Resume evaluate_inline[Return]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qspecl_then [`t.code`,`[Return xs]`,`es1`] mp_tac
       exp_rel_singleton_return
  >> disch_then drule
  >> strip_tac
  >> fs []
  >> fs [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["return_value return_state", "return_error return_state"]
  >> fs [case_eq_thms]
  >> rveq
  >> first_x_assum drule
  >> disch_then drule
  >> rw []
  >> qexists_tac `t1`
  >> fs []
QED

Resume evaluate_inline[Op]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qspecl_then [`t.code`,`[Op op xs]`,`es1`] mp_tac
       exp_rel_singleton_op
  >> disch_then drule
  >> strip_tac
  >> fs []
  >> fs [evaluate_def,case_eq_thms]
  >> rveq
  >> fs []
  >> first_x_assum drule
  >> disch_then drule
  >> strip_tac
  >> fs [evaluate_def]
  >> drule (Q.GEN `a` in_do_app_lemma)
  >> disch_then (qspecl_then [`op`,`REVERSE vs`] mp_tac)
  >> fs []
  >> strip_tac
  >> fs []
QED

Resume evaluate_inline[Tick]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qspecl_then [`t.code`,`[Tick x]`,`es1`] mp_tac
       exp_rel_singleton_tick
  >> disch_then drule
  >> strip_tac
  >> fs []
  >> `s.clock = t.clock` by fs [in_state_rel_def]
  >> fs [evaluate_def,case_eq_thms]
  >> rveq
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by fs [in_state_rel_def,dec_clock_def]
  >- (fs [])
  >- (qpat_x_assum `t.clock ≠ 0 ⇒ ∀res s1 t es1. _` mp_tac
      >> strip_tac
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> fs [evaluate_def])
QED


Resume evaluate_inline[Force]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qspecl_then [`t.code`,`[Force force_loc n]`,`es1`] mp_tac
       exp_rel_singleton_force
  >> disch_then drule
  >> strip_tac
  >> fs []
  >> gvs [AllCaseEqs(), evaluate_def, PULL_EXISTS, oneline dest_thunk_def]
  >- gvs [in_state_rel_def]
  >- (gvs [in_state_rel_def, bvlSemTheory.find_code_def, AllCaseEqs()]
      >> first_x_assum drule
      >> rw []
      >> gvs [])
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> last_x_assum drule
  >> rw []
  >> gvs [bvlSemTheory.find_code_def, AllCaseEqs(), in_state_rel_def,
          PULL_EXISTS]
  >> last_x_assum drule
  >> rw []
  >- (qsuff_tac `∃t1.
        evaluate ([exp1],[RefPtr F ptr; v],dec_clock 1 t) = (Rval v6,t1) ∧
        t1.refs = s1.refs ∧ t1.clock = s1.clock ∧ t1.global = s1.global ∧
        t1.ffi = s1.ffi ∧ t1.compile_oracle = in_co s1.compile_oracle ∧
        subspt (FST (FST (s1.compile_oracle 0))) t1.code ∧
        s1.compile = in_cc t1.compile ∧ domain t1.code = domain s1.code ∧
        ∀k arity exp.
          lookup k s1.code = SOME (arity,exp) ⇒
          ∃exp1. lookup k t1.code = SOME (arity,exp1) ∧
            exp_rel t1.code [exp] [exp1]`
      >- (last_x_assum drule
          >> rw []
          >> gvs [])
      >> (last_x_assum drule
          >> rw []
          >> gvs []))
  >- (qsuff_tac `∃t1.
        evaluate ([exp1],[RefPtr F ptr; v],dec_clock 1 t) =
          (Rerr (Rraise (Exn v14)),t1) ∧
        t1.refs = s1.refs ∧ t1.clock = s1.clock ∧ t1.global = s1.global ∧
        t1.ffi = s1.ffi ∧ t1.compile_oracle = in_co s1.compile_oracle ∧
        subspt (FST (FST (s1.compile_oracle 0))) t1.code ∧
        s1.compile = in_cc t1.compile ∧ domain t1.code = domain s1.code ∧
        ∀k arity exp.
          lookup k s1.code = SOME (arity,exp) ⇒
          ∃exp1. lookup k t1.code = SOME (arity,exp1) ∧
            exp_rel t1.code [exp] [exp1]`
      >- (last_x_assum drule
          >> rw []
          >> gvs [])
      >> (last_x_assum drule
          >> rw []
          >> gvs []))
  >- (qsuff_tac `∃t1.
        evaluate ([exp1],[RefPtr F ptr; v],dec_clock 1 t) =
          (Rerr (Rabort v11),t1) ∧
        t1.refs = s1.refs ∧ t1.clock = s1.clock ∧ t1.global = s1.global ∧
        t1.ffi = s1.ffi ∧ t1.compile_oracle = in_co s1.compile_oracle ∧
        subspt (FST (FST (s1.compile_oracle 0))) t1.code ∧
        s1.compile = in_cc t1.compile ∧ domain t1.code = domain s1.code ∧
        ∀k arity exp.
          lookup k s1.code = SOME (arity,exp) ⇒
          ∃exp1. lookup k t1.code = SOME (arity,exp1) ∧
            exp_rel t1.code [exp] [exp1]`
      >- (last_x_assum drule
          >> rw []
          >> gvs [])
      >> (last_x_assum drule
          >> rw []
          >> gvs []))
QED

Resume evaluate_inline[Call]:
  fs [case_eq_thms]
  >> rveq
  >> fs []
  >> qpat_x_assum `exp_rel _ [Call ticks dest xs handler] _`
       (mp_tac o MATCH_MP exp_rel_singleton_call)
  >> strip_tac
  >> fs []
  >- (rveq
      >> namedCases_on `evaluate (xs,env,s1)` ["args_result args_state"]
      >> namedCases_on `args_result` ["args_values", "args_error"]
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> namedCases_on `find_code dest args_values args_state.code`
               ["", "code_entry"]
          >- fs []
          >> PairCases_on `code_entry`
          >> qmatch_assum_rename_tac
               `find_code dest args_values args_state.code =
                  SOME (body_args,body_exp)`
          >> fs []
          >> qspecl_then
               [`args_state`,`t1`,`dest`,`args_values`,`body_args`,`body_exp`]
               mp_tac in_state_rel_find_code
          >> fs []
          >> strip_tac
          >> qmatch_assum_rename_tac
               `find_code dest args_values t1.code =
                  SOME (body_args,target_body)`
          >> Cases_on `args_state.clock < ticks + 1`
          >- gvs [in_state_rel_def]
          >> `in_state_rel (dec_clock (ticks + 1) args_state)
                (dec_clock (ticks + 1) t1)`
               by fs [in_state_rel_def,dec_clock_def]
          >> namedCases_on
               `evaluate ([body_exp],body_args,
                  dec_clock (ticks + 1) args_state)`
               ["body_result body_state"]
          >> namedCases_on `body_result` ["body_values", "body_error"]
          >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
              >> fs []
              >> strip_tac
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then
                      [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
              >> fs []
              >> strip_tac
              >> gvs [in_state_rel_def])
          >> namedCases_on `body_error` ["raised", "abort_kind"]
          >- (namedCases_on `raised` ["exception_value", "return_values"]
              >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
                  >> fs []
                  >> strip_tac
                  >> qpat_x_assum `∀t' es1'. _`
                       (qspecl_then
                          [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
                  >> fs []
                  >> strip_tac
                  >> gvs [in_state_rel_def])
              >- fs [])
          >> qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
          >> fs []
          >> strip_tac
          >> qpat_x_assum `∀t' es1'. _`
               (qspecl_then
                  [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def])
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def]))
  >- (rveq
      >> `dest ≠ NONE` by (Cases_on `dest` >> fs [evaluate_def])
      >> namedCases_on `evaluate (xs,env,s1)` ["args_result args_state"]
      >> namedCases_on `args_result` ["args_values", "args_error"]
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> imp_res_tac evaluate_code_mono
          >> qpat_x_assum `exp_rel t.code [h] [h1]`
               (qspec_then `t1.code` mp_tac o MATCH_MP exp_rel_mono)
          >> fs []
          >> strip_tac
          >> namedCases_on `find_code dest args_values args_state.code`
               ["", "code_entry"]
          >- fs []
          >> PairCases_on `code_entry`
          >> qmatch_assum_rename_tac
               `find_code dest args_values args_state.code =
                  SOME (body_args,body_exp)`
          >> fs []
          >> qspecl_then
               [`args_state`,`t1`,`dest`,`args_values`,`body_args`,`body_exp`]
               mp_tac in_state_rel_find_code
          >> fs []
          >> strip_tac
          >> qmatch_assum_rename_tac
               `find_code dest args_values t1.code =
                  SOME (body_args,target_body)`
          >> Cases_on `args_state.clock < ticks + 1`
          >- gvs [in_state_rel_def]
          >> `in_state_rel (dec_clock (ticks + 1) args_state)
                (dec_clock (ticks + 1) t1)`
               by fs [in_state_rel_def,dec_clock_def]
          >> namedCases_on
               `evaluate ([body_exp],body_args,
                  dec_clock (ticks + 1) args_state)`
               ["body_result body_state"]
          >> namedCases_on `body_result` ["body_values", "body_error"]
          >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
              >> fs []
              >> strip_tac
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then
                      [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
              >> fs []
              >> strip_tac
              >> gvs [in_state_rel_def])
          >> namedCases_on `body_error` ["raised", "abort_kind"]
          >- (namedCases_on `raised` ["exception_value", "return_values"]
              >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
                  >> fs []
                  >> strip_tac
                  >> qpat_x_assum `∀t' es1'. _`
                       (qspecl_then
                          [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
                  >> fs []
                  >> strip_tac
                  >> qmatch_assum_rename_tac
                       `evaluate
                          ([target_body],body_args,
                           dec_clock (ticks + 1) t1) =
                        (Rerr (Rraise (Exn exception_value)),target_body_state)`
                  >> imp_res_tac evaluate_code_mono
                  >> qpat_x_assum `exp_rel t1.code [h] [h1]`
                       (qspec_then `target_body_state.code` mp_tac o
                        MATCH_MP exp_rel_mono)
                  >> fs []
                  >> strip_tac
                  >> namedCases_on
                       `evaluate ([h],exception_value::env,body_state)`
                       ["handler_result handler_state"]
                  >> namedCases_on `handler_result`
                       ["handler_values", "handler_error"]
                  >- (qpat_x_assum `∀res s1 t es1. _` mp_tac
                      >> fs []
                      >> strip_tac
                      >> qpat_x_assum `∀t' es1. _`
                           (qspecl_then
                              [`target_body_state`,`[h1]`] mp_tac)
                      >> fs []
                      >> strip_tac
                      >> gvs [in_state_rel_def])
                  >> namedCases_on `handler_error`
                       ["handler_raised", "handler_abort"]
                  >- (namedCases_on `handler_raised`
                        ["handler_exception", "handler_returns"]
                      >- (qpat_x_assum `∀res s1 t es1. _` mp_tac
                          >> fs []
                          >> strip_tac
                          >> qpat_x_assum `∀t' es1. _`
                               (qspecl_then
                                  [`target_body_state`,`[h1]`] mp_tac)
                          >> fs []
                          >> strip_tac
                          >> gvs [in_state_rel_def])
                      >- fs [])
                  >> qpat_x_assum `∀res s1 t es1. _` mp_tac
                  >> fs []
                  >> strip_tac
                  >> qpat_x_assum `∀t' es1. _`
                       (qspecl_then [`target_body_state`,`[h1]`] mp_tac)
                  >> fs []
                  >> strip_tac
                  >> gvs [in_state_rel_def])
              >- fs [])
          >> qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
          >> fs []
          >> strip_tac
          >> qpat_x_assum `∀t' es1'. _`
               (qspecl_then
                  [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def])
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def]))
  >- (rveq
      >> namedCases_on `evaluate (xs,env,s1)` ["args_result args_state"]
      >> namedCases_on `args_result` ["args_values", "args_error"]
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def,evaluate_bvi_mk_tick]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> imp_res_tac evaluate_code_mono
          >> imp_res_tac evaluate_LENGTH
          >> namedCases_on
               `find_code (SOME n) args_values args_state.code`
               ["", "code_entry"]
          >- fs []
          >> PairCases_on `code_entry`
          >> qmatch_assum_rename_tac
               `find_code (SOME n) args_values args_state.code =
                  SOME (body_args,body_exp)`
          >> qspecl_then
               [`args_state`,`t1`,`SOME n`,`args_values`,`body_args`,`body_exp`]
               mp_tac in_state_rel_find_code
          >> fs []
          >> strip_tac
          >> qmatch_assum_rename_tac
               `find_code (SOME n) args_values t1.code =
                  SOME (body_args,target_body)`
          >> `lookup n t1.code = SOME (LENGTH ys,body)` by
               fs [subspt_lookup]
          >> `find_code (SOME n) args_values t1.code =
                SOME (args_values,body)` by
               fs [bvlSemTheory.find_code_def]
          >> fs []
          >> Cases_on `args_state.clock < ticks + 1`
          >- gvs [in_state_rel_def]
          >> `in_state_rel (dec_clock (ticks + 1) args_state)
                (dec_clock (ticks + 1) t1)` by
               fs [in_state_rel_def,dec_clock_def]
          >> namedCases_on
               `evaluate ([body_exp],body_args,
                  dec_clock (ticks + 1) args_state)`
               ["body_result body_state"]
          >> namedCases_on `body_result` ["body_values", "body_error"]
          >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
              >> fs []
              >> strip_tac
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then
                      [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
              >> fs []
              >> strip_tac
              >> qspecl_then
                   [`[target_body]`,`body_args`,
                    `dec_clock (ticks + 1) t1`,`env`]
                   mp_tac evaluate_expand_env
              >> fs []
              >> strip_tac
              >> gvs [in_state_rel_def,ADD1])
          >> namedCases_on `body_error` ["raised", "abort_kind"]
          >- (namedCases_on `raised` ["exception_value", "return_values"]
              >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
                  >> fs []
                  >> strip_tac
                  >> qpat_x_assum `∀t' es1'. _`
                       (qspecl_then
                          [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
                  >> fs []
                  >> strip_tac
                  >> qspecl_then
                       [`[target_body]`,`body_args`,
                        `dec_clock (ticks + 1) t1`,`env`]
                       mp_tac evaluate_expand_env
                  >> fs []
                  >> strip_tac
                  >> gvs [in_state_rel_def,ADD1])
              >- fs [])
          >> qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
          >> fs []
          >> strip_tac
          >> qpat_x_assum `∀t' es1'. _`
               (qspecl_then
                  [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
          >> fs []
          >> strip_tac
          >> qspecl_then
               [`[target_body]`,`body_args`,`dec_clock (ticks + 1) t1`,`env`]
               mp_tac evaluate_expand_env
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def,ADD1])
      >- (imp_res_tac evaluate_code_mono
          >> fs [evaluate_def,fix_clock_def,evaluate_bvi_mk_tick]
          >> qpat_x_assum
               `∀t' es1'.
                  in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
               (qspecl_then [`t`,`ys`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def]))
QED


Resume evaluate_inline[LetCall]:
  qpat_assum `exp_rel _ [LetCall rets ticks dest xs y] _`
    (mp_tac o MATCH_MP exp_rel_singleton_letcall)
  >> strip_tac
  >> fs []
  >> qpat_x_assum `exp_rel _ [LetCall rets ticks dest xs y] _`
    (mp_tac o MATCH_MP exp_rel_letcall_inv)
  >> strip_tac
  >> fs []
  >> qpat_x_assum `∀ys' y1'. _`
       (qspecl_then [`ys`,`y1`] mp_tac)
  >> fs []
  >> strip_tac
  >> rveq
  >> namedCases_on `evaluate (xs,env,s1)` ["args_result args_state"]
  >> namedCases_on `args_result` ["args_values", "args_error"]
  >- (imp_res_tac evaluate_code_mono
      >> fs [evaluate_def,fix_clock_def]
      >> qpat_x_assum
           `∀t' es1'.
              in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
           (qspecl_then [`t`,`ys`] mp_tac)
      >> fs []
      >> strip_tac
      >> namedCases_on `find_code (SOME dest) args_values args_state.code`
           ["", "code_entry"]
      >- fs []
      >> PairCases_on `code_entry`
      >> qmatch_assum_rename_tac
           `find_code (SOME dest) args_values args_state.code =
              SOME (body_args,body_exp)`
      >> fs []
      >> qspecl_then
           [`args_state`,`t1`,`SOME dest`,`args_values`,`body_args`,`body_exp`]
           mp_tac in_state_rel_find_code
      >> fs []
      >> strip_tac
      >> qmatch_assum_rename_tac
           `find_code (SOME dest) args_values t1.code =
              SOME (body_args,target_body)`
      >> Cases_on `args_state.clock < ticks + 1`
      >- gvs [in_state_rel_def]
      >> `in_state_rel (dec_clock (ticks + 1) args_state)
            (dec_clock (ticks + 1) t1)` by
           fs [in_state_rel_def,dec_clock_def]
      >> namedCases_on
           `evaluate ([body_exp],body_args,
              dec_clock (ticks + 1) args_state)`
           ["body_result body_state"]
      >> namedCases_on `body_result` ["body_values", "body_error"]
      >- fs []
      >> namedCases_on `body_error` ["raised", "abort_kind"]
      >- (namedCases_on `raised` ["exception_value", "return_values"]
          >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
              >> fs []
              >> strip_tac
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then
                      [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
              >> fs []
              >> strip_tac
              >> gvs [in_state_rel_def])
          >> Cases_on `LENGTH return_values = rets`
          >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
              >> fs []
              >> strip_tac
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then
                      [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
              >> fs []
              >> strip_tac
              >> qmatch_assum_rename_tac
                   `evaluate
                      ([target_body],body_args,
                       dec_clock (ticks + 1) t1) =
                    (Rerr (Rraise (Ret return_values)),target_body_state)`
              >> imp_res_tac evaluate_code_mono
              >> qpat_x_assum
                   `evaluate (ys,env,t) = (Rval args_values,t1)` mp_tac
              >> drule evaluate_code_mono
              >> strip_tac
              >> qpat_x_assum `exp_rel t.code [y] [y1]`
                   (qspec_then `target_body_state.code` mp_tac o
                    MATCH_MP exp_rel_mono)
              >> impl_tac
              >- (irule subspt_trans
                  >> qexists_tac `t1.code`
                  >> fs [])
              >> fs []
              >> qpat_x_assum `∀t' es1'. _`
                   (qspecl_then [`target_body_state`,`[y1]`] mp_tac)
              >> fs []
              >> strip_tac
              >> gvs [in_state_rel_def,ADD1])
          >- fs [])
      >- (qpat_x_assum `¬_ ⇒ ∀res' s1'' t' es1'. _` mp_tac
          >> fs []
          >> strip_tac
          >> qpat_x_assum `∀t' es1'. _`
               (qspecl_then
                  [`dec_clock (ticks + 1) t1`,`[target_body]`] mp_tac)
          >> fs []
          >> strip_tac
          >> gvs [in_state_rel_def]))
  >- (imp_res_tac evaluate_code_mono
      >> fs [evaluate_def,fix_clock_def]
      >> qpat_x_assum
           `∀t' es1'.
              in_state_rel s1 t' ∧ exp_rel t'.code xs es1' ⇒ _`
           (qspecl_then [`t`,`ys`] mp_tac)
      >> fs []
      >> strip_tac
      >> gvs [in_state_rel_def])
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
    t = s with <| code := map (I ## remove_ticks_exp) s.code;
                  compile := t.compile;
                  compile_oracle := remove_ticks_co ∘ s.compile_oracle |> ∧
    s.compile = remove_ticks_cc t.compile
End

Theorem remove_ticks_exps_NIL[simp]:
  remove_ticks_exps [] = []
Proof
  EVAL_TAC
QED

Theorem remove_state_rel_find_code_eq[local]:
  ∀dest vs s (t:('c,'ffi) bviSem$state).
    remove_state_rel s t ⇒
    find_code dest vs t.code =
      OPTION_MAP (I ## remove_ticks_exp) (find_code dest vs s.code)
Proof
  rpt strip_tac
  >> fs [remove_state_rel_def, state_component_equality]
  >> Cases_on `dest`
  >> fs [bvlSemTheory.find_code_def, lookup_map]
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

Theorem add_clock_rotate[local]:
  ∀a b c:num. a + b + c = b + (a + c)
Proof
  rpt strip_tac
  >> metis_tac [ADD_ASSOC, ADD_COMM]
QED

Theorem remove_state_rel_do_install_Rval[local]:
  ∀args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value t1.
    remove_state_rel s t ∧
    do_install args t = Rval (value,t1) ⇒
    ∃s1. do_install args s = Rval (value,s1) ∧
      remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> fs [remove_state_rel_def, state_component_equality]
  >> fs [do_install_def, case_eq_thms, UNCURRY]
  >> fs [remove_ticks_co_def, remove_ticks_cc_def, clean_prog_def]
  >> Cases_on `s.compile_oracle 0`
  >> fs []
  >> qpat_x_assum `t.compile_oracle = _` (fn h => fs [h])
  >> Cases_on `r`
  >- (fs [clean_prog_def])
  >- (fs [clean_prog_def]
      >> Cases_on `h`
      >> fs [clean_prog_def]
      >> rveq
      >> gvs [state_component_equality, shift_seq_def, o_DEF]
      >> rveq
      >> fs []
      >> Cases_on `r`
      >> fs []
      >> fs [map_union, map_fromAList]
      >> fs [PAIR_MAP]
      >> sg
           `MAP (λ(name,arity,body). (name,arity,remove_ticks_exp body)) t' =
            MAP (λ(k',v). (k',FST v,remove_ticks_exp (SND v))) t'`
      >- (match_mp_tac MAP_CONG
          >> conj_tac
          >- fs []
          >- (rpt strip_tac
              >> Cases_on `x`
              >> fs []
              >> Cases_on `r`
              >> fs []))
      >> fs [])
QED

Theorem clean_prog_map_fromAList[local]:
  ∀t'.
    MAP (λ(name,arity,body). (name,arity,remove_ticks_exp body)) t' =
    MAP (λ(k',v). (k',FST v,remove_ticks_exp (SND v))) t'
Proof
  rpt strip_tac
  >> match_mp_tac MAP_CONG
  >> conj_tac
  >- fs []
  >- (rpt strip_tac
      >> Cases_on `x`
      >> fs []
      >> Cases_on `r`
      >> fs [])
QED

Theorem remove_state_rel_do_install_Rval_fwd[local]:
  ∀args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value s1.
    remove_state_rel s t ∧
    do_install args s = Rval (value,s1) ⇒
    ∃t1. do_install args t = Rval (value,t1) ∧
      remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> fs [remove_state_rel_def, state_component_equality]
  >> fs [do_install_def, case_eq_thms, UNCURRY]
  >> fs [remove_ticks_co_def, remove_ticks_cc_def, clean_prog_def]
  >> Cases_on `s.compile_oracle 0`
  >> fs []
  >> qpat_x_assum `t.compile_oracle = _` (fn h => fs [h])
  >> Cases_on `r`
  >- (fs [clean_prog_def])
  >> fs [clean_prog_def]
  >> Cases_on `h`
  >> fs [clean_prog_def]
  >> rveq
  >> gvs [state_component_equality, shift_seq_def, o_DEF]
  >> rveq
  >> fs []
  >> fs [map_union, map_fromAList]
  >> fs [PAIR_MAP]
  >> qexists_tac
       `t with <|compile_oracle := shift_seq 1 ((I ## clean_prog) ∘ s.compile_oracle);
                    code := union (map (I ## remove_ticks_exp) s.code)
                      (fromAList
                        ((λ(arity,body). (k,arity,remove_ticks_exp body)) prog ::
                         MAP (λ(name,arity,body).
                           (name,arity,remove_ticks_exp body)) t'))|>`
  >> gvs [state_component_equality, shift_seq_def, o_DEF]
  >> fs []
  >> conj_tac
  >- (conj_tac
      >- (conj_tac
          >- (Cases_on `prog` >> fs [])
          >- (Cases_on `prog` >> fs []))
      >- (qexists_tac `(FST prog,remove_ticks_exp (SND prog))`
          >> Cases_on `prog`
          >> fs [PAIR_MAP]))
  >- (conj_tac
      >- (rw [FUN_EQ_THM]
          >> rpt strip_tac
          >> fs [clean_prog_def, PAIR_MAP]
          >> qexists_tac `SND (s.compile_oracle (x + 1))`
          >> Cases_on `s.compile_oracle (x + 1)`
          >> fs [])
      >- (rw [clean_prog_map_fromAList]
          >> Cases_on `prog`
          >> fs []))
QED

Theorem remove_state_rel_do_app_install_Rval[local]:
  ∀args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value t1.
    remove_state_rel s t ∧
    do_app Install args t = Rval (value,t1) ⇒
    ∃s1. do_app Install args s = Rval (value,s1) ∧
      remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> fs [do_app_def]
  >> match_mp_tac
       (Q.SPECL [`args`,`s`,`t`,`value`,`t1`]
          (INST_TYPE [``:'a`` |-> ``:exn_or_ret``]
             remove_state_rel_do_install_Rval))
  >> conj_tac
  >- qpat_x_assum `remove_state_rel s t` ACCEPT_TAC
  >- qpat_x_assum `do_install _ _ = Rval _` ACCEPT_TAC
QED

Theorem remove_state_rel_do_app_install_Rval_fwd[local]:
  ∀args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value s1.
    remove_state_rel s t ∧
    do_app Install args s = Rval (value,s1) ⇒
    ∃t1. do_app Install args t = Rval (value,t1) ∧
      remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> fs [do_app_def]
  >> match_mp_tac
       (Q.SPECL [`args`,`s`,`t`,`value`,`s1`]
          (INST_TYPE [``:'a`` |-> ``:exn_or_ret``]
             remove_state_rel_do_install_Rval_fwd))
  >> conj_tac
  >- qpat_x_assum `remove_state_rel s t` ACCEPT_TAC
  >- qpat_x_assum `do_install _ _ = Rval _` ACCEPT_TAC
QED

Theorem remove_state_rel_do_app_Rval[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value s1.
    remove_state_rel s t ∧ op ≠ Install ∧
    do_app op args s = Rval (value,s1) ⇒
    ∃t1. do_app op args t = Rval (value,t1) ∧
      remove_state_rel s1 t1
Proof
  rpt strip_tac
  >> fs [remove_state_rel_def, state_component_equality]
  >> qexists_tac
       `t with <| refs := s1.refs; clock := s1.clock;
                   global := s1.global; ffi := s1.ffi |>`
  >> conj_tac
  >- (`do_app op args t =
        do_app op args
          (t with <| refs := s.refs; clock := s.clock;
                      global := s.global; ffi := s.ffi |>)` by
         (AP_TERM_TAC >> fs [state_component_equality])
      >> qpat_assum
           `do_app _ _ _ = do_app _ _ _`
           (fn h => once_rewrite_tac [h])
      >> match_mp_tac do_app_state_swap_Rval
      >> qpat_x_assum `t.code = map _ s.code`
           (fn h => rw [h]))
  >- (imp_res_tac bviPropsTheory.do_app_code
      >> imp_res_tac bviPropsTheory.do_app_oracle
      >> fs [state_component_equality])
QED

Theorem remove_state_rel_do_app_Rerr[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) error.
    remove_state_rel s t ∧ op ≠ Install ∧
    do_app op args s = Rerr error ⇒
    do_app op args t = Rerr error
Proof
  rpt strip_tac
  >> fs [remove_state_rel_def, state_component_equality]
  >> sg `do_app op args t =
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                    global := s.global; ffi := s.ffi |>)`
  >- (AP_TERM_TAC >> fs [state_component_equality])
  >> qpat_assum
       `do_app _ _ _ = do_app _ _ _`
       (fn h => once_rewrite_tac [h])
  >> match_mp_tac do_app_state_swap_Rerr
  >> qpat_x_assum `t.code = map _ s.code`
       (fn h => rw [h])
QED

Theorem do_install_Rerr_type[local]:
  ∀args (s:('c,'ffi) bviSem$state) error.
    do_install args s = Rerr error ⇒
    error = Rabort Rtype_error
Proof
  rpt strip_tac
  >> fs [do_install_def, case_eq_thms, UNCURRY]
QED

Theorem remove_state_rel_do_app_Rerr_eq[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) error1 error2.
    remove_state_rel s t ∧
    do_app op args s = Rerr error1 ∧
    do_app op args t = Rerr error2 ⇒
    error1 = error2
Proof
  rpt strip_tac
  >> Cases_on `op = Install`
  >- (fs [do_app_def]
      >> imp_res_tac do_install_Rerr_type
      >> fs [])
  >- (qspecl_then [`op`,`args`,`s`,`t`,`error1`]
         mp_tac remove_state_rel_do_app_Rerr
      >> impl_tac
      >- (fs [])
      >> fs [])
QED

Theorem remove_state_rel_do_app_Rval_Rerr_absurd[local]:
  ∀op args (s:('c,'ffi) bviSem$state)
      (t:('c,'ffi) bviSem$state) value s1 error.
    remove_state_rel s t ∧
    do_app op args s = Rval (value,s1) ∧
    do_app op args t = Rerr error ⇒ F
Proof
  rpt strip_tac
  >> Cases_on `op = Install`
  >- (rveq
      >> imp_res_tac remove_state_rel_do_app_install_Rval_fwd
      >> gvs [])
  >- (qspecl_then [`op`,`args`,`s`,`t`,`value`,`s1`]
           mp_tac remove_state_rel_do_app_Rval
      >> impl_tac
      >- fs []
      >> fs [])
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
  fs [remove_ticks_exp_def, evaluate_def]
  >> rveq
  >> fs []
  >> CASE_TAC
  >- (rveq >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >- (rveq >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
QED

Resume evaluate_remove_ticks_mutual[If]:
  rw [remove_ticks_exp_def, evaluate_def]
  >> qpat_x_assum
       `evaluate ([remove_ticks_exp (If e e' e'')],env,t) = (res,t1)`
       mp_tac
  >> fs [remove_ticks_exp_def, evaluate_def]
  >> strip_tac
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
       ["cond_result cond_state"]
  >> namedCases_on `cond_result` ["cond_values", "cond_error"]
  >> fs [case_eq_thms]
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rval cond_values`,`cond_state`] mp_tac)
      >> fs []
      >> strip_tac
      >> imp_res_tac evaluate_clock
      >> fs []
      >> qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e'],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`cond_state`,`s1`,`res`,`t1`] mp_tac)
      >> fs []
      >> strip_tac
      >> qpat_x_assum
       `evaluate ([e],env,s with clock := extra + s.clock) = _`
       assume_tac
      >> drule evaluate_add_clock
      >> fs [inc_clock_def]
      >> disch_then assume_tac
      >> qpat_x_assum
       `∀ck. evaluate ([e],env,s with clock := ck + (extra + s.clock)) = _`
       (qspec_then `extra'` assume_tac)
      >> qexists_tac `extra + extra'`
      >> qexists_tac `s1'`
      >> conj_tac
      >- (qexists_tac `Rval cond_values`
          >> qexists_tac `s1 with clock := extra' + s1.clock`
          >> conj_tac
          >- metis_tac [add_clock_rotate]
          >- (disj1_tac >> qexists_tac `cond_values` >> fs []))
      >- fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rval cond_values`,`cond_state`] mp_tac)
      >> fs []
      >> strip_tac
      >> imp_res_tac evaluate_clock
      >> fs []
      >> qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e''],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`cond_state`,`s1`,`res`,`t1`] mp_tac)
      >> fs []
      >> strip_tac
      >> qpat_x_assum
       `evaluate ([e],env,s with clock := extra + s.clock) = _`
       assume_tac
      >> drule evaluate_add_clock
      >> fs [inc_clock_def]
      >> disch_then assume_tac
      >> qpat_x_assum
       `∀ck. evaluate ([e],env,s with clock := ck + (extra + s.clock)) = _`
       (qspec_then `extra'` assume_tac)
      >> qexists_tac `extra + extra'`
      >> qexists_tac `s1'`
      >> conj_tac
      >- (qexists_tac `Rval cond_values`
          >> qexists_tac `s1 with clock := extra' + s1.clock`
          >> conj_tac
          >- metis_tac [add_clock_rotate]
          >- (disj1_tac
              >> qexists_tac `cond_values`
              >> conj_tac
              >- fs []
              >- (disj2_tac >> fs [])))
      >- fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rval cond_values`,`cond_state`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj1_tac
      >> qexists_tac `vs`
      >> fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rerr cond_error`,`cond_state`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `cond_error`
      >> fs [])
QED

Resume evaluate_remove_ticks_mutual[Let]:
  fs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)` ["q r"]
  >> fs [case_eq_thms]
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> imp_res_tac evaluate_clock
      >> fs []
      >> qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`vs ++ env`,`r`,`s1`,`res`,`t1`] mp_tac)
      >> fs []
      >> strip_tac
      >> qpat_x_assum
       `evaluate (es,env,s with clock := extra + s.clock) = _`
       assume_tac
      >> drule evaluate_add_clock
      >> fs [inc_clock_def]
      >> disch_then assume_tac
      >> qpat_x_assum
       `∀ck. evaluate (es,env,s with clock := ck + (extra + s.clock)) = _`
       (qspec_then `extra'` assume_tac)
      >> qexists_tac `extra + extra'`
      >> qexists_tac `s1'`
      >> fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `v7`
      >> fs [])
QED

Resume evaluate_remove_ticks_mutual[Raise]:
  fs [remove_ticks_exp_def, evaluate_def, case_eq_thms]
  >> rpt strip_tac
  >> rveq
  >> fs []
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rval vs`,`s'`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`Rerr v7`,`s'`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> fs [])
QED

Resume evaluate_remove_ticks_mutual[Tick]:
  fs [remove_ticks_exp_def, evaluate_def, case_eq_thms]
  >> rpt strip_tac
  >> rveq
  >> qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
  >> fs []
  >> strip_tac
  >> fs [remove_state_rel_def]
  >> rveq
  >> fs [state_component_equality]
  >> qexists_tac `SUC extra`
  >> fs [dec_clock_def]
  >> qexists_tac `s1`
  >> fs [state_component_equality]
  >> fs [ADD1]
QED

Resume evaluate_remove_ticks_mutual[Call]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def, IS_SOME_MAP]
  >> IF_CASES_TAC
  >- (strip_tac
      >> gvs []
      >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >- (qpat_x_assum `¬(_ = NONE ∧ IS_SOME _)` kall_tac
      >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
           ["args_res args_st"]
      >> qpat_x_assum
           `∀env' t' s' res' t1'.
              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
              evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
      >> fs []
      >> strip_tac
      >> namedCases_on `args_res` ["arg_vals", "arg_err"]
      >- (strip_tac
          >> qspecl_then [`dest`,`arg_vals`,`s1`,`args_st`] mp_tac
               remove_state_rel_find_code_eq
          >> fs []
          >> strip_tac
          >> namedCases_on `find_code dest arg_vals s1.code` ["", "callee"]
          >- (gvs []
              >> qexistsl [`extra`,`s1`]
              >> gvs [])
          >- (PairCases_on `callee`
              >> gvs []
              >> `s1.clock = args_st.clock`
                   by fs [remove_state_rel_def, state_component_equality]
              >> Cases_on `args_st.clock = 0`
              >> gvs []
              >- (qexistsl [`extra`,`s1 with clock := 0`]
                  >> gvs []
                  >> fs [remove_state_rel_def, state_component_equality])
              >- (namedCases_on
                       `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1 args_st)`
                       ["body_res body_st"]
                  >> `args_st.clock - 1 < k`
                       by (irule clock_sub_lt
                           >> imp_res_tac evaluate_clock
                           >> fs [])
                  >> qpat_x_assum `∀m. m < k ⇒ _`
                       (qspec_then `args_st.clock - 1` mp_tac)
                  >> fs []
                  >> strip_tac
                  >> `remove_state_rel (s1 with clock := args_st.clock − 1)
                        (args_st with clock := args_st.clock − 1)`
                       by fs [remove_state_rel_def, state_component_equality]
                  >> qpat_x_assum
                       `∀e env' t' s' res' t1'.
                          remove_state_rel s' t' ∧ t'.clock ≤ _ ∧
                          evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
                       (qspecl_then [`callee1`,`callee0`,`dec_clock 1 args_st`,
                                     `dec_clock 1 s1`,`body_res`,`body_st`] mp_tac)
                  >> fs [dec_clock_def]
                  >> strip_tac
                  >> qmatch_asmsub_rename_tac
                       `evaluate ([callee1],callee0,
                          s1 with clock := body_extra + args_st.clock − 1) =
                            (body_res,body_src)`
                  >> qpat_x_assum `evaluate (es,env,s with clock := extra + s.clock) = _`
                       assume_tac
                  >> drule evaluate_add_clock
                  >> fs [inc_clock_def]
                  >> disch_then assume_tac
                  >> qpat_x_assum `∀ck. evaluate (es,env,_) = _`
                       (qspec_then `ticks + body_extra` assume_tac)
                  >> namedCases_on `body_res` ["body_vals", "body_err"]
                  >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                      >> gvs [])
                  >> namedCases_on `body_err` ["raised", "aborted"]
                  >- (namedCases_on `raised` ["exn_val", "ret_vals"]
                      >- (namedCases_on `handler` ["", "handle_exp"]
                          >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                              >> gvs [])
                          >- (namedCases_on
                                   `evaluate ([remove_ticks_exp handle_exp],exn_val::env,body_st)`
                                   ["hres hst"]
                              >> `body_st.clock ≤ k`
                                   by (imp_res_tac evaluate_clock >> fs [])
                              >> qpat_x_assum `∀e. SOME handle_exp = SOME e ⇒ _`
                                   (qspec_then `handle_exp` mp_tac)
                              >> fs []
                              >> strip_tac
                              >> qpat_x_assum
                                   `∀env' t' s' res' t1'.
                                      remove_state_rel s' t' ∧ t'.clock ≤ k ∧
                                      evaluate ([remove_ticks_exp handle_exp],env',t') = (res',t1') ⇒ _`
                                   (qspecl_then [`exn_val::env`,`body_st`,`body_src`,`hres`,`hst`] mp_tac)
                              >> fs []
                              >> strip_tac
                              >> qmatch_asmsub_rename_tac
                                   `evaluate ([handle_exp],exn_val::env,
                                      body_src with clock := handler_extra + body_src.clock) =
                                        (hres,handler_src)`
                              >> qpat_x_assum `evaluate (es,env,_) = (Rval arg_vals,s1 with clock := _)`
                                   kall_tac
                              >> qpat_x_assum
                                   `evaluate ([callee1],callee0,_) =
                                      (Rerr (Rraise (Exn exn_val)),body_src)`
                                   assume_tac
                              >> drule evaluate_add_clock
                              >> fs [inc_clock_def]
                              >> disch_then assume_tac
                              >> qpat_x_assum `∀ck. evaluate ([callee1],callee0,_) = _`
                                   (qspec_then `handler_extra` assume_tac)
                              >> qpat_x_assum `evaluate (es,env,s with clock := extra + s.clock) = _`
                                   assume_tac
                              >> drule evaluate_add_clock
                              >> fs [inc_clock_def]
                              >> disch_then assume_tac
                              >> qpat_x_assum `∀ck. evaluate (es,env,_) = _`
                                   (qspec_then `ticks + body_extra + handler_extra` assume_tac)
                              >> qexistsl [`ticks + body_extra + handler_extra + extra`,`handler_src`]
                              >> gvs []
                              >> every_case_tac
                              >> gvs []))
                      >> qexistsl [`ticks + body_extra + extra`,`body_src`]
                      >> gvs [])
                  >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                      >> gvs []))))
      >- (strip_tac
          >> gvs []
          >> qexistsl [`extra`,`s1`]
          >> gvs []))
QED

Resume evaluate_remove_ticks_mutual[Force]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> `t.refs = s.refs ∧ t.clock = s.clock`
       by fs [remove_state_rel_def, state_component_equality]
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> IF_CASES_TAC
  >- (strip_tac
      >> gvs []
      >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >> namedCases_on `dest_thunk (EL n env) s.refs`
       ["", "", "thunk_mode thunk_val"]
  >- (strip_tac
      >> gvs []
      >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >- (strip_tac
      >> gvs []
      >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >> namedCases_on `thunk_mode` ["", ""]
  >- (strip_tac
      >> gvs []
      >> qexists_tac `0`
      >> fs [remove_state_rel_def, state_component_equality])
  >- (strip_tac
      >> qspecl_then [`SOME loc`,`[EL n env; thunk_val]`,`s`,`t`] mp_tac
           remove_state_rel_find_code_eq
      >> fs []
      >> strip_tac
      >> namedCases_on `find_code (SOME loc) [EL n env; thunk_val] s.code`
           ["", "callee"]
      >- (gvs []
          >> qexists_tac `0`
          >> fs [remove_state_rel_def, state_component_equality])
      >- (PairCases_on `callee`
          >> gvs []
          >> Cases_on `s.clock = 0`
          >> gvs []
          >- (qexistsl [`0`,`s with clock := 0`]
              >> fs [remove_state_rel_def, state_component_equality])
          >- (namedCases_on `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1 t)`
                   ["body_res body_st"]
              >> `s.clock - 1 < k`
                   by (irule clock_sub_lt >> fs [])
              >> qpat_x_assum `∀m. m < k ⇒ _`
                   (qspec_then `s.clock - 1` mp_tac)
              >> fs []
              >> strip_tac
              >> `remove_state_rel (s with clock := s.clock − 1)
                    (t with clock := t.clock − 1)`
                   by fs [remove_state_rel_def, state_component_equality]
              >> qpat_x_assum
                   `∀e env' t' s' res' t1'.
                      remove_state_rel s' t' ∧ t'.clock ≤ _ ∧
                      evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
                   (qspecl_then [`callee1`,`callee0`,`t with clock := t.clock − 1`,
                                 `s with clock := s.clock − 1`,`body_res`,`body_st`] mp_tac)
              >> fs [dec_clock_def]
              >> strip_tac
              >> qmatch_asmsub_rename_tac
                   `evaluate ([callee1],callee0,s with clock := body_extra + s.clock − 1) =
                      (body_res,body_src)`
              >> qexistsl [`body_extra`,`body_src`]
              >> gvs [dec_clock_def]
              >> every_case_tac
              >> gvs [])))
QED

Resume evaluate_remove_ticks_mutual[Op]:
  fs [remove_ticks_exp_def, evaluate_def]
  >> Cases_on `evaluate (remove_ticks_exps es,env,t)`
  >> fs [case_eq_thms]
  >- (qpat_x_assum
           `∀env' t' s' res' t1'. _`
           (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> Cases_on `op = Install`
      >- (qspecl_then
               [`REVERSE vs`,`s1`,`r`,`v3`,`t1`]
               mp_tac remove_state_rel_do_app_install_Rval
          >> impl_tac
          >- (fs [])
          >> strip_tac
          >> rename1 `remove_state_rel install_state t1`
          >> qexists_tac `extra`
          >> qexists_tac `install_state`
          >> conj_tac
          >- (qexists_tac `Rval vs`
              >> qexists_tac `s1`
              >> conj_tac
              >- (first_assum ACCEPT_TAC)
              >- (disj1_tac
                  >> qexists_tac `vs`
                  >> conj_tac
                  >- (fs [])
                  >- (disj1_tac
                      >> qexists_tac `(v3,install_state)`
                      >> fs [])))
          >- (first_assum ACCEPT_TAC))
      >- (Cases_on `do_app op (REVERSE vs) s1`
          >> fs [case_eq_thms]
          >~ [`do_app op (REVERSE vs) s1 = Rval _`]
          >- (qspecl_then
                   [`op`,`REVERSE vs`,`s1`,`r`,`FST a`,`SND a`]
                   mp_tac remove_state_rel_do_app_Rval
              >> impl_tac
              >- (fs [])
              >> strip_tac
              >> qexists_tac `extra`
              >> qexists_tac `SND a`
              >> conj_tac
              >- (qexists_tac `Rval vs`
                  >> qexists_tac `s1`
                  >> fs []
                  >> qexists_tac `FST a`
                  >> fs [])
              >- (Cases_on `a`
                  >> fs []
                  >> qpat_x_assum `t1' = t1` (fn h => fs [h])))
          >> qspecl_then
               [`op`,`REVERSE vs`,`s1`,`r`,`e`]
               mp_tac remove_state_rel_do_app_Rerr
          >> impl_tac
          >- (fs [])
          >> fs []))
  >- (qpat_x_assum
           `∀env' t' s' res' t1'.
              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
              evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> Cases_on `do_app op (REVERSE vs) s1`
      >> fs [case_eq_thms]
      >- (qspecl_then [`op`,`REVERSE vs`,`s1`,`t1`,`FST a`,`SND a`,`e`]
               mp_tac remove_state_rel_do_app_Rval_Rerr_absurd
          >> fs [])
      >- (qspecl_then [`op`,`REVERSE vs`,`s1`,`t1`,`e'`,`e`]
               mp_tac remove_state_rel_do_app_Rerr_eq
          >> impl_tac
          >- fs []
          >> strip_tac
          >> qexists_tac `extra`
          >> qexists_tac `s1`
          >> conj_tac
          >- (qexists_tac `Rval vs`
              >> qexists_tac `s1`
              >> fs [])
          >- fs []))
  >- (qpat_x_assum
           `∀env' t' s' res' t1'.
              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
              evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `v10`
      >> fs [])
QED

Resume evaluate_remove_ticks_mutual[LetCall]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> fs []
  >> strip_tac
  >> namedCases_on `args_res` ["arg_vals", "arg_err"]
  >- (strip_tac
      >> qspecl_then [`SOME dest`,`arg_vals`,`s1`,`args_st`] mp_tac
           remove_state_rel_find_code_eq
      >> fs []
      >> strip_tac
      >> namedCases_on `find_code (SOME dest) arg_vals s1.code` ["", "callee"]
      >- (gvs []
          >> qexistsl [`extra`,`s1`]
          >> gvs [])
      >- (PairCases_on `callee`
          >> gvs []
          >> `s1.clock = args_st.clock`
               by fs [remove_state_rel_def, state_component_equality]
          >> Cases_on `args_st.clock = 0`
          >> gvs []
          >- (qexistsl [`extra`,`s1 with clock := 0`]
              >> gvs []
              >> fs [remove_state_rel_def, state_component_equality])
          >- (namedCases_on
                   `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1 args_st)`
                   ["body_res body_st"]
              >> `args_st.clock - 1 < k`
                   by (irule clock_sub_lt
                       >> imp_res_tac evaluate_clock
                       >> fs [])
              >> qpat_x_assum `∀m. m < k ⇒ _`
                   (qspec_then `args_st.clock - 1` mp_tac)
              >> fs []
              >> strip_tac
              >> `remove_state_rel (s1 with clock := args_st.clock − 1)
                    (args_st with clock := args_st.clock − 1)`
                   by fs [remove_state_rel_def, state_component_equality]
              >> qpat_x_assum
                   `∀e env' t' s' res' t1'.
                      remove_state_rel s' t' ∧ t'.clock ≤ args_st.clock − 1 ∧
                      evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
                   (qspecl_then [`callee1`,`callee0`,`dec_clock 1 args_st`,
                                 `dec_clock 1 s1`,`body_res`,`body_st`] mp_tac)
              >> fs [dec_clock_def]
              >> strip_tac
              >> qmatch_asmsub_rename_tac
                   `evaluate ([callee1],callee0,
                      s1 with clock := body_extra + args_st.clock − 1) =
                        (body_res,body_src)`
              >> qpat_x_assum `evaluate (es,env,s with clock := extra + s.clock) = _`
                   assume_tac
              >> drule evaluate_add_clock
              >> fs [inc_clock_def]
              >> disch_then assume_tac
              >> qpat_x_assum `∀ck. evaluate (es,env,_) = _`
                   (qspec_then `ticks + body_extra` assume_tac)
              >> namedCases_on `body_res` ["body_vals", "body_err"]
              >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                  >> gvs [])
              >> namedCases_on `body_err` ["raised", "aborted"]
              >- (namedCases_on `raised` ["exn_val", "ret_vals"]
                  >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                      >> gvs [])
                  >> Cases_on `LENGTH ret_vals = rets`
                  >> gvs []
                  >- (namedCases_on `evaluate ([remove_ticks_exp e],ret_vals ++ env,body_st)`
                           ["cont_res cont_st"]
                      >> `body_st.clock ≤ k`
                           by (imp_res_tac evaluate_clock >> fs [])
                      >> qpat_x_assum
                           `∀env' t' s' res' t1'.
                              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
                              evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
                           (qspecl_then [`ret_vals ++ env`,`body_st`,`body_src`,
                                         `cont_res`,`cont_st`] mp_tac)
                      >> fs []
                      >> strip_tac
                      >> qmatch_asmsub_rename_tac
                           `evaluate ([e],ret_vals ++ env,
                              body_src with clock := cont_extra + body_src.clock) =
                                (res,cont_src)`
                      >> qpat_x_assum `evaluate (es,env,_) = (Rval arg_vals,s1 with clock := _)`
                           kall_tac
                      >> qpat_x_assum
                           `evaluate ([callee1],callee0,_) =
                              (Rerr (Rraise (Ret ret_vals)),body_src)`
                           assume_tac
                      >> drule evaluate_add_clock
                      >> fs [inc_clock_def]
                      >> disch_then assume_tac
                      >> qpat_x_assum `∀ck. evaluate ([callee1],callee0,_) = _`
                           (qspec_then `cont_extra` assume_tac)
                      >> qpat_x_assum `evaluate (es,env,s with clock := extra + s.clock) = _`
                           assume_tac
                      >> drule evaluate_add_clock
                      >> fs [inc_clock_def]
                      >> disch_then assume_tac
                      >> qpat_x_assum `∀ck. evaluate (es,env,_) = _`
                           (qspec_then `ticks + body_extra + cont_extra` assume_tac)
                      >> qexistsl [`ticks + body_extra + cont_extra + extra`,`cont_src`]
                      >> gvs [])
                  >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                      >> gvs []))
              >- (qexistsl [`ticks + body_extra + extra`,`body_src`]
                  >> gvs []))))
  >- (strip_tac
      >> gvs []
      >> qexistsl [`extra`,`s1`]
      >> gvs [])
QED

Resume evaluate_remove_ticks_mutual[Return]:
  fs [remove_ticks_exp_def, evaluate_def]
  >> Cases_on `evaluate (remove_ticks_exps es,env,t)`
  >> fs [case_eq_thms]
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `v7`
      >> fs [])
  >- (qpat_x_assum
       `∀env' t' s' res' t1'.
          remove_state_rel s' t' ∧ t'.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env',t') = (res',t1') ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`q`,`r`] mp_tac)
      >> fs []
      >> strip_tac
      >> qexists_tac `extra`
      >> qexists_tac `s1`
      >> fs []
      >> disj2_tac
      >> qexists_tac `v7`
      >> fs [])
QED

Resume evaluate_remove_ticks_mutual[NIL]:
  fs [remove_ticks_exp_def, evaluate_def]
  >> qexists_tac `0`
  >> fs [remove_state_rel_def, state_component_equality]
QED

Resume evaluate_remove_ticks_mutual[CONS]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def]
  >> namedCases_on `es` ["", "tail_head tail_rest"]
  >- (strip_tac
      >> qpat_x_assum
           `∀env' t' s' res' t1'.
              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
              evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
      >> fs [])
  >- (simp [remove_ticks_exp_def, evaluate_def]
      >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
           ["head_res head_st"]
      >> qpat_x_assum
           `∀env' t' s' res' t1'.
              remove_state_rel s' t' ∧ t'.clock ≤ k ∧
              evaluate ([remove_ticks_exp e],env',t') = (res',t1') ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`head_res`,`head_st`] mp_tac)
      >> fs []
      >> strip_tac
      >> namedCases_on `head_res` ["head_vals", "head_err"]
      >- (strip_tac
          >> namedCases_on
               `evaluate (remove_ticks_exp tail_head::remove_ticks_exps tail_rest,
                  env,head_st)`
               ["tail_res tail_st"]
          >> `head_st.clock ≤ k`
               by (imp_res_tac evaluate_clock >> fs [])
          >> qpat_x_assum
               `∀env' t' s' res' t1'.
                  remove_state_rel s' t' ∧ t'.clock ≤ k ∧
                  evaluate (remove_ticks_exps (tail_head::tail_rest),env',t') =
                    (res',t1') ⇒ _`
               (qspecl_then [`env`,`head_st`,`s1`,`tail_res`,`tail_st`] mp_tac)
          >> fs [remove_ticks_exp_def]
          >> strip_tac
          >> qmatch_asmsub_rename_tac
               `evaluate (tail_head::tail_rest,env,
                  s1 with clock := tail_extra + s1.clock) = (tail_res,tail_src)`
          >> qpat_x_assum `evaluate ([e],env,s with clock := extra + s.clock) = _`
               assume_tac
          >> drule evaluate_add_clock
          >> fs [inc_clock_def]
          >> disch_then assume_tac
          >> qpat_x_assum `∀ck. evaluate ([e],env,_) = _`
               (qspec_then `tail_extra` assume_tac)
          >> qexistsl [`tail_extra + extra`,`tail_src`]
          >> gvs []
          >> every_case_tac
          >> gvs [])
      >- (strip_tac
          >> gvs []
          >> qexistsl [`extra`,`s1`]
          >> gvs []))
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
  >> qspecl_then [`k`] mp_tac evaluate_remove_ticks_mutual
  >> fs []
  >> strip_tac
  >> qpat_x_assum
       `∀es env t s res t1.
          remove_state_rel s t ∧ t.clock ≤ k ∧
          evaluate (remove_ticks_exps es,env,t) = (res,t1) ⇒ _`
       (qspecl_then [`es`,`env`,`t`,`s`,`res`,`t1`] mp_tac)
  >> fs []
QED

Theorem state_cc_compile_inc_eq:
  state_cc compile_inc cc = state_cc inline_all (remove_ticks_cc cc)
Proof
  rw [state_cc_def, compile_inc_def, remove_ticks_cc_def]
  >> fs [FUN_EQ_THM]
  >> rw []
  >> rpt (pairarg_tac >> fs [])
  >> rveq
  >> fs [clean_prog_def]
QED

Theorem state_co_compile_inc_eq:
  state_co compile_inc co = remove_ticks_co ∘ state_co inline_all co
Proof
  rw [state_co_def, compile_inc_def, remove_ticks_co_def]
  >> fs [FUN_EQ_THM]
  >> rw []
  >> rpt (pairarg_tac >> fs [])
  >> rveq
  >> fs [clean_prog_def]
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

Theorem fromAList_clean_prog[local]:
  ∀prog.
    fromAList (MAP (λ(name,arity,body). (name,arity,remove_ticks_exp body))
      prog) = map (I ## remove_ticks_exp) (fromAList prog)
Proof
  gen_tac
  >> simp [map_fromAList]
  >> AP_TERM_TAC
  >> simp [MAP_EQ_f, FORALL_PROD, PAIR_MAP]
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
  ∀code co ffi cc k start r s.
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (map (I ## remove_ticks_exp) code)
      (remove_ticks_co ∘ co) cc k) = (r,s) ⇒
  ∃ck s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co (remove_ticks_cc cc) (k + ck)) = (r,s2) ∧
    s2.ffi = s.ffi
Proof
  rpt strip_tac
  >> qspecl_then
       [`k`,`[Call 0 (SOME start) [] NONE]`,`[]`,
        `initial_state ffi (map (I ## remove_ticks_exp) code)
           (remove_ticks_co ∘ co) cc k`,
        `initial_state ffi code co (remove_ticks_cc cc) k`,
        `r`,`s`] mp_tac evaluate_remove_ticks
  >> fs [remove_ticks_exp_def, remove_state_rel_def, initial_state_def,
         state_component_equality]
  >> strip_tac
  >> qexists_tac `extra`
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
  >> CCONTR_TAC
  >> qpat_x_assum `semantics _ _ _ _ _ ≠ Fail` mp_tac
  >> simp [semantics_def]
  >> IF_CASES_TAC
  >- simp []
  >> fs []
  >> qpat_x_assum `∀a b. _` (qspecl_then [`j`,`e`] mp_tac)
  >> fs []
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

Theorem semantics_no_type_error[local]:
  ∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ∀j. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j)) ≠ Rerr (Rabort Rtype_error)
Proof
  rpt strip_tac
  >> qpat_x_assum `semantics _ _ _ _ _ ≠ Fail` mp_tac
  >> simp [semantics_def]
  >> IF_CASES_TAC
  >- simp []
  >> fs []
  >> qpat_x_assum `∀k e. _`
       (qspecl_then [`j`,`Rabort Rtype_error`] mp_tac)
  >> fs []
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
  >> fs [compile_prog_def, compile_inc_def]
  >> pairarg_tac
  >> fs []
  >> rveq
  >> fs [state_co_compile_inc_eq, state_cc_compile_inc_eq,
         fromAList_clean_prog]
  >> qspecl_then
       [`fromAList prog1'`,`state_co inline_all co`,`ffi`,`cc`,`k`,`start`,
        `r`,`s`] mp_tac evaluate_remove_ticks_compile
  >> fs []
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
       by (rpt strip_tac
           >> qspecl_then
                [`prog`,`cs1`,`prog1`,`co`,`ffi`,`cc`,`k`,`start`,`r`,`s`]
                mp_tac evaluate_compile_prog
           >> fs [])
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
      >- (qexistsl [`ck + k`,`s2`,`r`,`outcome`]
          >> fs []))
  >- (strip_tac
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
      >- (strip_tac
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
                   evaluate_add_to_clock_io_events_mono
                     |> CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s"]))
                     |> Q.SPEC `s with clock := k`
                     |> SIMP_RULE (srw_ss()) [inc_clock_def]])
          >- (simp [equiv_lprefix_chain_thm]
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
              >- (rw []
                  >> qexists_tac `ck + k`
                  >> fs [])
              >- (rw []
                  >> qexists_tac `k`
                  >> fs []
                  >> qmatch_assum_abbrev_tac `_ < LENGTH (_ src_ffi)`
                  >> `src_ffi.io_events ≼ s2.ffi.io_events`
                       by (qunabbrev_tac `src_ffi`
                           >> metis_tac [initial_state_with_simp,
                                evaluate_add_to_clock_io_events_mono
                                  |> CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s"]))
                                  |> Q.SPEC `s with clock := k`
                                  |> SIMP_RULE (srw_ss()) [inc_clock_def], SND, ADD_SYM])
                  >> fs [IS_PREFIX_APPEND]
                  >> qpat_x_assum `s2.ffi = tgt_st.ffi` (fn h => fs [GSYM h])
                  >> fs [EL_APPEND1]))))
QED

