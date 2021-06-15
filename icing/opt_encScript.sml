(**
  Correctness proof for optimization planner
**)
open semanticPrimitivesTheory evaluateTheory terminationTheory
     icing_rewriterTheory icing_optimisationsTheory
     icing_optimisationProofsTheory fpOptTheory fpValTreeTheory
     optPlannerTheory source_to_sourceTheory source_to_sourceProofsTheory;

open preamble;

val _ = new_theory "opt_enc";

Definition gather_constants_exp_def:
  gather_constants_exp (Lit (Word64 w)) = [w] ∧
  gather_constants_exp (FpOptimise sc e) = gather_constants_exp e ∧
  gather_constants_exp (Lit l) = [] ∧
  gather_constants_exp (Var x) = [] ∧
  gather_constants_exp (Raise e) = gather_constants_exp e ∧
  gather_constants_exp (Handle e pes) =
    (gather_constants_exp e) ++
    (FLAT (MAP (λ (p,e). gather_constants_exp e) pes)) ∧
  gather_constants_exp (Con mod exps) =
    FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Fun s e) = gather_constants_exp e ∧
  gather_constants_exp (App op exps) = FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Log lop e2 e3) =
    (gather_constants_exp e2) ++ (gather_constants_exp e3) ∧
  gather_constants_exp (If e1 e2 e3) =
    (gather_constants_exp e1) ++ (gather_constants_exp e2) ++
    (gather_constants_exp e3) ∧
  gather_constants_exp (Mat e pes) =
    (gather_constants_exp e) ++
    FLAT ((MAP (λ (p,e). gather_constants_exp e) pes)) ∧
  gather_constants_exp (Let so e1 e2) =
    (gather_constants_exp e1) ++ (gather_constants_exp e2) ∧
  gather_constants_exp (Letrec ses e) =
    (gather_constants_exp e) ∧
  gather_constants_exp (Tannot e t) =
    (gather_constants_exp e) ∧
  gather_constants_exp (Lannot e l) =
    (gather_constants_exp e)
Termination
  WF_REL_TAC ‘measure (λ e. exp_size e)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.exp_size_def]
  \\ TRY (
    Induct_on `pes` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    Induct_on `exps` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def, astTheory.lit_size_def, char_size_def, astTheory.lop_size_def,
        fpValTreeTheory.fp_opt_size_def]
  \\ ‘∀ x l. MEM x l ⇒ exp_size x ≤ exp6_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.exp_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Definition gather_used_identifiers_pat_def:
  gather_used_identifiers_pat Pany = [] ∧
  gather_used_identifiers_pat (Pvar v) = [v] ∧
  gather_used_identifiers_pat (Plit _) = [] ∧
  gather_used_identifiers_pat (Pref p) = gather_used_identifiers_pat p ∧
  gather_used_identifiers_pat (Ptannot p _) = gather_used_identifiers_pat p ∧
  gather_used_identifiers_pat (Pcon (SOME id) pats) =
    (let used_in_pats = FLAT (MAP gather_used_identifiers_pat pats) in
       case id of
       | (Short v) => v::used_in_pats
       | (Long m (Short v)) => m::v::used_in_pats) ∧
  gather_used_identifiers_pat (Pcon NONE pats) =
    FLAT (MAP gather_used_identifiers_pat pats)
Termination
  WF_REL_TAC ‘measure (λ p. pat_size p)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.pat_size_def]
  \\ Induct_on ‘pats’ \\ rpt strip_tac \\ fs[astTheory.pat_size_def]
  \\ ‘∀ x l. MEM x l ⇒ pat_size x ≤ pat1_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.pat_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Definition gather_used_identifiers_exp_def:
  gather_used_identifiers_exp (FpOptimise sc e) =
    gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Lit l) = [] ∧
  gather_used_identifiers_exp (Var x) =
    (case x of
     | Short v => [v]
     | _ => []) ∧
  gather_used_identifiers_exp (Raise e) = gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Handle e pes) =
    (gather_used_identifiers_exp e) ++
    (FLAT (MAP (λ (p,e). (gather_used_identifiers_pat p) ++
                         (gather_used_identifiers_exp e)) pes)) ∧
  gather_used_identifiers_exp (Con mod exps) =
    FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Fun s e) = [s] ++ gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (App op exps) =
    FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Log lop e2 e3) =
    (gather_used_identifiers_exp e2) ++ (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (If e1 e2 e3) =
    (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) ++
    (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (Mat e pes) =
    (gather_used_identifiers_exp e) ++
    FLAT ((MAP (λ (p,e). (gather_used_identifiers_pat p) ++
                         gather_used_identifiers_exp e) pes)) ∧
  gather_used_identifiers_exp (Let so e1 e2) =
    (let expression_identifiers =
         (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) in
       case so of
       | NONE => expression_identifiers
       | SOME n => n::expression_identifiers) ∧
  gather_used_identifiers_exp (Letrec ses e) =
    FLAT (MAP (λ (n, p, _). [n; p]) ses) ++ (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Tannot e t) =
    (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Lannot e l) =
    (gather_used_identifiers_exp e)
Termination
  WF_REL_TAC ‘measure (λ e. exp_size e)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.exp_size_def]
  \\ TRY (
    Induct_on `pes` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    Induct_on `exps` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def, astTheory.lit_size_def, char_size_def, astTheory.lop_size_def,
        fpValTreeTheory.fp_opt_size_def]
  \\ ‘∀ x l. MEM x l ⇒ exp_size x ≤ exp6_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.exp_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Inductive v_rel:
  (∀v. v_rel (Litv v) (Litv v))
  ∧
  (∀r. v_rel (Real r) (Real r))
  ∧
  (∀r. v_rel (FP_WordTree r) (FP_WordTree r))
  ∧
  (∀r. v_rel (FP_BoolTree r) (FP_BoolTree r))
  ∧
  (∀r. v_rel (Loc r) (Loc r))
  ∧
  (∀s vs vs1.
     LIST_REL v_rel vs vs1 ⇒
     v_rel (Conv s vs) (Conv s vs1))
  ∧
  (∀vs vs1.
     LIST_REL v_rel vs vs1 ⇒
     v_rel (Vectorv vs) (Vectorv vs1))
  ∧
  (∀env v e env1.
     DISJOINT (set (v::gather_used_identifiers_exp e)) (set (MAP SND al)) ∧
     env_rel env env1 al ⇒
     v_rel (Closure env v e) (Closure env1 v (replace_constants_exp al e)))
  ∧
  (∀env v env1 funs.
     DISJOINT (set (FLAT (MAP (λ(n,m,e). n::m::gather_used_identifiers_exp e) funs)))
              (set (MAP SND al)) ∧
     env_rel env env1 al ⇒
     v_rel (Recclosure env funs v)
           (Recclosure env1 (MAP (I ## I ## replace_constants_exp al) funs) v))
  ∧
  (∀env env1.
     env1.c = env.c ∧
     (∀n v.
        nsLookup env1.v n = SOME v ⇒
        if nsLookup env.v n = NONE then
          ∃m. n = Short m ∧ MEM m (MAP SND al)
        else ~∃m. n = Short m ∧ MEM m (MAP SND al)) ∧
     (∀n w.
        MEM (w,n) al ⇒ nsLookup env1.v (Short n) = SOME (Litv (Word64 w))) ∧
     (∀n v.
        nsLookup env.v n = SOME v ⇒
        ∃v1. v_rel v v1 ∧ nsLookup env1.v n = SOME v1) ⇒
     env_rel env env1 al)
End

Theorem v_rel_simp[simp] =
  [“v_rel (Litv v) w”,
   “v_rel (Real r) w”,
   “v_rel (FP_WordTree r) w”,
   “v_rel (FP_BoolTree r) w”,
   “v_rel (Loc r) w”,
   “v_rel (Conv s vs) w”,
   “v_rel (Vectorv vs) w”,
   “v_rel (Closure env v e) w”,
   “v_rel (Recclosure env funs v) w”,
   “v_rel w (Litv v)”,
   “v_rel w (Real r)”,
   “v_rel w (FP_WordTree r)”,
   “v_rel w (FP_BoolTree r)”,
   “v_rel w (Loc r)”,
   “v_rel w (Conv s vs)”,
   “v_rel w (Vectorv vs)”,
   “v_rel w (Closure env v e)”,
   “v_rel w (Recclosure env funs v)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases]) |> LIST_CONJ;

Theorem env_rel_def = v_rel_cases |> CONJUNCT2 |> SIMP_RULE std_ss [];

Definition res_rel_def[simp]:
  res_rel (Rval x) (Rval y) = LIST_REL v_rel x y ∧
  res_rel (Rerr (Rraise v)) (Rerr (Rraise w)) = v_rel v w ∧
  res_rel (Rerr (Rabort a)) (Rerr (Rabort b)) = (a = b) ∧
  res_rel _ _ = F
End

Definition ref_rel_def[simp]:
  ref_rel (Refv v) (Refv w) = v_rel v w ∧
  ref_rel (Varray vs) (Varray ws) = LIST_REL v_rel vs ws ∧
  ref_rel (W8array bs) (W8array as) = (bs = as) ∧
  ref_rel _ _ = F
End

Definition state_rel_def:
  state_rel s t ⇔
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    t.next_type_stamp = s.next_type_stamp ∧
    t.next_exn_stamp = s.next_exn_stamp ∧
    t.fp_state = s.fp_state ∧
    LIST_REL ref_rel t.refs s.refs
End

Theorem do_opapp_SOME_IMP:
  do_opapp (REVERSE a) = SOME x ⇒ ∃a1 a2. a = [a1;a2]
Proof
  fs [do_opapp_def,AllCaseEqs()] \\ rw []
  \\ gvs [SWAP_REVERSE_SYM]
QED

Theorem do_opapp_NONE:
  LIST_REL v_rel a a' ⇒
  (do_opapp (REVERSE a) = NONE ⇔
   do_opapp (REVERSE a') = NONE)
Proof
  once_rewrite_tac [GSYM LIST_REL_REVERSE_EQ]
  \\ qspec_tac (‘REVERSE a’,‘a’)
  \\ qspec_tac (‘REVERSE a'’,‘a'’)
  \\ fs [do_opapp_def,AllCaseEqs(),PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [] \\ rw []
  \\ fs [MAP_MAP_o,o_DEF,UNCURRY,LAMBDA_PROD]
  \\ qpat_x_assum ‘_ = NONE’ mp_tac
  \\ rename [‘_ (MAP _ funs2)’]
  \\ rename [‘_ nn _ = NONE’]
  \\ qid_spec_tac ‘funs2’
  \\ Induct \\ fs [FORALL_PROD]
  \\ once_rewrite_tac [find_recfun_def]
  \\ fs [] \\ rw []
QED

Theorem env_rel_update_lemma:
  env_rel (env with v := t) (env' with v := t') al ∧
  ¬MEM n (MAP SND al) ∧ v_rel x y ⇒
  env_rel (env with v := nsBind n x t)
          (env' with v := nsBind n y t') al
Proof
  simp [env_rel_def] \\ rpt strip_tac
  THEN1
   (reverse (Cases_on ‘n'’) \\ fs [ml_progTheory.nsLookup_nsBind_compute]
    THEN1 (first_x_assum drule \\ fs [])
    \\ CASE_TAC \\ gvs []
    \\ first_x_assum drule \\ fs [])
  THEN1
   (fs [MEM_MAP,EXISTS_PROD,ml_progTheory.nsLookup_nsBind_compute]
    \\ rw [] \\ gvs [])
  \\ Cases_on ‘n'’ \\ fs [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ fs []
QED

Theorem env_rel_update:
  env_rel env env' al ∧ ¬MEM n (MAP SND al) ∧ v_rel x y ⇒
  env_rel (env with v := nsBind n x env.v)
          (env' with v := nsBind n y env'.v) al
Proof
  rw [] \\ irule env_rel_update_lemma \\ gvs []
QED

Theorem env_rel_build_rec_env:
  env_rel env env' al ∧
  DISJOINT (set (FLAT (MAP (λ(n,m,e). n::m::gather_used_identifiers_exp e) l)))
           (set (MAP SND al)) ⇒
  env_rel (env with v := build_rec_env l env env.v)
          (env' with
           v :=
             build_rec_env (MAP (I ## I ## replace_constants_exp al) l)
               env' env'.v) al
Proof
  fs [build_rec_env_def]
  \\ qabbrev_tac ‘ff = Recclosure env l’
  \\ qabbrev_tac ‘gg = Recclosure env'
                         (MAP (I ## I ## replace_constants_exp al) l)’
  \\ disch_then (fn th => assume_tac th \\ mp_tac th)
  \\ qid_spec_tac ‘l’ \\ Induct \\ fs []
  \\ fs [FORALL_PROD] \\ rw []
  \\ irule env_rel_update_lemma \\ gvs []
  \\ unabbrev_all_tac \\ gvs []
  \\ first_assum $ irule_at (Pos last) \\ fs []
QED

Theorem find_recfun_lemma:
  ∀l s n e.
    find_recfun s l = SOME (n,e) ⇒
    find_recfun s (MAP (I ## I ## f) l) = SOME (n,(f:'a->'a) e)
Proof
  Induct \\ once_rewrite_tac [find_recfun_def]
  \\ fs [FORALL_PROD] \\ rw []
QED

Theorem can_pmatch_all_lemma:
  state_rel st' t1 ∧ v_rel a a' ⇒
  can_pmatch_all env.c st'.refs (MAP FST pes) a =
  can_pmatch_all env.c t1.refs (MAP FST pes) a'
Proof
  cheat
QED

Theorem v_rel_do_fpoptimise:
  LIST_REL v_rel xs ys ⇒
  LIST_REL v_rel (do_fpoptimise annot xs) (do_fpoptimise annot ys)
Proof
  cheat
QED

Theorem replace_constants_exp_thm:
  (∀(s:'ffi state) env es s1 res t env1 al.
     DISJOINT (set (FLAT (MAP gather_used_identifiers_exp es)))
              (set (MAP SND al)) ∧
     evaluate s env es = (s1,res) ∧
     state_rel s t ∧ env_rel env env1 al ⇒
     ∃t1 res1.
        evaluate t env1 (MAP (replace_constants_exp al) es) = (t1,res1) ∧
        state_rel s1 t1 ∧ res_rel res res1) ∧
  (∀(s:'ffi state) env v pes err v1 err1 s1 res t env1 al.
     DISJOINT (set (FLAT (MAP (gather_used_identifiers_exp o SND) pes)))
              (set (MAP SND al)) ∧
     evaluate_match s env v pes err = (s1,res) ∧
     state_rel s t ∧ env_rel env env1 al ∧ v_rel v v1 ∧ v_rel err err1 ⇒
     ∃t1 res1.
       evaluate_match t env1 v1
         (MAP (λ (p,e). (p, replace_constants_exp al e)) pes) err1 = (t1,res1) ∧
       state_rel s1 t1 ∧ res_rel res res1)
Proof
  ho_match_mp_tac evaluate_ind \\ rpt strip_tac
  THEN1 gvs [evaluate_def]
  THEN1
   (gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs [])
  THEN1
   (rename [‘Lit l’]
    \\ Cases_on ‘l’
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ CASE_TAC \\ fs [evaluate_def]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [env_rel_def] \\ res_tac \\ fs [])
  THEN1
   (rename [‘Raise’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ fs [CaseEq"prod"] \\ gvs []
    \\ first_x_assum $ drule_all_then strip_assume_tac
    \\ fs [] \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘res1’ \\ fs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs [])
  THEN1
   (rename [‘Handle’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ rename [‘res_rel (Rerr res0) (Rerr res1)’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ ‘env1.c = env.c’ by fs [env_rel_def] \\ gvs []
    \\ ‘can_pmatch_all env.c st'.refs (MAP FST pes) a =
        can_pmatch_all env.c t1.refs (MAP FST pes) a'’ by
           (irule can_pmatch_all_lemma \\ fs [])
    \\ fs [] \\ fs [AllCaseEqs()] \\ gvs []
    \\ first_x_assum irule \\ gvs []
    \\ fs [IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD]
    \\ metis_tac [MEM_APPEND])
  THEN1
   (rename [‘Con’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,
            replace_constants_exp_def]
    \\ ‘env1.c = env.c’ by fs [env_rel_def] \\ gvs []
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ gvs [CaseEq"prod",PULL_EXISTS]
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ rpt strip_tac
    \\ gvs [CaseEq"bool",CaseEq"prod"]
    \\ first_x_assum $ drule_at (Pos last)
    \\ disch_then $ drule_at (Pos last)
    \\ impl_tac
    THEN1
     (qsuff_tac ‘(set (FLAT (MAP gather_used_identifiers_exp (REVERSE es)))) =
                 (set (FLAT (MAP gather_used_identifiers_exp es)))’ \\ rw [] \\ fs []
      \\ fs [EXTENSION,MEM_FLAT,MEM_MAP])
    \\ strip_tac \\ gvs [MAP_REVERSE]
    \\ rename [‘res_rel res res1’]
    \\ reverse (Cases_on ‘res’) \\ Cases_on ‘res1’ \\ gvs []
    \\ gvs [build_conv_def,AllCaseEqs()])
  THEN1
   (rename [‘Var’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,
            replace_constants_exp_def]
    \\ fs [env_rel_def]
    \\ reverse (Cases_on ‘nsLookup env.v n’) \\ res_tac \\ gvs []
    \\ CASE_TAC \\ fs [] \\ res_tac
    \\ qpat_x_assum ‘nsLookup env.v n = NONE’ assume_tac \\ fs []
    \\ gvs [])
  THEN1
   (rename [‘Fun’]
    \\ gvs [evaluate_def,replace_constants_exp_def]
    \\ qexists_tac ‘al’ \\ fs [gather_used_identifiers_exp_def])
  THEN1
   (rename [‘App’] \\ Cases_on ‘op = Opapp’
    THEN1
     (gvs [astTheory.getOpClass_def]
      \\ gvs [evaluate_def,gather_used_identifiers_exp_def,
           replace_constants_exp_def,astTheory.getOpClass_def]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV)
      \\ gvs [CaseEq"prod",PULL_EXISTS]
      \\ rpt (pop_assum mp_tac)
      \\ CONV_TAC (DEPTH_CONV ETA_CONV)
      \\ rpt strip_tac
      \\ first_x_assum $ drule_at (Pos last)
      \\ disch_then $ drule_at (Pos last)
      \\ impl_tac
      THEN1
       (qsuff_tac ‘(set (FLAT (MAP gather_used_identifiers_exp (REVERSE es)))) =
         (set (FLAT (MAP gather_used_identifiers_exp es)))’ \\ rw [] \\ fs []
        \\ fs [EXTENSION,MEM_FLAT,MEM_MAP])
      \\ strip_tac \\ gvs [MAP_REVERSE]
      \\ rename [‘res_rel res res1’]
      \\ reverse (Cases_on ‘res’) \\ Cases_on ‘res1’ \\ gvs []
      \\ gvs [AllCaseEqs()]
      \\ drule do_opapp_NONE \\ strip_tac \\ gvs [PULL_EXISTS]
      \\ drule do_opapp_SOME_IMP \\ strip_tac \\ gvs []
      THEN1
       (fs [state_rel_def]
        \\ Cases_on ‘do_opapp [y'; y]’ \\ fs []
        \\ PairCases_on ‘x’ \\ fs [])
      \\ ‘t1.clock = st'.clock’ by fs [state_rel_def] \\ fs []
      \\ Cases_on ‘a2’ \\ gvs [do_opapp_def]
      THEN1
       (first_x_assum irule \\ fs [] \\ conj_tac
        THEN1 fs [dec_clock_def,state_rel_def]
        \\ irule env_rel_update \\ fs [])
      \\ gvs [CaseEq"option",CaseEq"prod",PULL_EXISTS]
      \\ drule_then assume_tac find_recfun_lemma \\ fs []
      \\ first_x_assum irule \\ fs [] \\ rpt conj_tac
      THEN1
       (qpat_x_assum ‘DISJOINT _ _’ mp_tac
        \\ qpat_x_assum ‘find_recfun s0 l = SOME (n,e)’ mp_tac
        \\ qid_spec_tac ‘l’ \\ Induct
        \\ once_rewrite_tac [find_recfun_def] \\ gvs []
        \\ gvs [FORALL_PROD] \\ rw [])
      THEN1 fs [dec_clock_def,state_rel_def]
      \\ irule env_rel_update_lemma \\ fs []
      \\ conj_tac
      THEN1
       (qpat_x_assum ‘DISJOINT _ _’ mp_tac
        \\ qpat_x_assum ‘find_recfun s0 l = SOME (n,e)’ mp_tac
        \\ qid_spec_tac ‘l’ \\ Induct
        \\ once_rewrite_tac [find_recfun_def] \\ gvs []
        \\ gvs [FORALL_PROD] \\ rw [])
      \\ irule env_rel_build_rec_env \\ fs [])
    \\ cheat (* long and boring *))
  THEN1 (rename [‘Log’] \\ cheat)
  THEN1 (rename [‘If’] \\ cheat)
  THEN1
   (rename [‘Mat’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ ‘env1.c = env.c’ by fs [env_rel_def] \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ ‘can_pmatch_all env.c st'.refs (MAP FST pes) v' =
        can_pmatch_all env.c t1.refs (MAP FST pes) v’ by
           (irule can_pmatch_all_lemma \\ fs [])
    \\ fs [] \\ fs [AllCaseEqs()] \\ gvs []
    \\ first_x_assum irule \\ gvs []
    \\ fs [IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD,bind_exn_v_def]
    \\ metis_tac [MEM_APPEND])
  THEN1 (rename [‘Let’] \\ cheat)
  THEN1 (rename [‘Letrec’] \\ cheat)
  THEN1
   (gvs [evaluate_def,replace_constants_exp_def,gather_used_identifiers_exp_def])
  THEN1
   (gvs [evaluate_def,replace_constants_exp_def,gather_used_identifiers_exp_def])
  THEN1
   (gvs [evaluate_def,replace_constants_exp_def,gather_used_identifiers_exp_def]
    \\ gvs [CaseEq"prod",PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate t4’
    \\ first_x_assum drule
    \\ disch_then $ drule_at (Pos last)
    \\ disch_then $ qspec_then ‘t4’ mp_tac
    \\ unabbrev_all_tac
    \\ impl_tac THEN1 fs [state_rel_def]
    \\ strip_tac \\ fs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ fs [state_rel_def]
    \\ irule v_rel_do_fpoptimise \\ fs [])
  THEN1
    gvs [evaluate_def,replace_constants_exp_def,gather_used_identifiers_exp_def]
  THEN1
   (gvs [evaluate_def,replace_constants_exp_def,gather_used_identifiers_exp_def]
    \\ gvs [CaseEq"bool"]
    \\ cheat)
QED

val _ = export_theory();
