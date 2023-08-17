(*
   Verification of fast interpreter for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory compute_syntaxTheory
     compute_evalTheory compute_execTheory compute_evalProofTheory;
open ml_monadBaseTheory ml_monadBaseLib;
open mlvectorTheory

val _ = new_theory "compute_execProof";

(* verification *)

Definition from_cv_def[simp]:
  from_cv ((Num n):cv) = (Num n : compute_exp) ∧
  from_cv (Pair x y) = Pair (from_cv x) (from_cv y)
End

Definition from_res_def[simp]:
  from_res f (M_success v) = M_success (f v) ∧
  from_res f (M_failure e) = M_failure e
End

Inductive code_rel:
  (∀eqs v1 n v2.
     ~MEM n v1 ⇒
     code_rel eqs (v1 ++ [n] ++ v2) ((Var n):compute_exp) ((Var (LENGTH v1)):ce)) ∧
  (∀eqs vars n.
     code_rel eqs vars (Num n) (Const n)) ∧
  (∀eqs vars x y x1 y1.
     code_rel eqs vars x x1 ∧
     code_rel eqs vars y y1 ⇒
     code_rel eqs vars (Pair x y) (Binop Pair x1 y1)) ∧
  (∀eqs vars x y z x1 y1 z1.
     code_rel eqs vars x x1 ∧
     code_rel eqs vars y y1 ∧
     code_rel eqs vars z z1 ⇒
     code_rel eqs vars (If x y z) (If x1 y1 z1)) ∧
  (∀eqs vars s x y x1 y1.
     code_rel eqs vars x x1 ∧
     code_rel eqs (s::vars) y y1 ⇒
     code_rel eqs vars (Let s x y) (Let x1 y1)) ∧
  (∀eqs vars xs xs1 f l body n.
     LIST_REL (code_rel eqs vars) xs xs1 ∧
     n < LENGTH eqs ∧ EL n eqs = (f,l,body) ∧
     LENGTH l = LENGTH xs ∧
     (∀k. k < n ⇒ FST (EL k eqs) ≠ f) ⇒
     code_rel eqs vars (App f xs) (App n xs1)) ∧
  (∀eqs vars x x1 m.
     code_rel eqs vars x x1 ⇒
     code_rel eqs vars (Uop m x) (Monop (monop m) x1)) ∧
  (∀eqs vars x y x1 y1 b.
     code_rel eqs vars x x1 ∧
     code_rel eqs vars y y1 ⇒
     code_rel eqs vars (Binop b x y) (Binop (binop b) x1 y1))
End

Theorem option_ALOOKUP:
  ∀eqs n f l body s.
    n < LENGTH eqs ∧
    EL n eqs = (f,l,body) ∧
    (∀k. k < n ⇒ FST (EL k eqs) ≠ f) ⇒
    option (ALOOKUP eqs) f s = (M_success (l,body),s)
Proof
  Induct \\ fs []
  \\ Cases_on ‘n’ \\ fs []
  \\ gvs [option_def,st_ex_return_def,ALOOKUP_def,FORALL_PROD]
  \\ rpt strip_tac
  \\ first_assum $ qspec_then ‘0’ mp_tac
  \\ strip_tac \\ fs []
  \\ first_x_assum irule
  \\ first_x_assum $ irule_at Any
  \\ rw []
  \\ ‘SUC k < SUC n'’ by fs []
  \\ res_tac \\ fs []
QED

Theorem LESS_LENGTH_env_lookup:
  ∀xs n. n < LENGTH xs ⇒ env_lookup n xs = EL n xs
Proof
  Induct \\ fs []
  \\ Cases_on ‘n’ \\ fs [env_lookup_def]
QED

Theorem compute_eval_from_cv:
  ∀x s ck eqs. compute_eval ck eqs (from_cv x) s = (M_success (from_cv x),s)
Proof
  Induct
  \\ fs [compute_eval_def,st_ex_return_def,st_ex_bind_def]
QED

Theorem compile_eval_list_length:
  ∀cvs xs ck ceqs s s'.
    compute_eval_list ck ceqs cvs s = (M_success xs,s') ⇒ LENGTH xs = LENGTH cvs
Proof
  Induct \\ fs [compute_eval_def,st_ex_return_def,st_ex_bind_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
QED

Theorem cexp_value_from_cv:
  ∀y. cexp_value (from_cv y)
Proof
  Induct \\ fs [cexp_value_def]
QED

Triviality cexp_vars_def[simp] = compute_syntaxProofTheory.cexp_vars_def;

Definition eqs_ok_def:
  eqs_ok eqs ⇔
    EVERY (λ(n,args,body).
             cexp_vars body ⊆ set args ∧ ALL_DISTINCT args ∧
             code_rel eqs (REVERSE args) body (compile_to_ce eqs (n,args,body))) eqs
End

Theorem do_uop_from_cv:
  do_uop uop (from_cv a) s = (M_success (from_cv (monop uop a)),s)
Proof
  Cases_on ‘uop’ \\ Cases_on ‘a’
  \\ fs [do_uop_def,monop_def,do_fst_def,do_snd_def,do_ispair_def,st_ex_return_def]
QED

Theorem from_cv_11:
  ∀x y. from_cv x = from_cv y ⇔ x = y
Proof
  Induct \\ Cases_on ‘y’ \\ fs []
QED

Theorem do_binop_from_cv:
  do_binop bop (from_cv a) (from_cv b) s = (M_success (from_cv (binop bop a b)),s)
Proof
  Cases_on ‘bop’ \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ fs []
  \\ fs [binop_def,do_binop_def,do_arith_def,st_ex_return_def,
         SAFEDIV_def,SAFEMOD_def,do_reln_def,cv_T_def,cv_F_def]
  \\ rw [] \\ fs [DIV_EQ_X,do_eq_def,st_ex_return_def,from_cv_11]
  \\ rw []
QED

Theorem env_lookup_lemma:
  ∀v1 env s v2.
    MAP FST env = v1 ++ [s] ++ v2 ∧ ¬MEM s v1 ⇒
    ∃z.
      ALOOKUP (MAP (λ(x,y). (x,from_cv y)) env) s = SOME (from_cv z) ∧
      env_lookup (LENGTH v1) (MAP SND env) = z
Proof
  Induct \\ fs []
  \\ Cases_on ‘env’ \\ fs [] \\ PairCases_on ‘h’ \\ fs [env_lookup_def]
QED

Theorem subst_from_cv:
  ∀v xs. subst xs (from_cv v) = from_cv v
Proof
  Induct \\ fs [subst_def]
QED

Theorem subst_subst:
  ∀e xs ys.
    EVERY (λx. ∃v. SND x = from_cv v) ys ⇒
    subst xs (subst ys e) = subst (ys ++ xs) e
Proof
  ho_match_mp_tac compute_syntaxProofTheory.cexp_vars_ind \\ rw []
  \\ gvs [subst_def,FILTER_APPEND,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]
  \\ gvs [ALOOKUP_APPEND]
  \\ every_case_tac  \\ fs [subst_def]
  \\ fs [EVERY_FILTER_IMP]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM] \\ res_tac
  \\ fs [subst_from_cv]
QED

Theorem alookup_subst:
  ∀e xs ys.
    ALOOKUP xs = ALOOKUP ys ⇒
    subst xs e = subst ys e
Proof
  ho_match_mp_tac compute_syntaxProofTheory.cexp_vars_ind \\ rw []
  \\ gvs [subst_def,MAP_EQ_f]
  \\ first_x_assum irule
  \\ fs [ALOOKUP_FILTER,FUN_EQ_THM]
QED

Theorem subst_cons_lemma:
  subst [(s,from_cv a)]
    (subst
       (FILTER (λ(n,x). n ≠ s) (MAP (λ(x,y). (x,from_cv y)) env)) e2) =
  subst (MAP (λ(x,y). (x,from_cv y)) ((s,a)::env)) e2
Proof
  DEP_REWRITE_TAC [subst_subst] \\ fs []
  \\ conj_tac
  >-
   (fs [EVERY_FILTER,EVERY_MAP,LAMBDA_PROD,EXISTS_PROD]
    \\ fs [EVERY_MEM,FORALL_PROD] \\ metis_tac [])
  \\ irule alookup_subst
  \\ fs [FUN_EQ_THM]
  \\ rw []
  >-
   (fs [ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ fs [MEM_MAP,EXISTS_PROD,MEM_FILTER])
  \\ Induct_on ‘env’ \\ fs []
  \\ PairCases \\ fs [] \\ rw []
QED

Theorem subst_eq_subst_lemma:
  ∀s xs ys.
    ALL_DISTINCT (MAP FST xs) ∧ xs = REVERSE ys ⇒
    subst xs s = subst ys s
Proof
  ho_match_mp_tac compute_syntaxProofTheory.cexp_vars_ind
  \\ rw [] \\ gvs [subst_def]
  \\ fs [MAP_EQ_f]
  \\ imp_res_tac alistTheory.alookup_distinct_reverse
  \\ fs [FILTER_REVERSE]
  \\ first_x_assum irule
  \\ fs [MAP_REVERSE]
  \\ qsuff_tac ‘MAP FST (FILTER (λ(n,x). n ≠ s) ys) = FILTER (λn. n ≠ s) (MAP FST ys)’
  \\ fs [FILTER_ALL_DISTINCT]
  \\ qid_spec_tac ‘ys’ \\ Induct \\ fs [FORALL_PROD]
  \\ rw []
QED

Theorem exec_thm:
  (∀ck eqs e res env e1 s s1.
    compute_eval ck eqs (subst (MAP (λ(x,y). (x, from_cv y)) env) e) s = (res,s1) ∧
    cexp_vars e SUBSET set (MAP FST env) ∧ eqs_ok eqs ∧
    code_rel eqs (MAP FST env) e e1 ⇒
    ∃res1.
      exec (build_funs eqs) (MAP SND env) ck e1 s = (res1,s1) ∧
      res = from_res from_cv res1) ∧
  (∀ck eqs e res env e1 s s1 acc.
    compute_eval_list ck eqs (MAP (subst (MAP (λ(x,y). (x, from_cv y)) env)) e) s = (res,s1) ∧
    EVERY (λe. cexp_vars e SUBSET set (MAP FST env)) e ∧ eqs_ok eqs ∧
    LIST_REL (code_rel eqs (MAP FST env)) e e1 ⇒
    ∃res1.
      exec_list (build_funs eqs) (MAP SND env) ck e1 acc s = (res1,s1) ∧
      from_res (λxs. REVERSE xs ++ MAP from_cv acc) res = from_res (MAP from_cv) res1)
Proof
  ho_match_mp_tac compute_eval_ind_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac
    \\ gvs [subst_def,exec_def,st_ex_return_def]
    \\ drule_all env_lookup_lemma \\ strip_tac \\ fs []
    \\ gvs [compute_eval_from_cv])
  >~ [‘Num’] >-
   (gvs [Once code_rel_cases]
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup,subst_def])
  >~ [‘Pair x y’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,subst_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs []
    \\ Cases_on ‘res1'’ \\ gvs [])
  >~ [‘If x y z’] >-
   (gvs [cexp_consts_ok_def]
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,subst_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [AllCaseEqs()]
    \\ pop_assum mp_tac \\ simp [Once code_rel_cases] \\ rw []
    \\ first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def]
    \\ Cases_on ‘res1’ \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ TRY (first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def])
    \\ Cases_on ‘n’ \\ gvs []
    \\ first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def])
  >~ [‘Let s e1 e2’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac
    \\ Cases_on ‘ck = 0’ \\ gvs [compute_eval_def,exec_def,subst_def]
    \\ gvs [raise_Failure_def,exec_def,st_ex_bind_def]
    \\ gvs [AllCaseEqs(),PULL_EXISTS]
    \\ first_x_assum drule_all \\ gvs [] \\ strip_tac \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs []
    \\ ‘a::MAP SND env = MAP SND ((s,a)::env)’ by fs []
    \\ pop_assum $ once_rewrite_tac o single
    \\ first_x_assum irule
    \\ fs [subst_cons_lemma]
    \\ fs [SUBSET_DEF] \\ metis_tac [])
  >~ [‘App f xs’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac
    \\ qpat_x_assum ‘cexp_vars (App f xs) ⊆ set (MAP FST env)’ mp_tac
    \\ gvs [subst_def]
    \\ Cases_on ‘ck = 0’ \\ gvs [compute_eval_def]
    \\ gvs [raise_Failure_def,exec_def]
    \\ drule_all option_ALOOKUP
    \\ strip_tac \\ fs [st_ex_bind_def,check_def,st_ex_return_def,st_ex_ignore_bind_def]
    \\ ‘n < length (build_funs eqs)’ by fs [build_funs_def,length_def]
    \\ fs [get_code_def,st_ex_return_def]
    \\ disch_then assume_tac
    \\ ‘EVERY (λe. cexp_vars e ⊆ set (MAP FST env)) xs’ by
     (fs [EVERY_MEM,EXTENSION,MEM_MAP,PULL_EXISTS,SUBSET_DEF]
      \\ metis_tac [])
    \\ reverse $ gvs [AllCaseEqs(),SF ETA_ss]
    \\ first_x_assum drule_all
    \\ disch_then $ qspec_then ‘[]’ mp_tac \\ strip_tac \\ gvs []
    >- (Cases_on ‘res1’ \\ fs [])
    \\ Cases_on ‘res1’ \\ fs []
    \\ rename [‘REVERSE vs = _’]
    \\ gvs [SWAP_REVERSE_SYM,sub_def,build_funs_def,EL_MAP]
    \\ gvs [eqs_ok_def,EVERY_EL]
    \\ imp_res_tac compile_eval_list_length \\ fs [MAP_ZIP,MEM_ZIP,PULL_EXISTS]
    \\ qpat_x_assum ‘∀x. _ ⇒ _’ drule
    \\ fs [] \\ strip_tac
    \\ ‘a = MAP SND (ZIP (REVERSE l,a))’ by fs [MAP_ZIP]
    \\ pop_assum $ once_rewrite_tac o single
    \\ first_x_assum irule
    \\ fs [MAP_ZIP]
    \\ first_x_assum $ irule_at $ Pos last
    \\ first_x_assum $ irule_at $ Pos last
    \\ qpat_x_assum ‘_ = (res,s1)’ $ rewrite_tac o single o GSYM
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ ‘MAP (λ(x,y). (x,from_cv y)) (ZIP (REVERSE l,a)) =
        ZIP (REVERSE l,MAP from_cv a)’ by
      (‘LENGTH a = LENGTH l’ by fs []
       \\ pop_assum mp_tac
       \\ qid_spec_tac ‘a’
       \\ qid_spec_tac ‘l’
       \\ Induct using SNOC_INDUCT
       \\ fs [] \\ strip_tac \\ Cases \\ fs [])
    \\ fs []
    \\ irule subst_eq_subst_lemma
    \\ fs [MAP_ZIP,REVERSE_ZIP])
  >~ [‘Uop’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,subst_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs [do_uop_from_cv])
  >~ [‘Binop’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,subst_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs [do_binop_from_cv]
    \\ Cases_on ‘res1'’ \\ gvs [do_binop_from_cv])
  >- (gvs [exec_def,st_ex_return_def,compute_eval_def])
  \\ gvs [compute_eval_def,exec_def]
  \\ fs [Once st_ex_bind_def]
  \\ reverse (gvs [AllCaseEqs()])
  \\ last_x_assum drule_all \\ fs [] \\ strip_tac \\ fs []
  \\ Cases_on ‘res1’ \\ gvs []
  \\ gvs [compute_eval_def,exec_def]
  \\ fs [st_ex_bind_def,st_ex_return_def]
  \\ reverse (gvs [AllCaseEqs()])
  \\ last_x_assum drule_all \\ fs [] \\ strip_tac \\ fs []
  \\ first_x_assum $ qspec_then ‘a::acc’ strip_assume_tac
  \\ gvs [] \\ Cases_on ‘res1’ \\ gvs []
QED

Theorem exec_lemma =
  exec_thm
  |> CONJUNCT1
  |> Q.SPECL [‘ck’,‘eqs’,‘e’,‘res’,‘[]’,‘to_ce eqs [] e’,‘s’,‘s1’]
  |> SIMP_RULE std_ss [MAP,subst_empty,listTheory.LIST_TO_SET];

Triviality LIST_REL_MAP_lemma:
  ∀xs. LIST_REL R xs (MAP f xs) = EVERY (λx. R x (f x)) xs
Proof
  Induct \\ fs []
QED

Theorem code_rel_to_ce:
  ∀e vars eqs.
    cexp_vars e ⊆ set vars ∧ cexp_consts_ok eqs e ∧
    EVERY (λ(n,args,body). cexp_vars body ⊆ set args ∧ cexp_consts_ok eqs body) eqs ∧
    ALL_DISTINCT (MAP FST eqs) ⇒
    code_rel eqs vars e (to_ce eqs vars e)
Proof
  ho_match_mp_tac compute_syntaxProofTheory.cexp_vars_ind
  \\ rw [to_ce_def,cexp_consts_ok_def]
  \\ simp [Once code_rel_cases]
  >-
   (Induct_on ‘vars’ \\ fs [] \\ rw [] \\ fs [indexedListsTheory.findi_def]
    \\ rw [] \\ fs []
    \\ qexists_tac ‘h::v1’ \\ qexists_tac ‘v2’ \\ fs [])
  >-
   (first_x_assum irule
    \\ fs [SUBSET_DEF] \\ metis_tac [])
  \\ gvs [MEM_MAP,EXISTS_PROD,LIST_REL_MAP_lemma]
  \\ fs [EVERY_MEM,FORALL_PROD]
  \\ rename [‘MEM (n,args,body) _’]
  \\ qexists_tac ‘args’
  \\ qexists_tac ‘body’
  \\ fs []
  \\ conj_tac
  >-
   (rw [] \\ first_x_assum irule \\ fs []
    \\ res_tac \\ fs []
    \\ rw [] \\ res_tac \\ fs []
    \\ fs [SUBSET_DEF,PULL_EXISTS,MEM_MAP]
    \\ res_tac \\ fs [])
  \\ qpat_x_assum ‘MEM _ _’ mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘eqs’
  \\ Induct \\ fs [FORALL_PROD]
  \\ rw [] \\ gvs [indexedListsTheory.findi_def]
  \\ rw [] \\ fs []
  \\ gvs [GSYM ADD1,EL]
  \\ gvs [MEM_MAP,FORALL_PROD]
  \\ every_case_tac \\ gvs []
  \\ Cases_on ‘k’ \\ gvs []
QED

Theorem compute_eval_eq_exec:
  cexp_vars e = ∅ ∧
  cexp_consts_ok eqs e ∧
  ALL_DISTINCT (MAP FST eqs) ∧
  EVERY (λ(n,args,body).
    ALL_DISTINCT args ∧
    cexp_vars body ⊆ set args ∧
    cexp_consts_ok eqs body) eqs
  ⇒
  compute_eval ck eqs e s =
    let (r,s1) = exec (build_funs eqs) [] ck (to_ce eqs [] e) s in
      (from_res from_cv r, s1)
Proof
  Cases_on ‘compute_eval ck eqs e s’ \\ fs []
  \\ pairarg_tac \\ gvs [] \\ strip_tac
  \\ ‘eqs_ok eqs’ by
   (fs [eqs_ok_def,EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ res_tac \\ fs [compile_to_ce_def]
    \\ irule code_rel_to_ce \\ fs []
    \\ fs [eqs_ok_def,EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ res_tac)
  \\ drule exec_lemma
  \\ impl_tac \\ rpt strip_tac \\ fs []
  \\ irule code_rel_to_ce  \\ fs []
  \\ gvs [EVERY_MEM,FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs []
QED

val _ = export_theory ();
