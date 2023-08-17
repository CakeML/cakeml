(**
  Implementation and correctness proof of the global constant lifting
  (Section 7.2)
**)
open semanticPrimitivesTheory evaluateTheory
     icing_rewriterTheory icing_optimisationsTheory
     icing_optimisationProofsTheory fpOptTheory fpValTreeTheory
     namespacePropsTheory ml_progTheory
     optPlannerTheory source_to_source2Theory source_to_source2ProofsTheory;

open preamble;

val _ = new_theory "pull_words";

Triviality exp_size_lemma:
  (∀f n e l. MEM (f,n,e) l ⇒ exp_size e ≤ exp1_size l) ∧
  (∀n e l. MEM (n,e) l ⇒ exp_size e ≤ exp3_size l) ∧
  (∀e l. MEM e l ⇒ exp_size e ≤ exp6_size l)
Proof
  rpt conj_tac \\ Induct_on ‘l’ \\ fs []
  \\ rw [] \\ gvs [astTheory.exp_size_def] \\ res_tac \\ gvs []
  \\ first_x_assum drule \\ fs []
QED

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
  WF_REL_TAC ‘measure (λ e. exp_size e)’
  \\ rw [astTheory.exp_size_def]
  \\ imp_res_tac exp_size_lemma \\ gvs []
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
    (FLAT (MAP (λ (p,e). pat_bindings p [] ++
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
    FLAT ((MAP (λ (p,e). pat_bindings p [] ++
                         gather_used_identifiers_exp e) pes)) ∧
  gather_used_identifiers_exp (Let so e1 e2) =
    (let expression_identifiers =
         (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) in
       case so of
       | NONE => expression_identifiers
       | SOME n => n::expression_identifiers) ∧
  gather_used_identifiers_exp (Letrec ses e) =
    FLAT (MAP (λ (n, p, e). n :: p :: gather_used_identifiers_exp e) ses) ++
    (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Tannot e t) =
    (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Lannot e l) =
    (gather_used_identifiers_exp e)
Termination
  WF_REL_TAC ‘measure (λ e. exp_size e)’
  \\ rw [astTheory.exp_size_def]
  \\ imp_res_tac exp_size_lemma \\ gvs []
End

Definition gather_constants_decl_def:
  gather_constants_decl [Dlet loc p e] =
    gather_constants_exp e ∧
  gather_constants_decl (d1::d2::ds) =
    gather_constants_decl [d1] ++ gather_constants_decl (d2::ds) ∧
  gather_constants_decl _ = []
End

(**
  Walk over an AST and replace constants by variables that globally allocate
  their value
**)
Definition replace_constants_exp_def:
  replace_constants_exp al (Lit (Word64 w)) =
    (case (ALOOKUP al w) of
    | NONE => Lit (Word64 w)
    | SOME v => (Var (Short v))) ∧
  replace_constants_exp al (FpOptimise sc e) =
    FpOptimise sc (replace_constants_exp al e) ∧
  replace_constants_exp al (Lit l) = (Lit l) ∧
  replace_constants_exp al (Var x) = (Var x) ∧
  replace_constants_exp al (Raise e) = Raise (replace_constants_exp al e) ∧
  replace_constants_exp al (Handle e pes) =
    Handle (replace_constants_exp al e)
           (MAP (λ (p,e). (p, replace_constants_exp al e)) pes) ∧
  replace_constants_exp al (Con mod exps) =
    Con mod (MAP (replace_constants_exp al) exps) ∧
  replace_constants_exp al (Fun s e) = Fun s (replace_constants_exp al e) ∧
  replace_constants_exp al (App op exps) =
    App op (MAP (replace_constants_exp al) exps) ∧
  replace_constants_exp al (Log lop e2 e3) =
    Log lop (replace_constants_exp al e2) (replace_constants_exp al e3) ∧
  replace_constants_exp al (If e1 e2 e3) =
    If (replace_constants_exp al e1) (replace_constants_exp al e2) (replace_constants_exp al e3) ∧
  replace_constants_exp al (Mat e pes) =
    Mat (replace_constants_exp al e) ((MAP (λ (p,e). (p, replace_constants_exp al e)) pes)) ∧
  replace_constants_exp al (Let so e1 e2) =
    Let so (replace_constants_exp al e1) (replace_constants_exp al e2) ∧
  replace_constants_exp al (Letrec ses e) =
    Letrec (MAP (λ(f,n,e). (f,n,replace_constants_exp al e)) ses)
      (replace_constants_exp al e) ∧
  replace_constants_exp al (Tannot e t) =
    Tannot (replace_constants_exp al e) t ∧
  replace_constants_exp al (Lannot e l) =
    Lannot (replace_constants_exp al e) l
Termination
  WF_REL_TAC ‘measure (λ (al, e). exp_size e)’
  \\ rw [astTheory.exp_size_def]
  \\ imp_res_tac exp_size_lemma \\ gvs []
End

Definition build_cnst_list_def:
  build_cnst_list [] vars n = [] ∧
  build_cnst_list (w1::ws) vars n =
  let newName = STRCAT ("GLOB_CONST") (toString n) in
    if (MEM newName vars)
    then build_cnst_list ws vars (SUC n)
    else (w1, newName)::build_cnst_list ws (newName::vars) (SUC n)
End

Definition build_decl_list_def:
  build_decl_list [] = [] ∧
  build_decl_list ((w1,x)::ws) =
    (Dlet unknown_loc (Pvar x) (Lit (Word64 w1))) :: build_decl_list ws
End

Definition gather_constants_decl_def:
  gather_constants_decl [Dlet loc p e] =
    gather_constants_exp e ∧
  gather_constants_decl (d1::d2::ds) =
    (gather_constants_decl [d1] ++ gather_constants_decl (d2::ds)) ∧
  gather_constants_decl [d] = []
End

Definition gather_used_identifiers_decl_def:
  gather_used_identifiers_decl [Dlet loc p e] =
    (pat_bindings p [] ++ gather_used_identifiers_exp e) ∧
  gather_used_identifiers_decl (d1::d2::ds) =
    (gather_used_identifiers_decl [d1] ++ gather_used_identifiers_decl (d2::ds)) ∧
  gather_used_identifiers_decl [Dlocal lds ds] =
    gather_used_identifiers_decl lds ++ gather_used_identifiers_decl ds ∧
  gather_used_identifiers_decl [Dletrec locs funs] =
    FLAT (MAP (λ (n,m,e). n :: m :: gather_used_identifiers_exp e) funs) ∧
  gather_used_identifiers_decl [Dmod mn ds] =
    gather_used_identifiers_decl ds ∧
  gather_used_identifiers_decl [d] = []
Termination
  wf_rel_tac ‘measure dec1_size’
End

Definition replace_constants_decl_def:
  replace_constants_decl [Dlet loc p e] ws =
    [Dlet loc p (replace_constants_exp ws e)] ∧
  replace_constants_decl (d1::d2::ds) ws =
    replace_constants_decl [d1] ws ++ replace_constants_decl (d2::ds) ws ∧
  replace_constants_decl [Dletrec locs funs] ws =
    [Dletrec locs (MAP (I ## I ## replace_constants_exp ws) funs)] ∧
  replace_constants_decl [Dmod mn ds] ws =
    [Dmod mn (replace_constants_decl ds ws)] ∧
  replace_constants_decl [Dlocal lds ds] ws =
    [Dlocal (replace_constants_decl lds ws) (replace_constants_decl ds ws)] ∧
  replace_constants_decl [d] ws = [d] ∧
  replace_constants_decl [] ws = []
Termination
  wf_rel_tac ‘measure (λ (ds, w). dec1_size ds)’
End

Definition lift_constants_decl_def:
  lift_constants_decl ds =
  let cnsts = gather_constants_decl ds;
      vars = gather_used_identifiers_decl ds;
      cnst_lst = build_cnst_list cnsts vars 0;
  in
    (build_decl_list cnst_lst) ++ (replace_constants_decl ds cnst_lst)
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
  (∀ env id. v_rel (Env env id) (Env env id))
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
   “v_rel (Env env id) w”,
   “v_rel (Conv s vs) w”,
   “v_rel (Vectorv vs) w”,
   “v_rel (Closure env v e) w”,
   “v_rel (Recclosure env funs v) w”,
   “v_rel w (Litv v)”,
   “v_rel w (Real r)”,
   “v_rel w (FP_WordTree r)”,
   “v_rel w (FP_BoolTree r)”,
   “v_rel w (Loc r)”,
   “v_rel w (Env env id)”,
   “v_rel w (Conv s vs)”,
   “v_rel w (Vectorv vs)”,
   “v_rel w (Closure env v e)”,
   “v_rel w (Recclosure env funs v)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases]) |> LIST_CONJ;

Theorem env_rel_def =
        v_rel_cases |> CONJUNCT2 |> SIMP_RULE std_ss []
                                 |> Q.SPECL [‘env1’, ‘env2’, ‘ws’]
                                 |> Q.GEN ‘ws’ |> Q.GEN ‘env2’ |> Q.GEN ‘env1’;

Definition res_rel_def[simp]:
  res_rel (Rval x) (Rval y) = LIST_REL v_rel x y ∧
  res_rel (Rerr (Rraise v)) (Rerr (Rraise w)) = v_rel v w ∧
  res_rel (Rerr (Rabort a)) (Rerr (Rabort b)) = (a = b) ∧
  res_rel _ _ = F
End

Definition res1_rel_def[simp]:
  res1_rel (Rval x) (Rval y) = v_rel x y ∧
  res1_rel (Rerr (Rraise v)) (Rerr (Rraise w)) = v_rel v w ∧
  res1_rel (Rerr (Rabort a)) (Rerr (Rabort b)) = (a = b) ∧
  res1_rel _ _ = F
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
    LIST_REL ref_rel s.refs t.refs
End

Inductive env_rel_strict:
    env2.c = env1.c ∧
     (∀ x v.
        nsLookup env2.v x = SOME v ⇒
        ((∃ v1. nsLookup env1.v x = SOME v1 ∧ v_rel v1 v) ∧
         (∀ m. x = Short m ⇒ ~ MEM m (MAP SND al)))) ∧
     (∀ x v.
        nsLookup env1.v x = SOME v ⇒
        ((∃ v2. nsLookup env2.v x = SOME v2 ∧ v_rel v v2) ∧
         (∀ m. x = Short m ⇒ ~ MEM m (MAP SND al)))) ∧
     (∀ x.
        nsLookup env2.v x = NONE ⇒
        nsLookup env1.v x = NONE) ∧
     (∀ x.
        nsLookup env1.v x = NONE ⇒
        nsLookup env1.v x = NONE) ∧
     (∀ (x:(string,string) id) p1 p2 (e3:(string,string,v) namespace).
        p1 ≠ [] ∧ id_to_mods x = p1 ++ p2 ⇒
        (nsLookupMod env1.v p1 = NONE ⇔ nsLookupMod env2.v p1 = NONE) ∧
        (∀ env.
           nsLookupMod env1.v p1 = SOME env ⇒
           ∃ env'. nsLookupMod env2.v p1 = SOME env' ∧
                   env_rel_strict <| v := env; c := nsEmpty |> <| v := env'; c := nsEmpty |> al) ∧
        (∀ env.
           nsLookupMod env2.v p1 = SOME env ⇒
           ∃ env'. nsLookupMod env1.v p1 = SOME env' ∧
                   env_rel_strict <| v := env'; c := nsEmpty |> <| v := env; c := nsEmpty |> al)) ⇒
    env_rel_strict env1 env2 al
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

Theorem list_rel_lookup_some_l:
  ∀ (xs:(string#v) list) ys x v1.
    LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ∧
    ALOOKUP xs x = SOME v1 ⇒
    ∃ v2.
      nsLookup (alist_to_ns ys) ((Short x):(string,string) id) = SOME v2 ∧
      v_rel v1 v2
Proof
  Induct_on ‘xs’ >> gs[]
  >> rpt strip_tac >> gs[] >> Cases_on ‘h’ >> gs[ALOOKUP_def]
  >> Cases_on ‘y’ >> gs[] >> rveq >> gs[ml_progTheory.nsLookup_nsBind_compute]
  >> Cases_on ‘q = x’ >> gs[]
QED

Theorem list_rel_lookup_some_r:
  ∀ (xs:(string#v) list) ys x v1.
    LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ∧
    ALOOKUP ys x = SOME v1 ⇒
    ∃ v2.
      nsLookup (alist_to_ns xs) ((Short x):(string,string) id) = SOME v2 ∧
      v_rel v2 v1
Proof
  Induct_on ‘ys’ >> gs[]
  >> rpt strip_tac >> gs[] >> Cases_on ‘h’ >> gs[ALOOKUP_def]
  >> Cases_on ‘x'’ >> gs[] >> rveq >> gs[ml_progTheory.nsLookup_nsBind_compute]
  >> Cases_on ‘q = x’ >> gs[]
QED

Theorem list_rel_lookup_none_r:
  ∀ xs ys x v1.
    LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ∧
    nsLookup ((alist_to_ns ys):(string,string,v) namespace) x = NONE ⇒
    nsLookup (alist_to_ns xs) x = NONE
Proof
  Induct_on ‘ys’ >> gs[]
  >> rpt strip_tac >> gs[] >> Cases_on ‘h’ >> gs[ALOOKUP_def]
  >> Cases_on ‘x'’ >> gs[] >> rveq
  >> Cases_on ‘x’ >> gs[ml_progTheory.nsLookup_nsBind_compute]
  >> Cases_on ‘q = n’ >> gs[]
QED

Theorem list_rel_lookup_none_l:
  ∀ xs ys x v1.
    LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ∧
    nsLookup ((alist_to_ns xs):(string,string,v) namespace) x = NONE ⇒
    nsLookup (alist_to_ns ys) x = NONE
Proof
  Induct_on ‘xs’ >> gs[]
  >> rpt strip_tac >> gs[] >> Cases_on ‘h’ >> gs[ALOOKUP_def]
  >> Cases_on ‘y’ >> gs[] >> rveq
  >> Cases_on ‘x’ >> gs[ml_progTheory.nsLookup_nsBind_compute]
  >> Cases_on ‘q = n’ >> gs[]
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

Theorem env_rel_strict_update_lemma:
  env_rel_strict (env with v := t) (env' with v := t') al ∧
  ¬MEM n (MAP SND al) ∧ v_rel x y ⇒
  env_rel_strict (env with v := nsBind n x t)
                 (env' with v := nsBind n y t') al
Proof
  simp [Once env_rel_strict_cases] >> rpt strip_tac
  >> simp[Once env_rel_strict_cases] >> rpt strip_tac
  >- (
    Cases_on ‘x'’ >> gs[nsLookup_nsBind_compute]
    >> IF_CASES_TAC >> gs[])
  >- (
    Cases_on ‘x'’ >> gs[nsLookup_nsBind_compute]
    >> Cases_on ‘n = m’ >> gs[])
  >- (
    Cases_on ‘x'’ >> gs[nsLookup_nsBind_compute]
    >> IF_CASES_TAC >> gs[])
  >- (
    Cases_on ‘x'’ >> gs[nsLookup_nsBind_compute]
    >> Cases_on ‘n = m’ >> gs[])
  >- (
    Cases_on ‘x'’ >> gs[nsLookup_nsBind_compute]
    >> IF_CASES_TAC >> gs[])
  >> Cases_on ‘t’ >> Cases_on ‘t'’ >> gs[namespaceTheory.nsBind_def, namespaceTheory.nsLookupMod_def]
  >> first_x_assum $ qspecl_then [‘x'’, ‘p1’, ‘p2’] mp_tac
  >> Cases_on ‘p1’
  >> gs[namespaceTheory.nsLookupMod_def]
QED

Theorem env_rel_strict_update:
  env_rel_strict env env' al ∧ ¬MEM n (MAP SND al) ∧ v_rel x y ⇒
  env_rel_strict (env with v := nsBind n x env.v)
                 (env' with v := nsBind n y env'.v) al
Proof
  rw [] \\ irule env_rel_strict_update_lemma \\ gvs []
QED

Theorem env_rel_nsAppend:
  env_rel env1 env2 al ∧
  env_rel_strict env3 env4 al ⇒
  env_rel (extend_dec_env env3 env1) (extend_dec_env env4 env2) al
Proof
  rpt strip_tac >> gs[env_rel_def, Once env_rel_strict_cases,extend_dec_env_def]
  >> rpt conj_tac
  >- (
    rpt strip_tac >> reverse $ Cases_on ‘n’ >> gs[nsLookup_nsAppend_some]
    >- (
      res_tac
      >> Cases_on ‘nsLookup env3.v (Long m i)’ >> gs[]
      >> ‘nsLookup (nsAppend env3.v env1.v) (Long m i) = SOME x’
         by (gs[nsLookup_nsAppend_some])
      >> gs[])
    >- (
      rpt strip_tac >> res_tac
      >> Cases_on ‘nsLookup env1.v (Long m i)’ >> gs[]
      >> gs[nsLookup_nsAppend_none]
      >> Cases_on ‘nsLookup env3.v (Long m i)’ >> gs[]
      >> ‘nsLookupMod env4.v p1 = SOME e3’
         by (res_tac >> gs[])
      >> gs[])
    >- (res_tac >> CCONTR_TAC >> gs[nsLookup_nsAppend_none])
    >> Cases_on ‘nsLookup env1.v (Short n')’ >> gs[]
    >- (
      ‘nsLookup (nsAppend env3.v env1.v) (Short n') = NONE’
      by gs[nsLookup_nsAppend_none]
      >> gs[]
      >> res_tac >> pop_assum $ mp_tac
      >> qpat_x_assum `nsLookup env1.v _ = _` $ rewrite_tac o single
      >> gs[])
    >> ‘nsLookup (nsAppend env3.v env1.v) (Short n') = SOME x’
       by gs[nsLookup_nsAppend_some, namespaceTheory.id_to_mods_def]
    >> gs[] >> res_tac
    >> qpat_x_assum `if _ then _ else _` mp_tac
    >> qpat_x_assum `nsLookup env1.v _ = _` $ rewrite_tac o single
    >> gs[])
  >- (
    rpt strip_tac
    >> ‘nsLookup env4.v (Short n) = NONE’
       by (CCONTR_TAC >> gs[] >> Cases_on ‘nsLookup env4.v (Short n)’
           >> gs[] >> res_tac >> gs[MEM_MAP])
    >> res_tac >> gs[nsLookup_nsAppend_some, namespaceTheory.id_to_mods_def])
  >> rpt strip_tac >> gs[nsLookup_nsAppend_some]
  >- (res_tac >> asm_exists_tac >> gs[])
  >> res_tac
  >> ‘nsLookup env4.v n = NONE’
    by (CCONTR_TAC >> gs[] >> Cases_on ‘nsLookup env4.v n’
        >> gs[] >> res_tac >> gs[MEM_MAP])
  >> gs[]
  >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.id_to_mods_def]
  >> CCONTR_TAC
  >> Cases_on ‘nsLookupMod env4.v p1’ >> gs[]
  >> first_x_assum $ qspecl_then [‘p1’, ‘p2’] mp_tac >> impl_tac >- gs[]
  >> rpt strip_tac
  >> first_x_assum $ qspecl_then [‘Long m i’, ‘p1’, ‘p2’] mp_tac
  >> impl_tac >- gs[namespaceTheory.id_to_mods_def]
  >> rpt strip_tac
  >> res_tac >> gs[]
QED

fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

Theorem id_to_mods_defined:
∀ ps. ∃ (id:(string,string) id).
        id_to_mods id = ps
Proof
  Induct_on ‘ps’
  >- (qexists_tac ‘Short "x"’ >> gs[namespaceTheory.id_to_mods_def])
  >> rpt strip_tac >> gs[]
  >> qexists_tac ‘Long h id’ >> gs[namespaceTheory.id_to_mods_def]
QED

(*
Theorem env_rel_strict_nsAppend:
  env_rel_strict env1 env2 al ∧
  env_rel_strict env3 env4 al ⇒
  env_rel_strict (extend_dec_env env3 env1) (extend_dec_env env4 env2) al
Proof
  rpt strip_tac >> gs[env_rel_def, Once env_rel_strict_cases,extend_dec_env_def]
  >> last_x_assum $ strip_assume_tac o SIMP_RULE std_ss [Once env_rel_strict_cases]
  >> simp[Once env_rel_strict_cases]
  >> rpt conj_tac
  >- (
    rpt strip_tac >> reverse $ Cases_on ‘x’ >> gs[nsLookup_nsAppend_some]
    >- (res_tac >> qexists_tac ‘v1’ >> gs[])
    >- (
      res_tac >> asm_exists_tac >> gs[]
      >> rpt strip_tac >> CCONTR_TAC >> gs[]
      >> Cases_on ‘nsLookupMod env3.v p1’ >> gs[]
      >> res_tac
      >> ‘nsLookupMod env4.v p1 = SOME x’ by gs[]
      >> gs[])
    >- (res_tac >> CCONTR_TAC >> gs[nsLookup_nsAppend_none])
    >> res_tac >> asm_exists_tac >> gs[namespaceTheory.id_to_mods_def])
  >- (
    rpt strip_tac >> reverse $ Cases_on ‘x’ >> gs[nsLookup_nsAppend_some]
    >- (res_tac >> qexists_tac ‘v2’ >> gs[])
    >- (
      res_tac
      >> ‘nsLookup env4.v (Long m i) = NONE’
         by (Cases_on ‘nsLookup env4.v (Long m i)’ >> gs[]
             >> res_tac >> gs[])
      >> qexists_tac ‘v2’ >> gs[]
      >> rpt strip_tac >> CCONTR_TAC >> gs[]
      >> Cases_on ‘nsLookupMod env4.v p1’ >> gs[]
      >> res_tac
      >> ‘nsLookupMod env3.v p1 = SOME x’ by gs[]
      >> gs[])
    >- (res_tac >> CCONTR_TAC >> gs[nsLookup_nsAppend_none])
    >> res_tac
    >> ‘nsLookup env4.v (Short n) = NONE’
      by (Cases_on ‘nsLookup env4.v (Short n)’ >> gs[]
          >> res_tac >> gs[])
    >> qexists_tac ‘v2’ >> gs[namespaceTheory.id_to_mods_def])
  >- (
    rpt strip_tac >> gs[nsLookup_nsAppend_none]
    >> Cases_on ‘nsLookup env1.v x = NONE’ >> gs[]
    >> res_tac >> asm_exists_tac >> gs[])
  >> rpt strip_tac
  >> first_x_assum $ (fn th => mp_tac th >> qspecl_then [‘x’, ‘p1’, ‘p2’] mp_tac th)
  >> impl_tac >- gs[]
  >> first_x_assum $ (fn th => mp_tac th >> qspecl_then [‘x’, ‘p1’, ‘p2’] mp_tac th)
  >> impl_tac >- gs[]
  >> rpt strip_tac >> gs[nsLookupMod_nsAppend_some]
  >- (
    EQ_TAC >> gs[nsLookupMod_nsAppend_none]
    >> rpt strip_tac >> gs[]
    >- (
      DISJ2_TAC >> rpt strip_tac
      >> qspec_then ‘p1'++ p2'’ strip_assume_tac id_to_mods_defined
      >> MAP_EVERY qexists_tac [‘p1'’, ‘p2'’]
      >> last_x_assum $ qspecl_then [‘id’, ‘p1'’, ‘p2'’] mp_tac
      >> gs[] >> rpt strip_tac >> gs[])
    >> DISJ2_TAC >> rpt strip_tac
    >> qspec_then ‘p1'++ p2'’ strip_assume_tac id_to_mods_defined
    >> MAP_EVERY qexists_tac [‘p1'’, ‘p2'’]
    >> last_x_assum $ qspecl_then [‘id’, ‘p1'’, ‘p2'’] mp_tac
    >> gs[] >> rpt strip_tac >> gs[])
  >- (qexists_tac ‘env'’ >> gs[])
  >- (
    rpt strip_tac
    >> qspec_then ‘p1'++ p2'’ strip_assume_tac id_to_mods_defined
    >> CCONTR_TAC >> gs[]
    >> Cases_on ‘nsLookupMod env4.v p1'’ >> gs[]
    >> first_x_assum $ qspecl_then [‘p1'’, ‘p2'’] mp_tac
    >> impl_tac >- gs[]
    >> strip_tac
    >> last_x_assum $ qspecl_then [‘id’, ‘p1'’, ‘p2'’] mp_tac
    >> impl_tac >- gs[]
    >> strip_tac >> gs[])
  >- (qexists_tac ‘env'’ >> gs[])
  >> rpt strip_tac
  >> qspec_then ‘p1'++ p2'’ strip_assume_tac id_to_mods_defined
  >> CCONTR_TAC >> gs[]
  >> Cases_on ‘nsLookupMod env3.v p1'’ >> gs[]
  >> first_x_assum $ qspecl_then [‘p1'’, ‘p2'’] mp_tac
  >> impl_tac >- gs[]
  >> strip_tac
  >> last_x_assum $ qspecl_then [‘id’, ‘p1'’, ‘p2'’] mp_tac
  >> impl_tac >- gs[]
  >> strip_tac >> gs[]
QED
*)

Theorem env_rel_build_rec_env_decl:
  env_rel env1 env2 al ∧
  DISJOINT (set (FLAT (MAP (λ(n,m,e). n::m::gather_used_identifiers_exp e) funs)))
           (set (MAP SND al)) ⇒
    env_rel_strict <| v := (build_rec_env funs env1 nsEmpty); c := nsEmpty |>
                   <| v := (build_rec_env (MAP (I ## I ## replace_constants_exp al) funs) env2 nsEmpty);
                      c := nsEmpty |> al
Proof
  fs [build_rec_env_def]
  \\ qabbrev_tac ‘ff = Recclosure env1 funs’
  \\ qabbrev_tac ‘gg = Recclosure env2
                         (MAP (I ## I ## replace_constants_exp al) funs)’
  \\ disch_then (fn th => assume_tac th \\ mp_tac th)
  \\ qid_spec_tac ‘funs’ \\ Induct
  >- (
    gs[Once env_rel_strict_cases]
    \\ rpt strip_tac \\ Cases_on ‘p1’ \\ gs[])
  \\ fs [FORALL_PROD] \\ rw []
  \\ irule env_rel_strict_update_lemma \\ gvs[]
  \\ unabbrev_all_tac \\ gvs [PULL_EXISTS]
  \\ qexists_tac ‘al’ \\ gs[]
QED

Theorem env_rel_strict_empty:
  env_rel_strict env1 env2 al ⇒
  env_rel_strict <| v := env1.v; c := nsEmpty |>
                 <| v := env2.v; c := nsEmpty |> al
Proof
  rw[Once env_rel_strict_cases] >> simp[Once env_rel_strict_cases]
  >> rpt conj_tac >> TRY (first_x_assum $ MATCH_ACCEPT_TAC)
  >> rpt strip_tac >> res_tac >> gs[]
QED

Theorem env_rel_nsLift:
  ∀ env1 env2 mn.
    env_rel_strict env1 env2 al ⇒
    env_rel_strict <| v := nsLift mn env1.v; c := nsLift mn env1.c |>
                   <| v := nsLift mn env2.v; c := nsLift mn env2.c |> al
Proof
  rpt gen_tac
  >> disch_then (fn th => assume_tac th >> assume_tac (SIMP_RULE std_ss [Once env_rel_strict_cases] th))
  >> simp[Once env_rel_strict_cases] >> rpt strip_tac >> gs[]
  >- (Cases_on ‘x’ >> gs[nsLookup_nsLift])
  >- gs[nsLookup_nsLift]
  >- (Cases_on ‘x’ >> gs[nsLookup_nsLift])
  >- gs[nsLookup_nsLift]
  >- (Cases_on ‘x’ >> gs[nsLookup_nsLift])
  >- (
    Cases_on ‘x’ >> gs[namespaceTheory.id_to_mods_def, nsLookupMod_nsLift]
    >> TOP_CASE_TAC >> gs[]
    >> Cases_on ‘mn = h’ >> gs[]
    >> Cases_on ‘t’ >> gs[namespaceTheory.nsLookupMod_def]
    >> first_x_assum $ qspecl_then [‘i’, ‘h'::t'’, ‘p2’] mp_tac
    >> impl_tac >> gs[])
  >- (
    Cases_on ‘x’ >> gs[namespaceTheory.id_to_mods_def, nsLookupMod_nsLift]
    >> TOP_CASE_TAC >> gs[] >> rveq
    >> Cases_on ‘t’ >> gs[namespaceTheory.nsLookupMod_def]
    >- (rveq >> irule env_rel_strict_empty >> gs[])
    >> first_x_assum $ qspecl_then [‘i’, ‘h::t'’, ‘p2’] mp_tac
    >> impl_tac >> gs[])
  >> Cases_on ‘x’ >> gs[namespaceTheory.id_to_mods_def, nsLookupMod_nsLift]
  >> TOP_CASE_TAC >> gs[] >> rveq
  >> Cases_on ‘t’ >> gs[namespaceTheory.nsLookupMod_def]
  >- (rveq >> irule env_rel_strict_empty >> gs[])
  >> first_x_assum $ qspecl_then [‘i’, ‘h::t'’, ‘p2’] mp_tac
  >> impl_tac >> gs[]
QED

Theorem env_rel_update_alist:
  env_rel env env' al ∧ DISJOINT (set (MAP FST xs)) (set (MAP SND al)) ∧
  LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ⇒
  env_rel <| v := nsAppend ((alist_to_ns xs):(string,string,v) namespace) env.v; c := env.c |>
          <| v := nsAppend ((alist_to_ns ys):(string,string,v) namespace) env'.v; c := env.c |> al
Proof
  Induct_on ‘xs’ >> simp[env_rel_def]
  >> rpt strip_tac
  >- (
    gs[namespacePropsTheory.nsLookup_nsAppend_some,
       namespacePropsTheory.nsLookup_alist_to_ns_some,
       ml_progTheory.nsLookup_nsAppend_Short]
    >- (
      rveq >> imp_res_tac list_rel_lookup_some_r
      >> first_x_assum $ qspec_then ‘h::xs’ mp_tac >> gs[]
      >> rpt strip_tac >> gs[]
      >> gs[IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD,
            namespacePropsTheory.nsLookup_alist_to_ns_some]
      >> rpt strip_tac >> imp_res_tac ALOOKUP_MEM
      >> ntac 2 $ first_x_assum $ qspec_then ‘x'’ assume_tac
      >> gs[] >> rveq >> gs[])
    >> imp_res_tac list_rel_lookup_none_r
    >> first_x_assum $ qspec_then ‘h::xs’ mp_tac
    >> gs[namespacePropsTheory.nsLookup_nsAppend_none] >> strip_tac
    >> Cases_on ‘nsLookup env.v n’ >> gs[]
    >- (first_x_assum drule >> gs[])
    >> Cases_on ‘n’ >> gs[namespaceTheory.id_to_mods_def]
    >- (last_x_assum drule >> gs[])
    >> rpt strip_tac
    >> Cases_on ‘p1’ >> gs[nsLookupMod_alist_to_ns])
  >- (
    rveq >> gs[ml_progTheory.nsLookup_nsAppend_Short]
    >> TOP_CASE_TAC >> gs[namespacePropsTheory.nsLookup_alist_to_ns_some]
    >> imp_res_tac list_rel_lookup_some_r
    >> first_x_assum $ qspec_then ‘h :: xs’ mp_tac
    >> gs[] >> rpt strip_tac
    >> gs[namespacePropsTheory.nsLookup_alist_to_ns_some]
    >> imp_res_tac ALOOKUP_MEM
    >> gs[IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD] >> rveq
    >- gs[]
    >- gs[]
    >- metis_tac[]
    >> metis_tac[])
  >> gs[namespacePropsTheory.nsLookup_nsAppend_some,
        namespacePropsTheory.nsLookup_alist_to_ns_some]
  >- (
    imp_res_tac list_rel_lookup_some_l
    >> first_x_assum $ qspec_then ‘y :: ys'’ mp_tac
    >> gs[] >> rpt strip_tac
    >> gs[namespacePropsTheory.nsLookup_alist_to_ns_some]
    >> asm_exists_tac >> gs[])
  >> imp_res_tac list_rel_lookup_none_l
  >> first_x_assum $ qspec_then ‘y :: ys'’ mp_tac
  >> gs[] >> rpt strip_tac
  >> res_tac
  >> asm_exists_tac >> gs[]
  >> DISJ2_TAC >> rpt strip_tac
  >> Cases_on ‘p1’ >> gs[nsLookupMod_alist_to_ns]
QED

Theorem env_rel_strict_update_alist:
  ∀ xs ys al.
    DISJOINT (set (MAP FST xs)) (set (MAP SND al)) ∧
    LIST_REL (λ (s1, x1) (s2, x2). s1 = s2 ∧ v_rel x1 x2) xs ys ⇒
    env_rel_strict <| v := (alist_to_ns xs):(string,string,v) namespace ; c := nsEmpty |>
                   <| v := (alist_to_ns ys):(string,string,v) namespace ; c := nsEmpty |> al
Proof
  Induct_on ‘xs’ >> simp[Once env_rel_strict_cases]
  >> rpt strip_tac
  >- (Cases_on ‘p1’ >> gs[])
  >- (
    Cases_on ‘h’ >> Cases_on ‘y’ >> gs[] >> rveq
    >> Cases_on ‘x’ >> gs[nsLookup_nsBind_compute]
    >- (
      IF_CASES_TAC >> gs[]
      >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
      >> rpt strip_tac >> gs[])
    >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
    >> rpt strip_tac >> gs[])
  >- (
    Cases_on ‘h’ >> Cases_on ‘y’ >> gs[] >> rveq
    >> gs[nsLookup_nsBind_compute]
    >> Cases_on ‘q = m’ >> gs[]
    >> res_tac
    >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
    >> rpt strip_tac >> gs[])
  >- (
    Cases_on ‘h’ >> Cases_on ‘y’ >> gs[] >> rveq
    >> Cases_on ‘x’ >> gs[nsLookup_nsBind_compute]
    >- (
      IF_CASES_TAC >> gs[]
      >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
      >> rpt strip_tac >> gs[])
    >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
    >> rpt strip_tac >> gs[])
  >- (
    Cases_on ‘h’ >> Cases_on ‘y’ >> gs[] >> rveq
    >> gs[nsLookup_nsBind_compute]
    >> Cases_on ‘q = m’ >> gs[]
    >> res_tac
    >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
    >> rpt strip_tac >> gs[])
  >- (
    Cases_on ‘h’ >> Cases_on ‘y’ >> gs[] >> rveq
    >> Cases_on ‘x’ >> gs[nsLookup_nsBind_compute]
    >- (
      IF_CASES_TAC >> gs[]
      >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
      >> rpt strip_tac >> gs[])
    >> res_tac >> pop_assum $ mp_tac >> rewrite_tac [Once env_rel_strict_cases]
    >> rpt strip_tac >> gs[])
  >> Cases_on ‘p1’ >> gs[]
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

Definition match_rel_def[simp]:
  match_rel No_match No_match = T ∧
  match_rel Match_type_error Match_type_error = T ∧
  match_rel (Match e1) (Match e2) =
    LIST_REL (λ(s1,x1) (s2,x2). s1 = (s2:string) ∧ v_rel x1 x2) e1 e2 ∧
  match_rel _ _ = F
End

Theorem LIST_REL_SYM:
  ∀ xs.
  (∀ x. R x x) ⇒
  LIST_REL R xs xs
Proof
  Induct_on ‘xs’ >> gs[]
  >> rpt strip_tac >> res_tac >> gs[]
QED

local
  val pmatch_goal =
    “(λ envC refs1 p a env1.
       ∀ refs2 a' r1 r2 env2.
         LIST_REL ref_rel refs1 refs2 ∧
         v_rel a a' ∧
         match_rel (Match env1) (Match env2) ∧
         pmatch envC refs1 p a env1 = r1 ∧
         pmatch envC refs2 p a' env2 = r2 ⇒
         match_rel r1 r2)”
  val pmatch_list_goal =
    “(λ envC refs1 p as env1.
       ∀ refs2 as' r1 r2 env2.
         LIST_REL ref_rel refs1 refs2 ∧
         LIST_REL v_rel as as' ∧
         match_rel (Match env1) (Match env2) ∧
         pmatch_list envC refs1 p as env1 = r1 ∧
         pmatch_list envC refs2 p as' env2 = r2 ⇒
         match_rel r1 r2)”
in

Theorem pmatch_single_lemma:
  (∀ envC refs p a env.
     ^pmatch_goal envC refs p a env) ∧
  (∀ envC refs p as env.
     ^pmatch_list_goal envC refs p as env)
Proof
  qspecl_then [‘^pmatch_goal’, ‘^pmatch_list_goal’] irule pmatch_ind
  >> rw[] >> gs[pmatch_def, match_rel_def]
  >- (
    Cases_on ‘nsLookup envC n’ >> gs[match_rel_def]
    >> TOP_CASE_TAC >> gs[]
    >> ntac 2 (COND_CASES_TAC >> gs[match_rel_def])
    >> ‘LENGTH vs = LENGTH vs1’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> COND_CASES_TAC >> gs[match_rel_def]
    >> first_x_assum irule >> gs[]
    >> qexists_tac ‘st'’ >>  gs[])
  >- (
    ‘LENGTH vs = LENGTH vs1’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> COND_CASES_TAC >> gs[match_rel_def]
    >> first_x_assum irule >> gs[]
    >> qexists_tac ‘st'’ >>  gs[])
  >- (ntac 2 (COND_CASES_TAC >> gs[match_rel_def]))
  >- (
    reverse (TOP_CASE_TAC >> gs[])
    >- (
      ‘match_rel (Match a) (pmatch envC refs2 p y env2)’
      by (first_x_assum irule >> gs[])
      >> Cases_on ‘pmatch envC refs2 p y env2’ >> gs[match_rel_def])
    >- (
      ‘match_rel (Match_type_error) (pmatch envC refs2 p y env2)’
      by (first_x_assum irule >> gs[])
      >> Cases_on ‘pmatch envC refs2 p y env2’ >> gs[match_rel_def])
    >> ‘match_rel (No_match) (pmatch envC refs2 p y env2)’
      by (first_x_assum irule >> gs[])
      >> Cases_on ‘pmatch envC refs2 p y env2’ >> gs[match_rel_def]
    >> reverse (TOP_CASE_TAC >> gs[])
    >- (
      ‘match_rel (Match a) (pmatch_list envC refs2 ps ys env2)’
       by (first_x_assum irule >> gs[])
      >> Cases_on ‘pmatch_list envC refs2 ps ys env2’ >> gs[match_rel_def])
    >- (
      ‘match_rel (Match_type_error) (pmatch_list envC refs2 ps ys env2)’
       by (first_x_assum irule >> gs[])
      >> Cases_on ‘pmatch_list envC refs2 ps ys env2’ >> gs[match_rel_def])
    >> ‘match_rel (No_match) (pmatch_list envC refs2 ps ys env2)’
       by (first_x_assum irule >> gs[])
    >> Cases_on ‘pmatch_list envC refs2 ps ys env2’ >> gs[match_rel_def])
  >> ‘LENGTH s = LENGTH refs2’
    by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
  >> TOP_CASE_TAC >> gs[]
  >- (
    ‘store_lookup lnum refs2 = NONE’
     by (gs[state_rel_def, store_lookup_def])
    >> gs[])
  >> ‘∃ y. store_lookup lnum refs2 = SOME y ∧ ref_rel x y’
    by (
    gs[store_lookup_def, LIST_REL_EL_EQN]
    >> res_tac >> rveq >> gs[])
  >> gs[]
  >> ntac 2 TOP_CASE_TAC >> gs[ref_rel_def]
QED

Theorem pmatch_thm:
  (∀envc refs1 p v xs v1 ys refs2.
     LIST_REL ref_rel refs1 refs2 ∧
     v_rel v v1 ∧ match_rel (Match xs) (Match ys) ⇒
     match_rel (pmatch envc refs1 p v xs)
               (pmatch envc refs2 p v1 ys)) ∧
  (∀envc refs1 ps vs xs vs1 ys refs2.
     LIST_REL ref_rel refs1 refs2 ∧
     LIST_REL v_rel vs vs1 ∧ match_rel (Match xs) (Match ys) ⇒
     match_rel (pmatch_list envc refs1 ps vs xs)
               (pmatch_list envc refs2 ps vs1 ys))
Proof
  rpt strip_tac
  >- (drule $ CONJUNCT1 $ SIMP_RULE std_ss [] pmatch_single_lemma
      >> gs[])
  >> drule $ CONJUNCT2 $ SIMP_RULE std_ss [] pmatch_single_lemma
  >> gs[]
QED
end

Theorem can_pmatch_all_lemma:
  state_rel st' t1 ∧ v_rel a a' ⇒
  can_pmatch_all env.c st'.refs (MAP FST pes) a =
  can_pmatch_all env.c t1.refs (MAP FST pes) a'
Proof
  Induct_on ‘pes’
  >- gs[can_pmatch_all_def]
  >> rpt strip_tac
  >> gs[can_pmatch_all_def]
  >> EQ_TAC >> rpt strip_tac >> gs[state_rel_def]
  >> ‘match_rel (Match []) (Match [])’ by (gs[match_rel_def])
  >> imp_res_tac pmatch_thm
  >- (
  last_x_assum $ qspecl_then [‘FST h’, ‘env.c’] mp_tac >> gs[]
  >> Cases_on ‘pmatch env.c st'.refs (FST h) a []’ >> gs[match_rel_def])
  >> last_x_assum $ qspecl_then [‘FST h’, ‘env.c’] mp_tac >> gs[]
  >> Cases_on ‘pmatch env.c t1.refs (FST h) a' []’ >> gs[match_rel_def]
QED

Theorem v_rel_do_fpoptimise:
  ∀annot xs ys.
    LIST_REL v_rel xs ys ⇒
    LIST_REL v_rel (do_fpoptimise annot xs) (do_fpoptimise annot ys)
Proof
  ho_match_mp_tac do_fpoptimise_ind \\ rpt strip_tac
  \\ gvs [do_fpoptimise_def]
  \\ TRY (first_assum $ irule_at (Pos last) \\ fs [])
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule_all
  \\ first_x_assum drule_all
  \\ metis_tac [LIST_REL_APPEND]
QED

Theorem pmatch_pat_bindings_general:
  (∀ envc refs p v env a.
     pmatch envc refs p v env = Match a ⇒
      set (MAP FST a) SUBSET (set (pat_bindings p []) UNION set (MAP FST env))) ∧
  (∀ envc refs ps vs env a.
     pmatch_list envc refs ps vs env = Match a ⇒
     set (MAP FST a) SUBSET (set (pats_bindings ps []) UNION set (MAP FST env)))
Proof
  qspecl_then [‘λ envc refs p v env.
                 ∀ a.
                 pmatch envc refs p v env = Match a ⇒
                 set (MAP FST a) SUBSET (set (pat_bindings p []) UNION set (MAP FST env))’,
               ‘λ envc refs ps vs env.
                 ∀ a.
                 pmatch_list envc refs ps vs env = Match a ⇒
                 set (MAP FST a) SUBSET (set (pats_bindings ps []) UNION set (MAP FST env))’]
              mp_tac pmatch_ind
  >> reverse impl_tac
  >- (gs[] >> rpt strip_tac)
  >> rw[] >> gs[pmatch_def] >> rveq
  >- (gs[astTheory.pat_bindings_def])
  >- (
    qpat_x_assum `_ = Match _` mp_tac
    >> rpt (TOP_CASE_TAC >> gs[]))
  >- (
    qpat_x_assum `_ = Match _` mp_tac
    >> rpt (TOP_CASE_TAC >> gs[])
    >> strip_tac >> res_tac
    >> gs[astTheory.pat_bindings_def])
  >- (
    qpat_x_assum `_ = Match _` mp_tac
    >> rpt (TOP_CASE_TAC >> gs[])
    >> strip_tac >> res_tac
    >> gs[astTheory.pat_bindings_def])
  >- (
    qpat_x_assum `_ = Match _` mp_tac
    >> rpt (TOP_CASE_TAC >> gs[])
    >> strip_tac >> res_tac
    >> gs[astTheory.pat_bindings_def])
  >> qpat_x_assum `_ = Match _` mp_tac
  >> rpt (TOP_CASE_TAC >> gs[])
  >> strip_tac >> res_tac
  >> gs[astTheory.pat_bindings_def]
  >> gs[SUBSET_DEF] >> rpt strip_tac
  >> res_tac >> gs[]
  >> TRY (simp[Once semanticPrimitivesPropsTheory.pat_bindings_accum])
  >> last_x_assum $ qspec_then ‘x’ mp_tac
  >> impl_tac
  >> rpt strip_tac >> gs[]
  >> simp[Once semanticPrimitivesPropsTheory.pat_bindings_accum]
QED

Theorem pmatch_pat_bindings:
  pmatch envc refs p v [] = Match a ⇒
  set (MAP FST a) SUBSET set (pat_bindings p [])
Proof
  rpt strip_tac
  >> drule $ CONJUNCT1 pmatch_pat_bindings_general
  >> gs[]
QED

Theorem v_rel_Boolv_id:
  ∀b. v_rel (Boolv b) (Boolv b)
Proof
  Cases \\ fs [Boolv_def]
QED

Theorem res1_rel_Rerr[simp]:
  res1_rel (Rerr e) (Rerr e') = res_rel (Rerr e) (Rerr e')
Proof
  Cases_on ‘e’ \\ Cases_on ‘e'’ \\ fs []
QED

Theorem v_rel_Boolv:
  v_rel v' v ⇒ (v' = Boolv b ⇔ v = Boolv b)
Proof
  Cases_on ‘b’ \\ Cases_on ‘v'’ \\ Cases_on ‘v’ \\ fs [Boolv_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
QED

Theorem v_rel_fp_translate:
  v_rel v1 v2 ⇒
  fp_translate v1 = fp_translate v2
Proof
  Cases_on ‘v1’ >> Cases_on ‘v2’ >> gs[Once v_rel_cases, fp_translate_def]
QED

Theorem v_rel_v_to_char_list:
  ∀ v1 v2.
    v_rel v1 v2 ⇒
    v_to_char_list v1 = v_to_char_list v2
Proof
  recInduct v_to_char_list_ind >> rpt strip_tac >> gs[v_to_char_list_def]
  >> ntac 2 $ TOP_CASE_TAC >> gs[]
  >> res_tac >> pop_assum $ gs o single o GSYM
QED

Theorem v_rel_list_to_v_char:
  v_rel (list_to_v (MAP (λc. Litv (Char c)) (EXPLODE s)))
    (list_to_v (MAP (λc. Litv (Char c)) (EXPLODE s)))
Proof
  Induct_on ‘s’ >> gs[list_to_v_def]
QED

Theorem v_rel_v_to_list:
  ∀ v1 v2.
    v_rel v1 v2 ⇒
    OPTREL (LIST_REL v_rel) (v_to_list v1) (v_to_list v2)
Proof
  recInduct v_to_list_ind >> rpt strip_tac >> gs[v_to_list_def, OPTREL_def]
  >> Cases_on ‘stamp = TypeStamp "::" list_type_num’ >> gs[]
  >> TOP_CASE_TAC >> gs[]
  >> res_tac >> pop_assum $ gs o single o GSYM
QED

Theorem v_rel_vs_to_string:
  ∀ vs1 vs2.
    LIST_REL v_rel vs1 vs2 ⇒ vs_to_string vs1 = vs_to_string vs2
Proof
  recInduct vs_to_string_ind >> rpt strip_tac >> gs[vs_to_string_def]
  >> TOP_CASE_TAC >> gs[]
  >> res_tac >> pop_assum $ gs o single o GSYM
QED

Theorem v_rel_list_to_v:
  ∀ vs1 vs2.
    LIST_REL v_rel vs1 vs2 ⇒
    v_rel (list_to_v vs1) (list_to_v vs2)
Proof
  Induct_on ‘vs1’ >> gs[list_to_v_def]
  >> rpt strip_tac >> gs[] >> rveq
  >> res_tac >> asm_rewrite_tac[list_to_v_def]
  >> qexists_tac ‘[y; list_to_v ys]’ >> gs[]
QED

Theorem v_rel_list_to_v_app:
  ∀ vs11 vs12 vs21 vs22.
    LIST_REL v_rel vs11 vs21 ∧
    LIST_REL v_rel vs12 vs22 ⇒
    v_rel (list_to_v (vs11 ++ vs12)) (list_to_v (vs21 ++ vs22))
Proof
  Induct_on ‘vs11’ >> gs[v_rel_list_to_v]
  >> rpt strip_tac >> rveq >> gs[list_to_v_def]
QED

Theorem v_rel_do_eq:
  (∀ v11 v21 v12 v22.
     v_rel v11 v21 ∧
     v_rel v12 v22 ⇒
     do_eq v11 v12 = do_eq v21 v22) ∧
  (∀ vs11 vs21  vs12 vs22.
     LIST_REL v_rel vs11 vs21 ∧
     LIST_REL v_rel vs12 vs22 ⇒
     do_eq_list vs11 vs12 = do_eq_list vs21 vs22)
Proof
  qspecl_then [‘(λ v11 v12.
       ∀ v21 v22.
         v_rel v11 v21 ∧
         v_rel v12 v22 ⇒
         do_eq v11 v12 = do_eq v21 v22)’,
   ‘(λ vs11 vs12.
       ∀ vs21 vs22.
         LIST_REL v_rel vs11 vs21 ∧
         LIST_REL v_rel vs12 vs22 ⇒
         do_eq_list vs11 vs12 = do_eq_list vs21 vs22)’] mp_tac
  do_eq_ind
  >> impl_tac >> gs[]
  >> rpt strip_tac >> gs[do_eq_def] >> rveq
  >- (
    imp_res_tac LIST_REL_LENGTH
    >> Cases_on ‘cn1 = cn2’ >> gs[]
    >> COND_CASES_TAC >> gs[])
  >- (
    imp_res_tac LIST_REL_LENGTH
    >> COND_CASES_TAC >> gs[])
  >- (
    gs[Boolv_def]
    >> COND_CASES_TAC >> gs[]
    >> Cases_on ‘vs2 = []’ >> gs[]
    >> rpt (COND_CASES_TAC >> gs[]))
  >- (
    gs[Boolv_def]
    >> COND_CASES_TAC >> gs[]
    >> Cases_on ‘vs2 = []’ >> gs[]
    >> rpt (COND_CASES_TAC >> gs[]))
  >> TOP_CASE_TAC >> gs[]
  >> COND_CASES_TAC >> gs[]
QED

val trivial_tac =
  rpt strip_tac
  >> ‘LENGTH a1 = LENGTH a2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
  >> rpt (TOP_CASE_TAC >> gs[])
  >> gs[do_app_def]
  >> gs[Once v_rel_cases, Boolv_def, div_exn_v_def, chr_exn_v_def,
        v_rel_fp_translate]
  >> COND_CASES_TAC >> gs[];

val fp_tac =
  rpt strip_tac
  >> ‘LENGTH a1 = LENGTH a2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
  >> rpt (TOP_CASE_TAC >> gs[])
  >> gs[do_app_def]
  >> imp_res_tac $ GSYM v_rel_fp_translate >> gs[];

val mem_tac =
  rpt strip_tac
  >> ‘LENGTH a1 = LENGTH a2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
  >> ‘LENGTH refs1 = LENGTH refs2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
  >> rpt (TOP_CASE_TAC >> gs[])
  >> gs[do_app_def, store_lookup_def, sub_exn_v_def, store_alloc_def,
        store_assign_def, copy_array_def, v_rel_list_to_v, v_rel_list_to_v_char]
  >> TRY (COND_CASES_TAC >> gs[])
  >> imp_res_tac LIST_REL_EL_EQN
  >> first_x_assum $ qspec_then ‘n’ assume_tac >> gs[]
  >> Cases_on ‘EL n refs2’ >> gs[ref_rel_def];

Theorem do_app_thm:
  ∀op a1 a2 refs1 refs2 ffi.
    LIST_REL v_rel a1 a2 ∧ LIST_REL ref_rel refs1 refs2 ⇒
    OPTREL (λ((r1,f1),v1) ((r2,f2),v2).
             f1 = f2 ∧ res1_rel v1 v2 ∧ LIST_REL ref_rel r1 r2)
           (do_app (refs1,ffi) op a1) (do_app (refs2,ffi) op a2)
Proof
  Cases_on ‘op’ >> gs[Once do_app_def, OPTREL_def]
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- (
    rpt strip_tac
    >> ‘LENGTH a1 = LENGTH a2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> ntac 3 (TOP_CASE_TAC >> gs[do_app_def])
    >> imp_res_tac $ GSYM v_rel_do_eq
    >> TOP_CASE_TAC >> gs[Boolv_def]
    >> COND_CASES_TAC >> gs[])
  >- fp_tac
  >- fp_tac
  >- fp_tac
  >- fp_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- (
    rpt strip_tac
    >> ‘LENGTH a1 = LENGTH a2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> ‘LENGTH refs1 = LENGTH refs2’ by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> rpt (TOP_CASE_TAC >> gs[])
    >> gs[do_app_def]
    >> gs[store_assign_def, store_v_same_type_def]
    >> Cases_on ‘n < LENGTH refs2’ >> gs[]
    >> Cases_on ‘EL n refs1’ >> gs[]
    >> imp_res_tac LIST_REL_EL_EQN
    >> first_x_assum $ qspec_then ‘n’ assume_tac
    >> Cases_on ‘EL n refs2’ >> rveq >> gs[ref_rel_def]
    >> irule EVERY2_LUPDATE_same
    >> gs[ref_rel_def])
  >- mem_tac
  >- mem_tac
  >- mem_tac
  >- mem_tac
  >- mem_tac
  >- (
    mem_tac
    >> rveq >> irule EVERY2_LUPDATE_same >> gs[ref_rel_def])
  >- trivial_tac
  >- trivial_tac
  >- mem_tac
  >- (
    mem_tac
    >> rveq >> irule EVERY2_LUPDATE_same >> gs[ref_rel_def])
  >- mem_tac
  >- (
    mem_tac
    >> imp_res_tac LIST_REL_EL_EQN
    >> first_x_assum $ qspec_then ‘n'’ assume_tac >> gs[]
    >> Cases_on ‘EL n' refs2’ >> gs[ref_rel_def]
    >> rveq >> irule EVERY2_LUPDATE_same >> gs[ref_rel_def])
  >- trivial_tac
  >- trivial_tac
  >- trivial_tac
  >- (
    mem_tac
    >> imp_res_tac $ GSYM v_rel_v_to_char_list >> gs[])
  >- mem_tac
  >- mem_tac
  >- mem_tac
  >- (
    mem_tac
    >> imp_res_tac v_rel_v_to_list >> gs[OPTREL_def]
    >> imp_res_tac $ GSYM v_rel_vs_to_string >> gs[])
  >- (
    mem_tac
    >> imp_res_tac v_rel_v_to_list >> gs[OPTREL_def])
  >- (
    mem_tac
    >> imp_res_tac v_rel_v_to_list >> gs[OPTREL_def])
  >- (
    mem_tac
    >> imp_res_tac v_rel_v_to_list >> gs[OPTREL_def])
  >- (
    mem_tac
    >> rewrite_tac $ single LIST_REL_REPLICATE_same
    >> strip_tac >> gs[])
  >- mem_tac
  >- mem_tac
  >- (
    mem_tac
    >> TOP_CASE_TAC >> gs[]
    >> ‘LENGTH l = LENGTH l'’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> gs $ single LIST_REL_EL_EQN)
  >- ( mem_tac >> gs $ single LIST_REL_EL_EQN)
  >- (
    mem_tac
    >> ‘LIST_REL v_rel l l'’ by (gs $ single LIST_REL_EL_EQN)
    >> ‘LENGTH l = LENGTH l'’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> TOP_CASE_TAC >> gs[store_v_same_type_def]
    >> rveq >> irule EVERY2_LUPDATE_same >> gs[]
    >> irule EVERY2_LUPDATE_same >> gs[])
  >- (
    mem_tac >> TOP_CASE_TAC >> gs[]
    >> ‘LENGTH l = LENGTH l'’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> gs[LIST_REL_EL_EQN])
  >- (
    mem_tac >> TOP_CASE_TAC >> gs[]
    >> ‘LENGTH l = LENGTH l'’
      by (irule LIST_REL_LENGTH >> asm_exists_tac >> gs[])
    >> gs[LIST_REL_EL_EQN]
    >> COND_CASES_TAC  >> gs[store_v_same_type_def]
    >> Cases_on ‘i < 0’ >> gs[] >> rveq
    >> gs[LENGTH_LUPDATE]
    >> rpt strip_tac >> gs[LIST_REL_EL_EQN]
    >> res_tac >> rewrite_tac [EL_LUPDATE]
    >> COND_CASES_TAC >> gs[]
    >> irule EVERY2_LUPDATE_same >> gs[]
    >> res_tac >> pop_assum $ mp_tac
    >> asm_rewrite_tac [] >> gs[ref_rel_def])
  >- mem_tac
  >- (
    mem_tac
    >> Cases_on ‘i < 0’ >> gs[]
    >> rveq >> gs[LIST_REL_EL_EQN]
    >> rpt strip_tac
    >> res_tac >> rewrite_tac [EL_LUPDATE]
    >> COND_CASES_TAC >> gs[])
  >- (
    mem_tac
    >> imp_res_tac v_rel_v_to_list >> gs[OPTREL_def]
    >> irule v_rel_list_to_v_app >> gs[])
  >- trivial_tac
  >- (mem_tac >> rveq >> irule EVERY2_LUPDATE_same >> gs[])
  >- (mem_tac >> rveq >> irule EVERY2_LUPDATE_same >> gs[])
  >> fp_tac >> simp[nat_to_v_def]
QED


(*
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
     DISJOINT (set (FLAT (MAP (λ(p,e). pat_bindings p []) pes)))
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
    \\ fs [replace_constants_exp_def]
    \\ ‘getOpClass op ≠ FunApp’ by
      (Cases_on ‘op’ \\ fs [astTheory.getOpClass_def])
    \\ gvs []
    \\ fs [evaluate_def,CaseEq"prod",gather_used_identifiers_exp_def]
    \\ rpt $ pop_assum mp_tac
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ rpt strip_tac \\ gvs []
    \\ last_x_assum $ drule_at (Pos last)
    \\ disch_then $ drule_at (Pos last)
    \\ impl_tac THEN1 fs [IN_DISJOINT,MEM_FLAT,MEM_MAP]
    \\ strip_tac \\ gvs [PULL_EXISTS]
    \\ rename [‘res_rel res0 res1’]
    \\ Cases_on ‘res0’ \\ Cases_on ‘res1’ \\ gvs [MAP_REVERSE]
    \\ qspecl_then [‘op’,‘REVERSE a’,‘REVERSE a'’,‘st'.refs’,‘t1.refs’,‘t1.ffi’]
          mp_tac do_app_thm
    \\ impl_tac
    THEN1 (fs [LIST_REL_REVERSE_EQ] \\ fs [state_rel_def])
    \\ rename [‘state_rel s1 t1’]
    \\ ‘s1.ffi = t1.ffi’ by fs [state_rel_def]
    \\ Cases_on ‘getOpClass op = Simple’ \\ gvs []
    THEN1
     (rw [] \\ gvs [AllCaseEqs()]
      \\ Cases_on ‘do_app (t1.refs,t1.ffi) op (REVERSE a')’ \\ fs []
      \\ PairCases_on ‘x’ \\ gvs []
      \\ fs [state_rel_def]
      \\ rename [‘res_rel (list_result g1) (list_result g2)’]
      \\ Cases_on ‘g1’ \\ Cases_on ‘g2’ \\ gvs []
      \\ Cases_on ‘e’ \\ Cases_on ‘e'’ \\ gvs [])
    \\ Cases_on ‘getOpClass op = Reals’ \\ gvs []
    THEN1
     (rw [] \\ gvs [AllCaseEqs()]
      \\ Cases_on ‘do_app (t1.refs,t1.ffi) op (REVERSE a')’ \\ fs []
      \\ TRY (gvs [state_rel_def,shift_fp_opts_def] \\ NO_TAC)
      \\ PairCases_on ‘x’ \\ gvs []
      \\ fs [state_rel_def]
      \\ rename [‘res_rel (list_result g1) (list_result g2)’]
      \\ Cases_on ‘g1’ \\ Cases_on ‘g2’ \\ gvs []
      \\ Cases_on ‘e’ \\ Cases_on ‘e'’ \\ gvs [])
    \\ ‘getOpClass op = Icing’ by (
      Cases_on ‘getOpClass op’ \\ fs [astTheory.getOpClass_def]
      \\ Cases_on ‘op’ \\ gs[])
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘do_app (t1.refs,t1.ffi) op (REVERSE a')’ \\ fs []
    \\ PairCases_on ‘x’ \\ gvs []
    \\ fs [state_rel_def,shift_fp_opts_def]
    \\ rw [] \\ gvs []
    \\ TRY (Cases_on ‘r’ \\ Cases_on ‘x2’) \\ fs [do_fprw_def]
    \\ TRY (Cases_on ‘a''’ \\ Cases_on ‘a'''’) \\ fs [v_rel_Boolv]
    \\ every_case_tac \\ fs [v_rel_Boolv_id]
    \\ metis_tac [])
  THEN1
   (rename [‘Log’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘lop’ \\ gvs [do_log_def,AllCaseEqs()]
    \\ imp_res_tac v_rel_Boolv \\ fs [])
  THEN1
   (rename [‘If’]
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ gvs [do_if_def,AllCaseEqs()]
    \\ imp_res_tac v_rel_Boolv \\ gvs []
    THEN1 (first_x_assum (qspec_then ‘T’ assume_tac) \\ gvs [])
    THEN1 (first_x_assum (qspec_then ‘F’ assume_tac) \\ gvs []))
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
  THEN1
   (rename [‘Let’]
    \\ Cases_on ‘xo’
    \\ gvs [evaluate_def,gather_used_identifiers_exp_def,replace_constants_exp_def]
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ rename [‘res_rel res0 res1’]
    \\ reverse (Cases_on ‘res0’) \\ Cases_on ‘res1’ \\ gvs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
    \\ gvs [namespaceTheory.nsOptBind_def]
    \\ first_x_assum irule \\ gvs []
    \\ irule env_rel_update \\ gvs [])
  THEN1
   (rename [‘Letrec’]
    \\ gvs [evaluate_def,replace_constants_exp_def,
            gather_used_identifiers_exp_def]
    \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD,CaseEq"bool"]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env11’
    \\ last_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then ‘env11’ mp_tac)
    \\ reverse impl_tac THEN1 (rw [] \\ fs [])
    \\ unabbrev_all_tac
    \\ qmatch_goalsub_abbrev_tac ‘MAP ll’
    \\ ‘ll = (I ## I ## replace_constants_exp al)’ by
      fs [Abbr‘ll’,FUN_EQ_THM,FORALL_PROD]
    \\ gvs [] \\ irule env_rel_build_rec_env \\ gvs [])
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
    \\ ‘env1.c = env.c’ by fs [env_rel_def] \\ fs []
    \\ ‘LIST_REL ref_rel s.refs t.refs’ by fs [state_rel_def]
    \\ drule $ CONJUNCT1 pmatch_thm
    \\ disch_then $ qspecl_then [‘env.c’,‘p’,‘v’,‘[]’,‘v1’,‘[]’] mp_tac
    \\ fs [] \\ strip_tac
    \\ Cases_on ‘pmatch env.c s.refs p v []’
    \\ Cases_on ‘pmatch env.c t.refs p v1 []’ \\ gvs []
    \\ last_x_assum drule
    \\ disch_then drule
    \\ disch_then irule
    \\ ‘DISJOINT (set (MAP FST a)) (set (MAP SND al))’ by
      (imp_res_tac pmatch_pat_bindings
       \\ fs [IN_DISJOINT,SUBSET_DEF] \\ metis_tac [])
    \\ pop_assum mp_tac
    \\ ntac 2 (pop_assum kall_tac)
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘a'’
    \\ qid_spec_tac ‘a’
    \\ Induct \\ fs []
    \\ fs [PULL_EXISTS,FORALL_PROD] \\ rw []
    \\ irule env_rel_update_lemma \\ fs [])
QED
*)

Theorem evaluate_decs_app:
  ∀ (s1:'ffi state) env ds1 ds2 s2 r.
    evaluate_decs s1 env (ds1 ++ ds2) =
    case evaluate_decs s1 env ds1 of
      |(s2, Rerr e) => (s2, Rerr e)
      |(s2, Rval env1) =>
         case evaluate_decs s2 (extend_dec_env env1 env) ds2 of
           | (s2, r) => (s2, combine_dec_result env1 r)
Proof
  Induct_on ‘ds1’ >> gs[]
  >- (rpt strip_tac >> TOP_CASE_TAC
      >> gs[evaluate_decs_def, extend_dec_env_def, combine_dec_result_def]
      >> TOP_CASE_TAC >> gs[])
  >> rpt strip_tac
  >> simp[Once evaluatePropsTheory.evaluate_decs_cons]
  >> ntac 2 (reverse TOP_CASE_TAC >> gs[])
  >- simp[Once evaluatePropsTheory.evaluate_decs_cons]
  >> simp[Once evaluatePropsTheory.evaluate_decs_cons]
  >> Cases_on ‘evaluate_decs q (extend_dec_env a env) ds1’ >> gs[]
  >> reverse $ Cases_on ‘r’ >- gs[combine_dec_result_def]
  >> simp[]
  >> simp[SimpR “$=”, combine_dec_result_def]
  >> ‘extend_dec_env (extend_dec_env a' a) env =
      extend_dec_env <| v := nsAppend a'.v a.v; c := nsAppend a'.c a.c |> env’
     by (gs[extend_dec_env_def])
  >> pop_assum $ simp o single
  >> qmatch_goalsub_abbrev_tac ‘evaluate_decs s2 (extend_dec_env addEnv env) ds2’
  >> Cases_on ‘evaluate_decs s2 (extend_dec_env addEnv env) ds2’
  >> gs[] >> TOP_CASE_TAC >> gs[combine_dec_result_def]
QED

Theorem MEM_MAP_SND:
  MEM (x,y) xs ⇒ MEM y (MAP SND xs)
Proof
  Induct_on ‘xs’ >> gs[]
  >> rpt strip_tac >> rveq >> gs[]
QED

(**
Theorem build_decl_list_lemma:
  ∀ (s1:'ffi state) env1 env ws1 ws2.
    (∀ x w.
       MEM (w, x) ws2 ⇒
       nsLookup env.v (Short x) = NONE) ∧
    DISJOINT (set (MAP SND ws2)) (set (MAP SND ws1)) ∧
   (∀ x w. MEM (w, x) ws2 ⇒ UNIQUE x (MAP SND ws2)) ∧
    env_rel env env1 ws1 ⇒
    ∃ env2.
      evaluate_decs s1 env1 (build_decl_list ws2) = (s1, Rval env2) ∧
      env_rel env (extend_dec_env env2 env1) (ws1 ++ ws2)
Proof
  Induct_on ‘ws2’ >> gs[build_decl_list_def]
  >- (gs[extend_dec_env_def, env_rel_def])
  >> rpt strip_tac >> Cases_on ‘h’ >> gs[build_decl_list_def]
  >> rename1 ‘Lit (Word64 w)’ >> rename1 ‘Pvar x’
  >> simp [Once evaluatePropsTheory.evaluate_decs_cons, Once evaluate_decs_def,
           astTheory.pat_bindings_def, evaluate_def, pmatch_def]
  >> qmatch_goalsub_abbrev_tac ‘extend_dec_env newEnv env1’
  >> ‘env_rel env (extend_dec_env newEnv env1) (ws1 ++ [(w,x)])’
    by (
      unabbrev_all_tac >> gs[env_rel_def, extend_dec_env_def]
      >> rpt conj_tac
      >- (
        rpt strip_tac
        >> reverse $ Cases_on ‘n’ >> gs[ml_progTheory.nsLookup_nsBind_compute]
        >- (
          CCONTR_TAC >> gs[]
          >> first_x_assum $ qspecl_then [‘Long m i’, ‘v’] mp_tac
          >> impl_tac >> gs[])
        >> Cases_on ‘x = n'’ >> gs[] >> rveq
        >> first_x_assum $ qspecl_then [‘Short n'’, ‘v’] mp_tac
        >> impl_tac >> gs[])
      >- (
        rpt strip_tac >> gs[ml_progTheory.nsLookup_nsBind_compute]
        >> COND_CASES_TAC >> gs[] >> rveq
        >> imp_res_tac MEM_MAP_SND >> gs[])
      >> rpt strip_tac >> res_tac
      >> qexists_tac ‘v1’ >> gs[]
      >> Cases_on ‘n’ >> gs[ml_progTheory.nsLookup_nsBind_compute]
      >> ‘x ≠ n'’ by (CCONTR_TAC >> gs[])
      >> gs[])
  >> first_x_assum $ qspecl_then [‘s1’, ‘extend_dec_env newEnv env1’, ‘env’, ‘ws1 ++ [(w,x)]’] mp_tac
  >> impl_tac >> gs[]
  >- (
    gs[DISJOINT_DEF] >> rpt conj_tac
    >- metis_tac[]
    >- (gs[INTER_DEF, FUN_EQ_THM] >> metis_tac[])
    >- (
      gs[env_rel_def]
      >> CCONTR_TAC >> gs[]
      >> qpat_x_assum `∀ x w. _ ⇒ UNIQUE _ _` $ qspecl_then [‘x’, ‘w’] mp_tac
      >> gs[] >> strip_tac >> gs[UNIQUE_DEF]
      >> ‘L1 = []’ by (Cases_on ‘L1’ >> gs[])
      >> rveq >> gs[])
    >> rpt strip_tac >> first_x_assum $ qspecl_then [‘x'’, ‘w'’] mp_tac
    >> gs[UNIQUE_DEF]
    >> rpt strip_tac
    >> ‘∃ L1'. L1 = (x:: L1')’
      by (Cases_on ‘L1’ >> gs[] >> rveq >> imp_res_tac MEM_MAP_SND)
    >> rveq
    >> ‘MAP SND ws2 = L1' ++ [x'] ++ L2’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> gs[] >> qexists_tac ‘L1'’ >> qexists_tac ‘L2’ >> gs[])
  >> strip_tac >> gs[combine_dec_result_def]
  >> ‘ws1 ++ (w,x) :: ws2 = ws1 ++ [(w,x)] ++ ws2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[extend_dec_env_def]
QED
**)

Theorem MEM_used_ids_not_mem_vars:
  ∀ ws x es n.
    MEM x (MAP SND (build_cnst_list ws es n)) ⇒
    ~ MEM x es
Proof
  Induct_on ‘ws’ >> gs[build_cnst_list_def]
  >> rpt gen_tac
  >> COND_CASES_TAC >> rw[]
  >- (first_x_assum irule >> asm_exists_tac >> gs[])
  >- gs[]
  >> res_tac
  >> gs[]
QED

Theorem build_cnst_list_unique:
  DISJOINT (set (FLAT (MAP gather_used_identifiers_exp es)))
    (set (MAP SND (build_cnst_list ws (FLAT (MAP gather_used_identifiers_exp es)) 0)))
Proof
  gs[pred_setTheory.DISJOINT_DEF, INTER_DEF]
  >> rewrite_tac [FUN_EQ_THM] >> rpt strip_tac >> reverse EQ_TAC
  >- gs[]
  >> gs[]
  >> Cases_on ‘MEM x (MAP SND (build_cnst_list ws (FLAT (MAP gather_used_identifiers_exp es)) 0))’
  >> gs[]
  >> imp_res_tac MEM_used_ids_not_mem_vars
QED

Theorem build_cnst_list_disjoint_res:
  ∀ cnsts vars n.
    DISJOINT (set (MAP SND (build_cnst_list cnsts vars n))) (set vars)
Proof
  Induct_on ‘cnsts’ >> gs[build_cnst_list_def]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM varStr vars’
  >> COND_CASES_TAC >> gs[]
  >> first_x_assum $ qspecl_then [‘varStr :: vars’, ‘SUC n’] assume_tac
  >> gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM]
  >> rpt strip_tac >> first_x_assum $ qspec_then ‘x’ strip_assume_tac
  >> gs[]
QED

Theorem build_cnst_list_unique:
  ∀ cnsts vars n.
    (∀ x w.
       MEM (w, x) (build_cnst_list cnsts vars n) ⇒
       UNIQUE x (MAP SND (build_cnst_list cnsts vars n)))
Proof
  Induct_on ‘cnsts’ >> gs[build_cnst_list_def]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM varStr vars’
  >> qspecl_then [‘cnsts’, ‘varStr::vars’, ‘SUC n’] assume_tac build_cnst_list_disjoint_res
  >> TOP_CASE_TAC >> gs[]
  >- (first_x_assum irule >> asm_exists_tac >> gs[])
  >- (
    rveq
    >> gs[UNIQUE_DEF]
    >> qexists_tac ‘[]’
    >> qexists_tac ‘MAP SND (build_cnst_list cnsts (varStr::vars) (SUC n))’
    >> gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM] >> strip_tac >> gs[]
    >> first_x_assum $ qspec_then ‘varStr’ strip_assume_tac >> gs[])
  >> res_tac >> gs[UNIQUE_DEF]
  >> qexists_tac ‘varStr::L1’ >> qexists_tac ‘L2’ >> gs[]
  >> CCONTR_TAC >> gs[] >> rveq
  >> gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM]
  >> imp_res_tac MEM_MAP_SND
QED

Theorem build_cnst_list_up:
  ∀ cnsts1 cnsts2 ids x n.
    MEM x (MAP SND (build_cnst_list cnsts1 ids n)) ⇒
    MEM x (MAP SND (build_cnst_list (cnsts1++cnsts2) ids n))
Proof
  Induct_on ‘cnsts1’ >> gs[build_cnst_list_def]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM varStr ids’
  >> COND_CASES_TAC >> gs[]
QED

Definition dec_res_rel_def[simp]:
  dec_res_rel env1 env2 (Rval x) (Rval y) ws =
    (env_rel (extend_dec_env x env1) (extend_dec_env y env2) ws ∧
    env_rel_strict x y ws) ∧
  dec_res_rel env1 env2 (Rerr (Rraise v)) (Rerr (Rraise w)) ws = v_rel v w ∧
  dec_res_rel env1 env2 (Rerr (Rabort a)) (Rerr (Rabort b)) ws = (a = b) ∧
  dec_res_rel _ _ _ _ _ = F
End

Theorem ALL_DISTINCT_MAP:
  ALL_DISTINCT (MAP (λ (x,y,z). x) funs) =
  ALL_DISTINCT (MAP (λ (x,y,z). x) (MAP (I ## I ## replace_constants_exp al) funs))
Proof
  Induct_on ‘funs’ >> gs[]
  >> rpt strip_tac >> Cases_on ‘h’ >> gs[]
  >> Cases_on ‘r’ >> gs[MEM_MAP] >> EQ_TAC >> rpt strip_tac
  >- (rveq >> Cases_on ‘y'’ >> gs[]
      >> Cases_on ‘r’ >> gs[])
  >- (gs[])
  >- (rveq >> Cases_on ‘y’ >> gs[]
      >> Cases_on ‘r’ >> gs[])
  >> gs[]
QED

(*
Theorem replace_constants_decl_thm:
  ∀(s:'ffi state) env ds s1 res t env1 al.
     DISJOINT (set (gather_used_identifiers_decl ds))
              (set (MAP SND al)) ∧
     evaluate_decs s env ds = (s1,res) ∧
     state_rel s t ∧ env_rel env env1 al ⇒
     ∃t1 res1.
        evaluate_decs t env1 (replace_constants_decl ds al) = (t1,res1) ∧
        state_rel s1 t1 ∧
        dec_res_rel env env1 res res1 al
Proof
  recInduct evaluate_decs_ind >> rw[]
  >- (
    gs[replace_constants_decl_def, env_rel_def, combine_dec_result_def,
        dec_res_rel_def, extend_dec_env_def, Once env_rel_strict_cases]
    >> rpt strip_tac >> Cases_on ‘p1’ >> gs[])
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _` mp_tac
    >> simp[Once replace_constants_decl_def, Once evaluate_decs_def, Once evaluate_decs_app]
    >> TOP_CASE_TAC >> gs[]
    >> first_x_assum $ qspecl_then [‘t’, ‘env1’, ‘al’] mp_tac
    >> impl_tac
    >- gs[gather_used_identifiers_decl_def]
    >> strip_tac >> reverse TOP_CASE_TAC >> gs[]
    >> Cases_on ‘res1’ >> gs[combine_dec_result_def]
    >- (rpt strip_tac >> rveq >> gs[])
    >> TOP_CASE_TAC >> gs[]
    >> rpt strip_tac >> rveq
    >> first_x_assum $ qspecl_then [‘t1’, ‘extend_dec_env a' env1’, ‘al’] mp_tac
    >> impl_tac >- gs[gather_used_identifiers_decl_def, extend_dec_env_def]
    >> strip_tac >> gs[]
    >> Cases_on ‘r’ >> Cases_on ‘res1’ >> gs[dec_res_rel_def, extend_dec_env_def]
    >- (imp_res_tac env_rel_strict_nsAppend >> gs[extend_dec_env_def])
    >> Cases_on ‘e’ >> Cases_on ‘e'’ >> gs[dec_res_rel_def])
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _` mp_tac
    >> simp[Once evaluate_decs_def, replace_constants_decl_def]
    >> reverse COND_CASES_TAC >> gs[]
    >- (
      rpt strip_tac >> rveq >> gs[]
      >> gs[Once evaluate_decs_def, dec_res_rel_def, combine_dec_result_def])
    >> TOP_CASE_TAC >> gs[]
    >> first_x_assum $ mp_then Any mp_tac (CONJUNCT1 replace_constants_exp_thm)
    >> disch_then $ qspecl_then [‘t’, ‘env1’, ‘al’] mp_tac >> impl_tac
    >- gs[gather_used_identifiers_decl_def]
    >> rpt strip_tac >> gs[Once evaluate_decs_def]
    >> Cases_on ‘r’ >> Cases_on ‘res1’ >> gs[] >> rveq
    >~ [‘res_rel (Rerr err1) (Rerr err2)’]
    >- (
      Cases_on ‘err1’ >> Cases_on ‘err2’ >> gs[combine_dec_result_def])
    >> imp_res_tac evaluatePropsTheory.evaluate_sing >> rveq
    >> Cases_on ‘a’ >> gs[] >> rveq
    >> first_assum $ mp_then Any mp_tac $ CONJUNCT1 pmatch_thm
    >> gs[state_rel_def, env_rel_def]
    >> disch_then $ qspecl_then [‘env.c’, ‘q.refs’, ‘p’, ‘[]’, ‘[]’, ‘t1.refs’] mp_tac
    >> impl_tac >- gs[]
    >> strip_tac >> ntac 2 TOP_CASE_TAC >> gs[combine_dec_result_def, bind_exn_v_def]
    >> imp_res_tac pmatch_pat_bindings >> gs[extend_dec_env_def] >> conj_tac
    >- (
      irule env_rel_update_alist
      >> gs[env_rel_def]
      >> gs[IN_DISJOINT,SUBSET_DEF, gather_used_identifiers_decl_def]
      >> metis_tac [])
    >> irule env_rel_strict_update_alist
    >> gs[IN_DISJOINT,SUBSET_DEF, gather_used_identifiers_decl_def]
    >> metis_tac [])
  >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    >> gs[replace_constants_decl_def, evaluate_decs_def]
    >> ntac 2 COND_CASES_TAC >> gs[ALL_DISTINCT_MAP]
    >> rpt strip_tac >> rveq >> gs[combine_dec_result_def, dec_res_rel_def, GSYM ALL_DISTINCT_MAP]
    >> first_assum $ mp_then Any assume_tac env_rel_build_rec_env_decl
    >> first_x_assum $ qspecl_then [‘funs’] assume_tac
    >> gs[gather_used_identifiers_decl_def]
    >> irule env_rel_nsAppend >> gs[])
  >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    >> gs[replace_constants_decl_def, evaluate_decs_def]
    >> COND_CASES_TAC >> gs[]
    >> rpt strip_tac >> rveq >> gs[combine_dec_result_def, state_rel_def]
    >> gs[env_rel_def, Once env_rel_strict_cases, extend_dec_env_def]
    >> rpt strip_tac >> Cases_on ‘p1’ >> gs[])
  >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    >> gs[replace_constants_decl_def, evaluate_decs_def]
    >> rpt strip_tac >> rveq
    >> gs[combine_dec_result_def, state_rel_def, extend_dec_env_def,
          env_rel_def, Once env_rel_strict_cases]
    >> rpt strip_tac >> Cases_on ‘p1’ >> gs[])
  >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    >> gs[replace_constants_decl_def, evaluate_decs_def]
    >> rpt strip_tac >> rveq >> gs[combine_dec_result_def, state_rel_def]
    >> gs[env_rel_def, Once env_rel_strict_cases, extend_dec_env_def]
    >> rpt strip_tac >> Cases_on ‘p1’ >> gs[])
  >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    >> gs[replace_constants_decl_def, evaluate_decs_def]
    >> TOP_CASE_TAC >> gs[]
    >> first_x_assum $ qspecl_then [‘t’, ‘env1’, ‘al’] mp_tac
    >> impl_tac  >- gs[gather_used_identifiers_decl_def]
    >> rpt strip_tac >> gs[]
    >> rpt strip_tac >> rveq >> gs[combine_dec_result_def, state_rel_def]
    >> Cases_on ‘r’ >> Cases_on ‘res1’ >> gs[]
    >> first_assum $ mp_then Any assume_tac env_rel_nsLift
    >> first_x_assum $ qspec_then ‘mn’ assume_tac >> gs[]
    >> irule env_rel_nsAppend >> gs[])
  >> qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
  >> gs[replace_constants_decl_def, evaluate_decs_def]
  >> TOP_CASE_TAC >> gs[]
  >> first_x_assum $ qspecl_then [‘t’, ‘env1’, ‘al’] mp_tac
  >> impl_tac  >- gs[gather_used_identifiers_decl_def]
  >> rpt strip_tac >> gs[]
  >> Cases_on ‘r’ >> Cases_on ‘res1’
  >> gs[combine_dec_result_def, dec_res_rel_def] >> rveq >> gs[]
  >> first_x_assum $ qspecl_then [‘t1’, ‘extend_dec_env a' env1’, ‘al’] mp_tac
  >> impl_tac  >- gs[gather_used_identifiers_decl_def, extend_dec_env_def]
  >> rpt strip_tac >> rveq >> gs[combine_dec_result_def, state_rel_def]
  >> Cases_on ‘res’ >> Cases_on ‘res1’ >> gs[extend_dec_env_def]
  >- ( imp_res_tac (SIMP_RULE std_ss [extend_dec_env_def] env_rel_nsAppend)
       >> gs[])
  >> Cases_on ‘e’ >> Cases_on ‘e'’ >> gs[]
QED
*)

(*
Theorem lift_constants_decl_thm:
  ∀ (s1:'ffi state) env ds s2 env1 res1 res2 ws1 s1' ids n .
    let ws2 =
        build_cnst_list (gather_constants_decl ds)
                        (MAP SND ws1 ++ ids) n in
      (* (∀ x. MEM x (gather_used_identifiers_decl ds) ⇒
            MEM x ids) ∧ *)
      (∀ x v.
         MEM x (MAP SND ws2) ⇒
         nsLookup env.v (Short x) = NONE) ∧
    DISJOINT (set (MAP SND ws2)) (set (MAP SND ws1)) ∧
    env_rel env env1 ws1 ∧
    state_rel s1 s1' ∧
    evaluate_decs s1 env ds = (s2, res1) ⇒
    ∃ s2'. evaluate_decs s1' env1 (FST (lift_constants_decl ds (MAP SND ws1 ++ ids) n)) = (s2', res1) ∧
    state_rel s2 s2'
Proof
  recInduct evaluate_decs_ind >> rw[]
  >- gs[lift_constants_decl_def, state_rel_def]
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _` mp_tac
    >> gs[Once evaluate_decs_def]
    >> TOP_CASE_TAC >> gs[]
    >> first_x_assum $ qspecl_then [‘env1’, ‘ws1’, ‘s1'’, ‘ids’, ‘n’] mp_tac
    >> impl_tac
    >- (
      rpt conj_tac >> gs[]
      (* >- (rpt strip_tac >> gs[gather_used_identifiers_decl_def])*)
      >- (
        rpt strip_tac
        >> first_x_assum $ mp_then Any mp_tac build_cnst_list_up
        >> disch_then $ qspec_then ‘gather_constants_decl (d2::ds)’ assume_tac
        >> first_x_assum irule >> gs[gather_constants_decl_def])
      >> gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM]
      >> rpt strip_tac >> first_x_assum $ qspec_then ‘x’ strip_assume_tac
      >> gs[]
      >> DISJ1_TAC
      >> CCONTR_TAC >> gs[]
      >> first_x_assum $ mp_then Any mp_tac build_cnst_list_up
      >> disch_then $ qspec_then ‘gather_constants_decl (d2::ds)’ assume_tac
      >> gs[gather_constants_decl_def])
    >> strip_tac >> reverse TOP_CASE_TAC >> gs[]
    >- (
      rpt strip_tac >> gs[lift_constants_decl_def]
      >> Cases_on ‘lift_constants_decl [d1] (MAP SND ws1 ++ ids) n’ >> gs[]
      >> Cases_on ‘r’ >> gs[]
      >> Cases_on ‘lift_constants_decl (d2::ds) (r' ++ MAP SND ws1 ++ ids) q''’ >> gs[]
      >> Cases_on ‘r’ >> gs[]
      >> gs[lift_constants_decl_def, Once evaluate_decs_def]
      >> simp[Once evaluate_decs_app] >> rveq >> gs[])
    >> simp[Once lift_constants_decl_def]
    >> Cases_on ‘lift_constants_decl [d1] (MAP SND ws1 ++ ids) n’ >> gs[]
    >> Cases_on ‘r’ >> gs[]
    >> Cases_on ‘lift_constants_decl (d2::ds) (r' ++ MAP SND ws1 ++ ids) q''’ >> gs[]
    >> Cases_on ‘r’ >> gs[]
    >> gs[Once evaluate_decs_app]
    >> TOP_CASE_TAC >> gs[] >> rpt strip_tac >> rveq
    >> first_x_assum $ qspecl_then [‘extend_dec_env a env1’, ‘ws1’, ‘s2'’, ‘r' ++ ids’, ‘q''’] mp_tac
    >> impl_tac
    >- (
      rpt conj_tac >> gs[]
      >- (
        rpt strip_tac >> gs[gather_constants_decl_def, MEM_APPEND]
        >> gs[extend_dec_env_def, namespacePropsTheory.nsLookup_nsAppend_none]
        >> conj_tac
        >- (cheat) (* Follows from construction of build_cnst_list *)
        >> DISJ1_TAC >> first_x_assum irule
        >> cheat (* lifting lemma for build_cnst_list *))
      >- (
        gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM]
        >> rpt strip_tac >> first_x_assum $ qspec_then ‘x’ strip_assume_tac
        >> gs[]
        >> DISJ1_TAC
        >> CCONTR_TAC >> gs[]
        >> first_x_assum $ mp_then Any mp_tac build_cnst_list_up
        >> cheat (* Lemma about build_cnst_list fine *))
      >> cheat) (* Should work *)

    (* OLD SUBGOAL PROOF:
       >> first_x_assum $ qspecl_then [‘extend_dec_env a env1’, ‘ws1’, ‘s2'’,
       ‘(MAP SND (build_cnst_list (gather_constants_decl [d1]) ids n)) ++ ids’, ‘m’] mp_tac
    >> impl_tac
    >- (
      rpt conj_tac >> gs[]
      >- (rpt strip_tac >> gs[gather_used_identifiers_decl_def])
      >- (
        rpt strip_tac >> gs[gather_constants_decl_def, MEM_APPEND]
        >> gs[extend_dec_env_def, namespacePropsTheory.nsLookup_nsAppend_none]
        >> conj_tac
        >- (cheat) (* Follows from construction of build_cnst_list *)
        >> DISJ1_TAC >> first_x_assum irule
        >> cheat (* lifting lemma for build_cnst_list *))
      >- (
        gs[DISJOINT_DEF, INTER_DEF, FUN_EQ_THM]
        >> rpt strip_tac >> first_x_assum $ qspec_then ‘x’ strip_assume_tac
        >> gs[]
        >> DISJ1_TAC
        >> CCONTR_TAC >> gs[]
        >> first_x_assum $ mp_then Any mp_tac build_cnst_list_up
        >> cheat (* Lemma about build_cnst_list fine *))
      >> cheat) (* Should work *) *)
    >> strip_tac >> gs[] >> cheat)
  >- (
    gs[Once lift_constants_decl_def, Once evaluate_decs_app]
    >> qpat_x_assum `DISJOINT _ _` mp_tac
    >> qmatch_goalsub_abbrev_tac ‘DISJOINT (set (MAP SND varList)) _’
    >> rpt strip_tac
    >> qspecl_then [‘s1'’, ‘env1’, ‘env’, ‘ws1’, ‘varList’] mp_tac
                          build_decl_list_lemma
    >> impl_tac >> gs[]
    >- (
      conj_tac >> unabbrev_all_tac
      >- (
        rpt strip_tac >> imp_res_tac MEM_MAP_SND >> res_tac)
      >> rpt strip_tac
      >> irule build_cnst_list_unique >> asm_exists_tac >> gs[])
    >> strip_tac >> unabbrev_all_tac
    >> gs[gather_constants_decl_def]
    >> qpat_x_assum `evaluate_decs _ _ [Dlet _ _ _] = _` mp_tac
    >> gs[evaluate_decs_def]
    >> reverse COND_CASES_TAC >> gs[]
    >- (rpt strip_tac >> gs[combine_dec_result_def])
    >> TOP_CASE_TAC
    >> first_x_assum $ mp_then Any mp_tac (CONJUNCT1 replace_constants_exp_thm)
    >> disch_then $ qspecl_then [‘s1'’, ‘extend_dec_env env2 env1’, ‘ws1 ++ build_cnst_list (gather_constants_exp e) (MAP SND ws1 ++ ids) n’] mp_tac
    >> impl_tac
    >- (
      rpt conj_tac >> gs[] >> conj_tac
      >- (cheat) (* Missing assumption *)
      >> cheat (* Also missing assumption *) )
    >> disch_then strip_assume_tac >> gs[]
*)

val _ = export_theory();
