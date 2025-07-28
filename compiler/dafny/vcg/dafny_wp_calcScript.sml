(*
  Calculus for VCG for Dafny
*)
Theory dafny_wp_calc
Ancestors
  integer dafny_ast dafny_semanticPrimitives dafnyProps dafny_evaluate
  dafny_evaluateProps dafny_eval_rel
Libs
  preamble


Datatype:
  met_spec = <| ins       : (mlstring # type) list
              ; reqs      : exp list
              ; ens       : exp list
              ; reads     : exp list
              ; decreases : exp list
              ; outs      : (mlstring # type) list
              ; mods      : exp list
              ; rank      : num |>
End

Datatype:
  met = Method mlstring met_spec statement
End

Overload "int_lt" = “BinOp Lt”
Overload "int_le" = “BinOp Le”
Overload "int_lit" = “λn. Lit (IntL n)”

(* TODO Move to AST *)
Definition Foralls_def:
  Foralls [] e = e ∧
  Foralls (v::vs) e = Forall v (Foralls vs e)
End

Definition lex_lt_def:
  lex_lt [] = False ∧
  lex_lt ((x,y)::rest) =
    conj [int_le (int_lit 0) x;
          int_le (int_lit 0) y;
          If (dfy_eq x y) (lex_lt rest) (int_lt x y)]
End

Definition decrease_lt_def:
  decrease_lt xs ys =
    if LENGTH xs = LENGTH ys then
      lex_lt (ZIP (xs,ys))
    else
      if LENGTH xs < LENGTH ys then True else False
End

Definition decreases_check_def:
  decreases_check (now_r,now) (old_r:num,old) =
    if now_r ≠ old_r then
      if now_r < old_r then [] else [False]
    else [decrease_lt now old]
End

Definition wrap_old_def:
  wrap_old (x,es) = (x,MAP Old es)
End

Definition freevars_def:
  (freevars (Let binds body) ⇔
     (BIGUNION (set (MAP freevars (MAP SND binds))))
      UNION ((freevars body) DIFF (set (MAP FST binds)))) ∧
  (freevars (Var n) ⇔ {n}) ∧
  (freevars (Lit _) ⇔ {}) ∧
  (freevars (If grd thn els) ⇔
     freevars grd UNION freevars thn UNION freevars els) ∧
  (freevars (UnOp _ e) ⇔ freevars e) ∧
  (freevars (BinOp _ e₀ e₁) ⇔
     (freevars e₀) UNION (freevars e₁)) ∧
  (freevars (ArrLen arr) ⇔ freevars arr) ∧
  (freevars (ArrSel arr idx) ⇔
     freevars arr UNION freevars idx) ∧
  (freevars (FunCall _ args) ⇔
     BIGUNION (set (MAP freevars args))) ∧
  (freevars (Forall (vn,_) e) ⇔
     freevars e DELETE vn) ∧
  (freevars (Old e) ⇔ freevars e) ∧
  (freevars (ForallHeap mods e) ⇔
     BIGUNION (set (MAP freevars mods)) UNION freevars e)
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_exp_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Definition no_Old_def:
  (no_Old (Old _) ⇔ F) ∧
  (no_Old (Lit _) ⇔ T) ∧
  (no_Old (Var _) ⇔ T) ∧
  (no_Old (If tst thn els) ⇔
     no_Old tst ∧ no_Old thn ∧ no_Old els) ∧
  (no_Old (UnOp _ e) ⇔ no_Old e) ∧
  (no_Old (BinOp _ e₀ e₁) ⇔
     no_Old e₀ ∧ no_Old e₁) ∧
  (no_Old (ArrLen arr) ⇔ no_Old arr) ∧
  (no_Old (ArrSel arr idx) ⇔ no_Old arr ∧ no_Old idx) ∧
  (no_Old (FunCall _ args) ⇔ EVERY (λe. no_Old e) args) ∧
  (no_Old (Forall _ term) ⇔ no_Old term) ∧
  (no_Old (Let binds body) ⇔
     EVERY (λe. no_Old e) (MAP SND binds) ∧ no_Old body) ∧
  (no_Old (ForallHeap mods e) ⇔
     EVERY (λe. no_Old e) mods ∧ no_Old e)
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_exp_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Inductive stmt_wp:
[~Skip:]
  ∀m ens post.
    stmt_wp m post Skip (post:exp list) (ens:exp list) decs
[~Assert:]
  ∀m ens post e.
    stmt_wp m (e::post) (Assert e) (post:exp list) (ens:exp list) decs
[~Return:]
  ∀m ens post.
    stmt_wp m (ens:exp list) Return (post:exp list) (ens:exp list) decs
[~Then:]
  ∀m s1 s2 pre1 pre2 post ens.
    stmt_wp m pre1 s1 pre2 ens decs ∧
    stmt_wp m pre2 s2 post ens decs
    ⇒
    stmt_wp m pre1 (Then s1 s2) post ens decs
[~If:]
  ∀m s1 s2 pre1 pre2 post ens g.
    stmt_wp m pre1 s1 post ens decs ∧
    stmt_wp m pre2 s2 post ens decs
    ⇒
    stmt_wp m [IsBool g; imp g (conj pre1); imp (not g) (conj pre2)]
      (If g s1 s2) post ens decs
[~Assign:]
  ∀m ret_names exps l post ens.
    (MAP FST l) = (MAP VarLhs ret_names) ∧
    (MAP SND l) = (MAP ExpRhs exps) ∧
    ALL_DISTINCT ret_names ∧
    LENGTH exps = LENGTH ret_names
    ⇒
    stmt_wp m ((Let (ZIP (ret_names,exps)) (conj post))::
               MAP (CanEval ∘ Var) ret_names) (Assign l) post ens decs
[~MetCall:]
  ∀m mname mspec mbody args ret_names rets post ens.
    Method mname mspec mbody ∈ m ∧
    LENGTH mspec.ins = LENGTH args ∧
    LENGTH mspec.outs = LENGTH rets ∧
    ALL_DISTINCT (MAP FST mspec.ins ++ MAP FST mspec.outs) ∧
    ALL_DISTINCT ret_names ∧
    rets = (MAP VarLhs ret_names) ∧
    EVERY (λe. DISJOINT (freevars e) (set ret_names)) args ∧
    EVERY (λe. freevars e ⊆ set (MAP FST mspec.ins) ∧ no_Old e) mspec.reqs ∧
    EVERY (λe. freevars e ⊆ set (MAP FST mspec.ins) ∧ no_Old e) mspec.decreases
    ⇒
    stmt_wp m (Let (ZIP (MAP FST mspec.ins,args)) (conj mspec.reqs) ::
               MAP CanEval args ++
               MAP CanEval (MAP Var ret_names) ++
               decreases_check (mspec.rank,
                                MAP (Let (ZIP (MAP FST mspec.ins,args))) mspec.decreases)
                               (wrap_old decs) ++
               [Foralls (ZIP (ret_names, MAP SND mspec.outs))
                  (imp (Let (ZIP(MAP FST mspec.ins ++ MAP FST mspec.outs,
                                 args              ++ MAP Var ret_names))
                          (conj mspec.ens))
                       (conj post))])
              (MetCall rets mname args) post ens decs
End

Definition proved_methods_def:
  proved_methods m ⇔
    ∀name mspec body.
      Method name mspec body ∈ m ⇒
      ∃wp_pre.
        stmt_wp m wp_pre body [False]
          (mspec.ens ++ MAP (CanEval o Var o FST) mspec.outs)
          (mspec.rank, mspec.decreases) ∧
        ⊢ (imp (conj mspec.reqs) (conj wp_pre))
End

(*
Inductive proved_methods:
[~empty:]
  proved_methods {}
[~nonrec:]
  ∀m body mspec wp_pre.
    proved_methods m ∧
    stmt_wp m wp_pre body [False] mspec.ens ∧
    ⊢ (imp (conj mspec.reqs) (conj wp_pre))
    ⇒
    proved_methods ((Method name mspec body) INSERT m)
[~mutrec:]
  ∀m mutrec.
    proved_methods m ∧
    (∀name mspec body.
       Method name mspec body ∈ mutrec ⇒
       ∃wp_pre.
         adjust_calls mspec.decreases mutrec body ∧
         stmt_wp (mutrec ∪ m) wp_pre body [False] mspec.ens ∧
         ⊢ (imp (conj mspec.reqs) (conj wp_pre)))
    ⇒
    proved_methods (mutrec ∪ m)
End
*)

Definition conditions_hold_def:
  conditions_hold st env ⇔ EVERY (eval_true st env)
End

Definition compatible_env_def:
  compatible_env env m ⇔
    ¬env.is_running ∧
    (∀name mspec body.
       Method name mspec body ∈ m ⇒
       get_member name env.prog =
       SOME (Method name mspec.ins mspec.reqs mspec.ens
                    mspec.reads mspec.decreases mspec.outs mspec.mods body))
End

Theorem imp_conditions_hold:
  ⊢ (imp (conj reqs) (conj wp_pre)) ∧
  conditions_hold st env reqs ⇒
  conditions_hold st env wp_pre
Proof
  rw [valid_def]
  \\ last_x_assum $ qspecl_then [‘st’,‘env’] mp_tac
  \\ gvs [conditions_hold_def]
  \\ strip_tac
  \\ drule eval_true_mp
  \\ gvs [eval_true_conj_every]
QED

Definition methods_sound_def:
  methods_sound m ⇔
    ∀name mspec body env.
      Method name mspec body ∈ m ⇒
      ∀st. conditions_hold st env mspec.reqs ∧ compatible_env env m ⇒
           ∃st'. eval_stmt st env body st' (Rstop Sret) ∧
                 conditions_hold st' env mspec.ens
End

Definition opt_lt_def:
  opt_lt (SOME m) (SOME n) = (m < n:num) ∧
  opt_lt _ _ = F
End

Triviality WF_lemma:
  WF (prim_rec$< LEX SHORTLEX opt_lt)
Proof
  irule pairTheory.WF_LEX
  \\ irule_at Any listTheory.WF_SHORTLEX
  \\ rewrite_tac [prim_recTheory.WF_LESS]
  \\ rewrite_tac [relationTheory.WF_EQ_INDUCTION_THM]
  \\ rw []
  \\ Cases_on ‘x’ \\ gvs []
  >- (pop_assum irule \\ Cases \\ gvs [opt_lt_def])
  \\ rename [‘SOME n’]
  \\ completeInduct_on ‘n’
  \\ last_x_assum irule
  \\ Cases \\ gvs [opt_lt_def]
QED

Triviality WF_ind =
  MATCH_MP relationTheory.WF_INDUCTION_THM WF_lemma;

Definition evaluate_exp_total_def:
  evaluate_exp_total st env e =
    some v. eval_exp st env e v
End

Definition evaluate_exp_num_def:
  evaluate_exp_num st env e =
    case evaluate_exp_total st env e of
    | SOME (IntV i) => (if i < 0 then NONE else SOME (Num i))
    | _ => NONE
End

Definition eval_decreases_def:
  eval_decreases st env es = MAP (evaluate_exp_num st env) es
End

Definition eval_measure_def:
  eval_measure st env (rank:num,es) =
    (rank, eval_decreases st env es)
End

Theorem False_thm[simp,local]:
  conditions_hold st env [False] = F
Proof
  simp [conditions_hold_def,eval_true_def,evaluate_exp_def,eval_exp_def]
QED

Triviality conditions_hold_cons:
  conditions_hold st env (e::es) ⇔
  eval_true st env e ∧ conditions_hold st env es
Proof
  gvs [conditions_hold_def]
QED

Triviality eval_decreases_old_eq:
  ∀es st st₁ env.
    st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ⇒
    eval_decreases st₁ env (MAP Old es) =
    eval_decreases st env (MAP Old es)
Proof
  Induct
  >- (simp [eval_decreases_def])
  \\ rpt gen_tac \\ strip_tac
  \\ last_x_assum drule_all
  \\ disch_then $ qspec_then ‘env’ assume_tac
  \\ fs [eval_decreases_def]
  \\ simp [evaluate_exp_num_def]
  \\ simp [evaluate_exp_total_def]
  \\ drule_all eval_exp_old_eq \\ gvs []
QED

Triviality Rcont_eval_measure:
  eval_stmt st env stmt st₁ Rcont ⇒
  eval_measure st₁ env (wrap_old decs) =
  eval_measure st env (wrap_old decs)
Proof
  strip_tac
  \\ imp_res_tac eval_stmt_Rcont_old
  \\ namedCases_on ‘decs’ ["rank es"]
  \\ simp [wrap_old_def, eval_measure_def]
  \\ DEP_REWRITE_TAC [eval_decreases_old_eq]
  \\ simp []
QED

Triviality conditions_hold_imp_case_split:
  conditions_hold st env [IsBool a; imp a b; imp (not a) c] ⇒
  conditions_hold st env [a] ∧ conditions_hold st env [b] ∨
  conditions_hold st env [not a] ∧ conditions_hold st env [c]
Proof
  strip_tac
  \\ gvs [conditions_hold_def]
  \\ imp_res_tac eval_true_imp
  \\ imp_res_tac eval_true_isbool_cases
  \\ gvs []
QED

Theorem conditions_hold_sing_conj[simp]:
  conditions_hold st env [conj xs] =
  conditions_hold st env xs
Proof
  Induct_on ‘xs’ \\ gvs [conditions_hold_def]
  \\ qx_gen_tac ‘x’
  \\ rewrite_tac [eval_true_cons] \\ simp []
QED

Triviality LIST_REL_eval_exp_MAP_Var:
  ∀ns vs.
    LIST_REL (eval_exp st env) (MAP Var ns) vs ⇒
    OPT_MMAP (read_local st.locals) ns = SOME vs
Proof
  Induct \\ Cases_on ‘vs’ \\ gvs []
  \\ gvs [eval_exp_def,evaluate_exp_def,AllCaseEqs(),PULL_EXISTS]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_False[simp]:
  ~eval_true st env False
Proof
  simp [eval_true_def,eval_exp_def,evaluate_exp_def]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_le_0:
  eval_true st env (int_le (int_lit 0) x) ⇒
  ∃n. eval_exp st env x (IntV (&n))
Proof
  rpt strip_tac
  \\ gvs [eval_true_def, eval_exp_def, evaluate_exp_def, do_sc_def, do_bop_def,
          AllCaseEqs()]
  \\ rename [‘0 ≤ i’]
  \\ qexists ‘Num i’
  \\ DEP_REWRITE_TAC [iffRL INT_OF_NUM] \\ simp []
  \\ last_assum $ irule_at (Pos hd)
QED

(* TODO Move to dafny_eval_rel *)
Theorem IMP_evaluate_exp_num:
  eval_exp st env x (IntV (&n)) ⇒
  evaluate_exp_num st env x = SOME n
Proof
  rpt strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_num_def, evaluate_exp_total_def,
          PULL_EXISTS, AllCaseEqs()]
  \\ rename [‘evaluate_exp (_ with clock := ck)’]
  \\ qexists ‘&n’ \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac
    \\ disch_then $ qx_choosel_then [‘ck₁’, ‘ck₂’] assume_tac
    \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘ck₁’ assume_tac
    \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘ck’ assume_tac \\ gvs [])
  \\ last_x_assum $ irule_at (Pos hd)
QED

(* TODO Move to dafnyProps *)
Theorem do_cond_some_cases:
  do_cond v thn els = SOME branch ⇒
  v = BoolV T ∧ branch = thn ∨ v = BoolV F ∧ branch = els
Proof
  rpt strip_tac \\ gvs [oneline do_cond_def, AllCaseEqs()]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_If_IMP:
  eval_true st env (If b x y) ⇒
  eval_true st env (imp b x) ∧
  eval_true st env (imp (not b) y)
Proof
  simp [eval_true_def, eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’] \\ disch_tac
  \\ qrefinel [‘ck’, ‘_’, ‘ck’, ‘_’]
  \\ gvs [evaluate_exp_def]
  \\ namedCases_on ‘evaluate_exp (st with clock := ck) env b’ ["st₁ r₁"]
  \\ fs []
  \\ namedCases_on ‘r₁’ ["v", "err"] \\ fs []
  \\ namedCases_on ‘do_cond v x y’ ["", "branch"] \\ fs []
  \\ drule (cj 1 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck₂’ assume_tac \\ gvs []
  \\ imp_res_tac do_cond_some_cases
  \\ gvs [do_sc_def, do_bop_def, do_uop_def]
  \\ simp [state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_lt_IMP:
  eval_exp st env xi (IntV i) ∧
  eval_exp st env xj (IntV j) ∧
  eval_true st env (int_lt xi xj) ⇒
  i < j
Proof
  simp [eval_exp_def, eval_true_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’, ‘ck₅’]
  \\ strip_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂ + ck’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₄ + ck₂’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₄ + ck₁’ assume_tac
  \\ gvs [evaluate_exp_def, do_sc_def, do_bop_def]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_eq_int:
  eval_exp st env h1 (IntV i) ∧
  eval_exp st env h2 (IntV j) ⇒
  eval_exp st env (dfy_eq h1 h2) (BoolV (i = j))
Proof
  simp [eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’]
  \\ strip_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ qexists ‘ck + ck₂’
  \\ full_simp_tac std_ss [AC ADD_ASSOC ADD_COMM]
  \\ simp [evaluate_exp_def, do_sc_def, do_bop_def]
  \\ simp [state_component_equality]
QED

(* TODO keep triv; move to evaluate props *)
Triviality push_local_with_old:
  push_local (s with <|locals_old := l; heap_old := h|>) vn v =
  push_local s vn v with <|locals_old := l; heap_old := h|>
Proof
  gvs [push_local_def]
QED

(* TODO keep triv; move to evaluate props *)
Triviality push_locals_with_old:
  push_locals (s with <|locals_old := l; heap_old := h|>) binds =
  push_locals s binds with <|locals_old := l; heap_old := h|>
Proof
  gvs [push_locals_def]
QED

(* TODO move to evaluate props *)
Theorem evaluate_exp_no_old:
  (∀s env e s' r h l.
     evaluate_exp s env e = (s', r) ∧ no_Old e ⇒
     evaluate_exp (s with <| heap_old := h; locals_old := l |>) env e =
     (s' with <| heap_old := h; locals_old := l |>, r)) ∧
  (∀s env es s' r h l.
     evaluate_exps s env es = (s', r) ∧ EVERY (λe. no_Old e) es ⇒
     evaluate_exps (s with <| heap_old := h; locals_old := l |>) env es =
     (s' with <| heap_old := h; locals_old := l |>, r))
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Forall (vn,vt) e’] >-
   (qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def, eval_forall_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [push_local_with_old, no_Old_def]
    \\ ‘∀v. SND (evaluate_exp
                   (push_local s vn v with <|locals_old := l; heap_old := h|>) env e) =
            SND (evaluate_exp (push_local s vn v) env e)’ by
      (gen_tac
       \\ namedCases_on ‘evaluate_exp (push_local s vn v) env e’ ["s₁ r₁"]
       \\ last_x_assum drule \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >- (rpt strip_tac \\ gvs [AllCaseEqs()]
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >- (* Type error *)
     (rpt strip_tac \\ gvs []
      \\ gvs [AllCaseEqs()]
      \\ first_assum $ irule_at $ Pos hd \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >- (* Timeout *)
     (rpt strip_tac \\ gvs [] \\ gvs [AllCaseEqs()])
    \\ IF_CASES_TAC \\ gvs []
    >- (* True *)
     (rpt strip_tac \\ gvs [] \\ gvs [AllCaseEqs()])
    (* False *)
    \\ rpt strip_tac \\ gvs [] \\ gvs [AllCaseEqs()]
    \\ first_assum $ irule_at (Pos hd) \\ gvs [])
  >~ [‘ForallHeap mods e’] >-
   (qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [no_Old_def]
    \\ namedCases_on ‘evaluate_exps s env mods’ ["s₁ r₁"] \\ gvs []
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ namedCases_on ‘get_locs vs’ ["", "locs"] \\ gvs []
    \\ rewrite_tac [GSYM AND_IMP_INTRO]
    \\ disch_then $ SUBST_ALL_TAC o GSYM
    \\ simp [eval_forall_def]
    \\ ‘∀hs.
          SND (evaluate_exp
                 (s₁ with <|heap := hs; locals_old := l; heap_old := h|>) env e)
          = SND (evaluate_exp (s₁ with heap := hs) env e)’ by
      (gen_tac
       \\ namedCases_on ‘evaluate_exp (s₁ with heap := hs) env e’ ["s₂ r₁"]
       \\ last_x_assum drule \\ gvs [])
    \\ gvs [])
  >~ [‘Let vars e’] >-
   (gvs [evaluate_exp_def, UNZIP_MAP, no_Old_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env (MAP SND vars)’ ["s₁ r₁"] \\ gvs []
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ namedCases_on
       ‘evaluate_exp (push_locals s₁ (ZIP (MAP FST vars,vs))) env e’
         ["s₂ r₂"]
    \\ gvs [push_locals_with_old, pop_locals_def, AllCaseEqs()])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_exp_def, no_Old_def, AllCaseEqs()]
    \\ imp_res_tac do_cond_some_cases \\ gvs [])
  >~ [‘ArrSel arr idx’] >-
   (gvs [evaluate_exp_def, no_Old_def, index_array_def, AllCaseEqs()])
  >~ [‘FunCall name args’] >-
   (gvs [evaluate_exp_def, no_Old_def, set_up_call_def, restore_caller_def,
         AllCaseEqs()])
  \\ gvs [evaluate_exp_def, no_Old_def, AllCaseEqs()]
QED

(* TODO Keep triv; Move to dafny_eval_rel *)
Triviality eval_exp_no_old_lemma:
  no_Old e ∧ eval_exp st env e v ⇒
  eval_exp (st with <| heap_old := h; locals_old := l |>) env e v
Proof
  simp [eval_exp_def]
  \\ rpt strip_tac
  \\ drule_all (cj 1 evaluate_exp_no_old) \\ gvs []
  \\ disch_then $ irule_at (Pos hd)
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_exp_no_old:
  no_Old e ⇒
  eval_exp st env e v =
  eval_exp (st with <| heap_old := h; locals_old := l |>) env e v
Proof
  strip_tac
  \\ iff_tac >- (simp [eval_exp_no_old_lemma])
  \\ strip_tac
  \\ drule_all eval_exp_no_old_lemma
  \\ disch_then $ qspecl_then [‘st.locals_old’, ‘st.heap_old’] mp_tac
  \\ simp []
  \\ match_mp_tac EQ_IMPLIES
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp [state_component_equality]
QED

Theorem eval_exp_no_old_IMP:
  ∀h l.
    no_Old e ∧
    eval_exp (st with <| heap_old := h; locals_old := l |>) env e v ⇒
    eval_exp st env e v
Proof
  metis_tac [eval_exp_no_old]
QED

(* TODO keep triv; Move to dafny_eval_rel *)
Triviality pair_I:
  (λ(x,y). (x,y)) = I
Proof
  rewrite_tac [FUN_EQ_THM] \\ Cases \\ simp []
QED

Triviality map_lambda_pair_zip:
  LENGTH xs = LENGTH ys ⇒
  MAP (λ(var,val). (var,SOME val)) (ZIP (xs,ys)) = ZIP (xs,MAP SOME ys)
Proof
  rpt strip_tac
  \\ gvs [ZIP_MAP]
  \\ irule MAP_CONG \\ simp []
  \\ qx_gen_tac ‘xy’
  \\ Cases_on ‘xy’ \\ simp []
QED

Triviality eval_exp_val_eq:
  eval_exp st env e v ∧
  evaluate_exp (st with clock := ck) env e = (st', Rval v') ⇒
  v' = v
Proof
  simp [eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’] \\ strip_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ gvs []
QED

Triviality list_rel_eval_exp_vals_eq:
  LIST_REL (eval_exp st env) es vs ∧
  evaluate_exps (st with clock := ck) env es = (st', Rval vs') ⇒
  vs' = vs
Proof
  strip_tac
  \\ drule eval_exp_evaluate_exps
  \\ disch_then $ qx_choosel_then [‘ck₁’, ‘ck₂’] assume_tac
  \\ rev_dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ rev_dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck’ assume_tac
  \\ gvs []
QED

Triviality eval_exp_Let_lr:
  LIST_REL (eval_exp st env) args vs ∧
  LENGTH ns = LENGTH args
  ⇒
  eval_exp st env (Let (ZIP (ns,args)) e) v' ⇒
  eval_exp
    (st with locals := REVERSE (ZIP (ns,MAP SOME vs)) ++ st.locals) env e v'
Proof
  namedCases_on ‘args’ ["", "arg args"] >-
   (gvs [eval_exp_def, evaluate_exp_def, push_locals_def, pop_locals_def,
         safe_drop_def, pair_I])
  \\ strip_tac
  \\ namedCases_on ‘vs’ ["", "v vs'"] \\ gvs []
  \\ namedCases_on ‘ns’ ["", "n ns'"] \\ gvs []
  \\ simp [eval_exp_def, evaluate_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’]
  \\ IF_CASES_TAC \\ gvs []
  \\ rpt strip_tac
  \\ namedCases_on ‘evaluate_exp (st with clock := ck) env arg’ ["st₁ r₁"]
  \\ gvs []
  \\ drule (cj 1 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck₂’ assume_tac \\ gvs []
  \\ namedCases_on ‘r₁’ ["v₁", "err"] \\ gvs []
  \\ namedCases_on ‘evaluate_exps (st with clock := ck₂) env args'’ ["st₂ r₂"]
  \\ gvs []
  \\ drule (cj 2 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck₃’ assume_tac \\ gvs []
  \\ namedCases_on ‘r₂’ ["vs₁", "err"] \\ gvs []
  \\ imp_res_tac eval_exp_val_eq \\ gvs []
  \\ imp_res_tac list_rel_eval_exp_vals_eq \\ gvs []
  \\ namedCases_on
       ‘evaluate_exp (push_locals (st with clock := ck₃) ((n,v)::ZIP (ns',vs'))) env e’
       ["st₃ r₃"]
  \\ gvs []
  \\ drule (cj 1 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck₄’ assume_tac \\ gvs []
  \\ pop_assum mp_tac
  \\ simp [push_locals_def]
  \\ DEP_REWRITE_TAC [map_lambda_pair_zip] \\ simp []
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ strip_tac
  \\ qexistsl [‘ck₃’, ‘ck₄’] \\ gvs [AllCaseEqs()]
QED

Triviality eval_exp_Let_rl:
  LIST_REL (eval_exp st env) args vs ∧
  LENGTH ns = LENGTH args ∧
  ALL_DISTINCT ns ⇒
  eval_exp
  (st with locals := REVERSE (ZIP (ns,MAP SOME vs)) ++ st.locals) env e v'
  ⇒
  eval_exp st env (Let (ZIP (ns,args)) e) v'
Proof
  namedCases_on ‘args’ ["", "arg args'"] >-
   (gvs [eval_exp_def, evaluate_exp_def, push_locals_def, pop_locals_def,
         safe_drop_def, pair_I])
  \\ strip_tac
  \\ namedCases_on ‘vs’ ["", "v vs'"] \\ gvs []
  \\ namedCases_on ‘ns’ ["", "n ns'"] \\ gvs []
  \\ last_x_assum mp_tac
  \\ dxrule eval_exp_evaluate_exps
  \\ gvs [eval_exp_def, evaluate_exp_def, PULL_EXISTS, PULL_FORALL]
  \\ qx_genl_tac [‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’, ‘ck₅’]
  \\ rpt strip_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck + ck₄’ assume_tac
  \\ rev_dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃ + ck₄’ assume_tac
  \\ qexists ‘ck + ck₂ + ck₄’ \\ gvs []
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁ + ck₃’ assume_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ pop_assum mp_tac
  \\ simp [push_locals_def]
  \\ DEP_REWRITE_TAC [map_lambda_pair_zip] \\ simp []
  \\ imp_res_tac evaluate_exps_len_eq \\ simp []
  \\ strip_tac \\ gvs []
  \\ simp [AllCaseEqs()]
  \\ simp [pop_locals_def, safe_drop_def, ADD1, state_component_equality]
  \\ simp [DROP_APPEND]
QED

Theorem eval_exp_Let:
  LIST_REL (eval_exp st env) args vs ∧
  LENGTH ns = LENGTH args ∧
  ALL_DISTINCT ns
  ⇒
  eval_exp st env (Let (ZIP (ns,args)) e) v =
  eval_exp
    (st with locals := REVERSE (ZIP (ns,MAP SOME vs)) ++ st.locals) env e v
Proof
  rpt strip_tac \\ iff_tac \\ strip_tac
  >- (drule_all eval_exp_Let_lr \\ simp [])
  \\ drule_all eval_exp_Let_rl \\ simp []
QED

Triviality push_locals_with_locals:
  push_locals s xs with locals := l =
  s with locals := l
Proof
  gvs [push_locals_def]
QED

Triviality push_locals_zip:
  LENGTH xs = LENGTH ys ⇒
  push_locals s (ZIP (xs,ys)) =
  s with locals := REVERSE (ZIP (xs, MAP SOME ys)) ++ s.locals
Proof
  gvs [push_locals_def, map_lambda_pair_zip]
QED

Theorem evaluate_exp_freevars:
  (∀st env e st' r l2.
     (∀n. n ∈ freevars e ⇒ ALOOKUP st.locals n = ALOOKUP l2 n) ⇒
     evaluate_exp st env e = (st', r) ⇒
     evaluate_exp (st with locals := l2) env e = (st' with locals := l2, r)) ∧
  (∀st env es st' r l2.
     EVERY (λe. (∀n. n ∈ freevars e ⇒ ALOOKUP st.locals n = ALOOKUP l2 n)) es ⇒
     evaluate_exps st env es = (st', r) ⇒
     evaluate_exps (st with locals := l2) env es = (st' with locals := l2, r))
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Let binds body’] >-
   (gvs [evaluate_exp_def, freevars_def, UNZIP_MAP]
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exps st env (MAP SND binds)’ ["st₁ r₁"] \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ strip_tac \\ gvs []
    \\ last_x_assum $ qspec_then ‘l2’ mp_tac
    \\ impl_tac >- (simp [EVERY_MEM] \\ metis_tac [MEM_MAP])
    \\ strip_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp st₁'’
    \\ namedCases_on ‘evaluate_exp st₁' env body’ ["st₂ r₂"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ strip_tac \\ gvs []
    \\ simp [Abbr ‘st₁'’]
    \\ gvs [push_locals_with_locals]
    \\ imp_res_tac evaluate_exps_len_eq \\ gvs []
    \\ gvs [push_locals_zip]
    \\ qmatch_goalsub_abbrev_tac
         ‘evaluate_exp (_ with <| clock := _; locals := lcls |>)’
    \\ last_x_assum $ qspec_then ‘lcls’ mp_tac
    \\ simp [Abbr ‘lcls’]
    \\ impl_tac >-
     (rpt strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘ALOOKUP (xs ++ _)’
      \\ simp [ALOOKUP_APPEND]
      \\ Cases_on ‘ALOOKUP xs n’ \\ gvs []
      \\ last_x_assum irule
      \\ disj2_tac \\ simp [Abbr ‘xs’]
      \\ imp_res_tac evaluate_exps_len_eq
      \\ gvs [ALOOKUP_NONE, MAP_ZIP, MAP_REVERSE])
    \\ strip_tac \\ gvs []
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ simp [state_component_equality]
    \\ simp [DROP_APPEND])
  >~ [‘Forall (vn,vt) e’] >-
   (gvs [evaluate_exp_def, freevars_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ simp [eval_forall_def]
    \\ ‘∀v. SND (evaluate_exp (push_local (st with locals := l2) vn v) env e) =
            SND (evaluate_exp (push_local st vn v) env e)’ by
      (gen_tac
       \\ namedCases_on ‘evaluate_exp (push_local st vn v) env e’ ["s₁ r₁"]
       \\ gvs [snd_tuple]
       \\ last_x_assum $ drule_at (Pos last)
       \\ gvs [push_local_def])
    \\ gvs [])
  >~ [‘ForallHeap mods e’] >-
   (gvs [evaluate_exp_def, freevars_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exps st env mods’ ["st₁ r₁"] \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ strip_tac \\ gvs []
    \\ last_x_assum $ qspec_then ‘l2’ mp_tac
    \\ impl_tac >- (simp [EVERY_MEM] \\ metis_tac [MEM_MAP])
    \\ strip_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ namedCases_on ‘get_locs vs’ ["", "locs"] \\ gvs []
    \\ simp [eval_forall_def]
    \\ ‘∀hs. SND (evaluate_exp
                   (st with <|clock := ck; locals := l2; heap := hs|>) env e)
             = SND (evaluate_exp (st with <| clock := ck; heap := hs |>) env e)’
      by
      (gen_tac
       \\ namedCases_on
            ‘evaluate_exp (st with <|clock := ck; heap := hs|>) env e’ ["st₁ r₁"]
       \\ gvs [snd_tuple]
       \\ last_x_assum $ irule_at Any \\ gvs [])
    \\ gvs [])
  >~ [‘FunCall name args’] >-
   (gvs [evaluate_exp_def, freevars_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exps st env args’ ["st₁ r₁"] \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ strip_tac \\ gvs []
    \\ first_x_assum $ qspec_then ‘l2’ mp_tac
    \\ impl_tac >- (simp [EVERY_MEM] \\ metis_tac [MEM_MAP])
    \\ strip_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["in_vs", "err"] \\ gvs []
    \\ gvs [set_up_call_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [safe_zip_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    >- (gvs [restore_caller_def])
    \\ qmatch_goalsub_abbrev_tac ‘evaluate_exp st₁’
    \\ namedCases_on ‘evaluate_exp st₁ env e’ ["st₂ r₂"] \\ gvs []
    \\ Cases_on ‘r₂’ \\ gvs [restore_caller_def])
  >~ [‘If grd thn els’] >-
   (gvs [evaluate_exp_def, freevars_def]
    \\ namedCases_on ‘evaluate_exp st env grd’ ["st₁ r₁"] \\ gvs []
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ first_x_assum $ qspec_then ‘l2’ mp_tac
    \\ impl_tac >- (gvs [])
    \\ strip_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["v", "err"] \\ gvs []
    \\ namedCases_on ‘do_cond v thn els’ ["", "branch"] \\ gvs []
    \\ imp_res_tac do_cond_some_cases \\ gvs []
    \\ last_x_assum irule \\ gvs [])
  >~ [‘UnOp uop e’] >-
   (gvs [freevars_def, evaluate_exp_def, AllCaseEqs()])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [freevars_def, evaluate_exp_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
  >~ [‘ArrSel arr idx’] >-
   (gvs [evaluate_exp_def, freevars_def, index_array_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
  >~ [‘Old e’] >-
   (gvs [freevars_def, evaluate_exp_def, unuse_old_def, use_old_def,
         AllCaseEqs()])
  >~ [‘Var n’] >-
   (gvs [evaluate_exp_def, freevars_def, read_local_def, AllCaseEqs()])
  >~ [‘ArrLen arr’] >-
   (gvs [freevars_def, evaluate_exp_def, AllCaseEqs()])
  >~ [‘Lit l’] >-
   (gvs [evaluate_exp_def])
  >~ [‘[]’] >-
   (gvs [evaluate_exp_def])
  >~ [‘e::es’] >-
   (gvs [evaluate_exp_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
QED

Triviality eval_exp_freevars_lemma:
  (∀n. n ∈ freevars e ⇒ ALOOKUP l1 n = ALOOKUP l2 n) ⇒
  eval_exp (st with locals := l1) env e v ⇒
  eval_exp (st with locals := l2) env e v
Proof
  rpt strip_tac
  \\ qsuff_tac ‘eval_exp ((st with locals := l1) with locals := l2) env e v’
  >- (simp [])
  \\ gvs [eval_exp_def]
  \\ drule_at (Pos last) (cj 1 evaluate_exp_freevars) \\ simp []
  \\ disch_then $ irule_at Any \\ simp []
QED

Theorem eval_exp_freevars:
  (∀n. n ∈ freevars e ⇒ ALOOKUP l1 n = ALOOKUP l2 n) ⇒
  eval_exp (st with locals := l1) env e v =
  eval_exp (st with locals := l2) env e v
Proof
  strip_tac \\ iff_tac \\ metis_tac [eval_exp_freevars_lemma]
QED

Triviality eval_exp_swap_locals_alt_aux:
  ALOOKUP l' = ALOOKUP l ∧
  eval_exp (st with locals := l') env e v ⇒
  eval_exp (st with locals := l) env e v
Proof
  rpt strip_tac
  \\ ‘∀n. n ∈ freevars e ⇒ ALOOKUP l' n = ALOOKUP l n’ by (gvs [])
  \\ drule (iffLR eval_exp_freevars) \\ gvs []
QED

Theorem eval_exp_swap_locals_alt:
  ALOOKUP l' = ALOOKUP l ⇒
  eval_exp (st with locals := l') env e v =
  eval_exp (st with locals := l) env e v
Proof
  strip_tac \\ metis_tac [eval_exp_swap_locals_alt_aux]
QED

Theorem eval_exp_swap_locals:
  ALOOKUP st.locals = ALOOKUP l ⇒
  eval_exp st env e =
  eval_exp (st with locals := l) env e
Proof
  strip_tac
  \\ simp [FUN_EQ_THM] \\ strip_tac
  \\ iff_tac \\ strip_tac
  \\ metis_tac [with_same_locals, eval_exp_swap_locals_alt]
QED

Triviality ALOOKUP_MAP_SOME:
  ∀ns vs.
    LENGTH ns = LENGTH vs ⇒
    (ALOOKUP (ZIP (ns,MAP SOME vs)) n = SOME (SOME v) ⇔
     ALOOKUP (ZIP (ns,vs)) n = SOME v)
Proof
  Induct \\ Cases_on ‘vs’ \\ gvs [] \\ rw []
QED

Theorem eval_exp_Let_equiv:
  LIST_REL (eval_exp st env) args vs ∧
  ALL_DISTINCT ns ∧
  LENGTH ns = LENGTH args ∧
  LENGTH ns = LENGTH vs ∧
  (∀n. n ∈ freevars e ⇒ ∃v. ALOOKUP l n = SOME (SOME v) ∧
                            ALOOKUP (ZIP (ns,vs)) n = SOME v)
  ⇒
  eval_exp st env (Let (ZIP (ns,args)) e) v =
  eval_exp (st with locals := l) env e v
Proof
  strip_tac
  \\ irule EQ_TRANS
  \\ irule_at (Pos hd) eval_exp_Let
  \\ last_x_assum $ irule_at Any \\ fs []
  \\ irule eval_exp_freevars \\ rw []
  \\ simp [ALOOKUP_APPEND,CaseEq"option"]
  \\ disj2_tac
  \\ res_tac \\ gvs []
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
  \\ gvs [MAP_ZIP]
  \\ gvs [ALOOKUP_MAP_SOME]
QED

Theorem eval_true_lex_lt:
  ∀xs ys.
    eval_true st env (lex_lt (ZIP (xs,ys))) ∧ LENGTH xs = LENGTH ys ⇒
    SHORTLEX opt_lt (eval_decreases st env xs) (eval_decreases st env ys)
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [lex_lt_def] \\ rw []
  \\ gvs [eval_decreases_def,eval_true_conj_every]
  \\ imp_res_tac eval_true_le_0
  \\ imp_res_tac IMP_evaluate_exp_num \\ gvs [opt_lt_def]
  \\ rename [‘m < k’]
  \\ drule eval_true_If_IMP \\ strip_tac
  \\ imp_res_tac eval_true_imp
  \\ rename [‘(dfy_eq h1 h2)’]
  \\ ‘eval_exp st env (dfy_eq h1 h2) (BoolV (m = k))’ by
    (imp_res_tac eval_true_eq_int \\ gvs [])
  \\ imp_res_tac eval_exp_bool_not
  \\ Cases_on ‘m = k’ >- gvs [GSYM eval_true_def]
  \\ gvs [GSYM eval_true_def]
  \\ drule_all eval_true_lt_IMP
  \\ gvs []
QED

Theorem eval_true_forall_foralls:
  eval_true st env (Forall (vn,vt) (Foralls vars b)) ∧ v ∈ all_values vt ⇒
  eval_true (st with locals := (vn, SOME v)::st.locals) env (Foralls vars b)
Proof
  strip_tac
  \\ qpat_x_assum ‘eval_true _ _ _’ mp_tac
  \\ simp [eval_true_def, eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’]
  \\ simp [evaluate_exp_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ simp [state_component_equality]
  \\ simp [GSYM AND_IMP_INTRO]
  \\ strip_tac \\ gvs []
  \\ simp [eval_forall_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ first_x_assum drule
  \\ simp [snd_tuple, push_local_def]
  \\ strip_tac
  \\ imp_res_tac evaluate_exp_with_clock
  \\ gvs []
  \\ first_assum $ irule_at (Pos hd)
QED

Theorem eval_true_Foralls:
  ∀vars st env b.
    eval_true st env (Foralls vars b) ⇒
    ∀xs.
      LIST_REL (λ(n,ty) (m,x). m = n ∧ ∃v. v ∈ all_values ty ∧ x = SOME v) vars xs ⇒
      eval_true (st with locals := REVERSE xs ++ st.locals) env b
Proof
  Induct >- (gvs [Foralls_def])
  \\ qx_genl_tac [‘var’, ‘st’, ‘env’, ‘b’]
  \\ rpt strip_tac
  \\ namedCases_on ‘var’ ["vn vt"]
  \\ namedCases_on ‘xs’ ["", "x xs'"]
  \\ gvs [Foralls_def]
  \\ namedCases_on ‘x’ ["xn xt"] \\ gvs []
  \\ drule_all eval_true_forall_foralls
  \\ strip_tac
  \\ last_x_assum drule_all \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Triviality alookup_distinct_reverse_append:
  ALL_DISTINCT (MAP FST xs) ⇒
  ALOOKUP (REVERSE xs ++ ys) = ALOOKUP (xs ++ ys)
Proof
  strip_tac
  \\ irule ALOOKUP_APPEND_same
  \\ simp [FUN_EQ_THM]
  \\ simp [alookup_distinct_reverse]
QED

Triviality eval_true_with_locals_reverse:
  ALL_DISTINCT (MAP FST xs) ⇒
  eval_true (st with locals := REVERSE xs ++ st.locals) env e =
  eval_true (st with locals := xs ++ st.locals) env e
Proof
  strip_tac
  \\ simp [eval_true_def]
  \\ ‘ALOOKUP (REVERSE xs ++ st.locals) = ALOOKUP (xs ++ st.locals)’ by
    (gvs [alookup_distinct_reverse_append])
  \\ drule eval_exp_swap_locals_alt \\ gvs []
QED

Triviality list_rel_locals_map_fst:
  ∀ns xs.
    LIST_REL
      (λ(n,ty) (m,x). m = n ∧ ∃v. v ∈ all_values ty ∧ x = SOME v) ns xs ⇒
    MAP FST ns = MAP FST xs
Proof
  Induct \\ gvs []
  \\ Cases_on ‘xs’ \\ gvs []
  \\ rpt strip_tac \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality eval_true_Foralls_distinct:
  eval_true st env (Foralls ns b) ∧ ALL_DISTINCT (MAP FST ns) ⇒
  ∀xs.
    LIST_REL (λ(n,ty) (m,x). m = n ∧ ∃v. v ∈ all_values ty ∧ x = SOME v) ns xs ⇒
    eval_true (st with locals := xs ++ st.locals) env b
Proof
  rpt strip_tac
  \\ drule eval_true_Foralls
  \\ rpt strip_tac
  \\ first_x_assum $ qspec_then ‘xs’ mp_tac \\ gvs []
  \\ DEP_REWRITE_TAC [eval_true_with_locals_reverse]
  \\ imp_res_tac list_rel_locals_map_fst \\ gvs []
QED

Definition assi_value_def:
  assi_value st env lhs rhs st' ⇔
    ∃ck1 ck2.
      assign_value (st with clock := ck1) env lhs rhs =
      (st' with clock := ck2,Rcont)
End

Theorem can_eval_var_update_local:
  eval_true st env (CanEval (Var n)) ⇒
  ∃l. update_local st n v = SOME (st with locals := l) ∧
      ALOOKUP l = ALOOKUP ((n, SOME v)::st.locals)
Proof
  cheat
QED

Theorem can_eval_vars:
  EVERY (eval_true st env) (MAP CanEval (MAP Var ns)) ∧
  (∀n. IS_SOME (ALOOKUP st.locals n) ⇒ IS_SOME (ALOOKUP l n)) ⇒
  EVERY (eval_true (st' with locals := l) env) (MAP CanEval (MAP Var ns))
Proof
  cheat
QED

Theorem assi_value_VarLhs:
  update_local st n v = SOME st' ⇒ assi_value st env (VarLhs n) v st'
Proof
  simp [assi_value_def, assign_value_def, update_local_def,
        state_component_equality, AllCaseEqs()]
QED

Theorem assi_values_cons:
  (∃st₁.
    assi_value st env var val st₁ ∧ assi_values st₁ env vars vals st') ⇒
    assi_values st env (var::vars) (val::vals) st'
Proof
  simp [assi_value_def, assi_values_def, PULL_EXISTS]
  \\ qx_genl_tac [‘st₁’, ‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’]
  \\ rpt strip_tac
  \\ dxrule assign_value_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ dxrule assign_values_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ qexists ‘ck + ck₂’
  \\ gvs [assign_values_def, state_component_equality]
QED

Triviality ALOOKUP_APPEND_same_tail:
  ALOOKUP ys = ALOOKUP zs ⇒ ALOOKUP (xs ++ ys) = ALOOKUP (xs ++ zs)
Proof
  simp [FUN_EQ_THM, ALOOKUP_APPEND]
QED

Theorem IMP_assi_values:
  ∀ret_names out_vs st.
    EVERY (eval_true st env) (MAP CanEval (MAP Var ret_names)) ∧
    LENGTH out_vs = LENGTH ret_names
    ⇒
    ∃l. assi_values st env (MAP VarLhs ret_names) out_vs (st with locals := l) ∧
        ALOOKUP l = ALOOKUP (REVERSE (ZIP(ret_names,MAP SOME out_vs)) ++ st.locals)
Proof
  Induct >-
   (gvs [assi_values_def, assign_values_def, state_component_equality])
  \\ qx_genl_tac [‘n’, ‘out_vs’, ‘st’]
  \\ rpt strip_tac
  \\ namedCases_on ‘out_vs’ ["", "v out_vs'"] \\ gvs []
  \\ irule_at (Pos hd) assi_values_cons
  \\ drule can_eval_var_update_local
  \\ disch_then $ qspec_then ‘v’ mp_tac
  \\ disch_then $ qx_choose_then ‘l’ mp_tac
  \\ strip_tac
  \\ irule_at (Pos hd) assi_value_VarLhs
  \\ first_assum $ irule_at (Pos hd)
  \\ drule can_eval_vars
  \\ disch_then $ qspecl_then [‘st’, ‘l’] mp_tac
  \\ impl_tac >-
   (strip_tac \\ simp [ALOOKUP_def] \\ IF_CASES_TAC \\ gvs [])
  \\ strip_tac
  \\ last_x_assum drule_all \\ simp []
  \\ disch_then $ qx_choose_then ‘l₁’ mp_tac
  \\ strip_tac
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ irule ALOOKUP_APPEND_same_tail \\ simp []
QED

Triviality IMP_assi_values_distinct:
  ∀ret_names out_vs st.
    EVERY (eval_true st env) (MAP CanEval (MAP Var ret_names)) ∧
    ALL_DISTINCT ret_names ∧ LENGTH out_vs = LENGTH ret_names
    ⇒
    ∃l. assi_values st env (MAP VarLhs ret_names) out_vs (st with locals := l) ∧
        ALOOKUP l = ALOOKUP (ZIP(ret_names,MAP SOME out_vs) ++ st.locals)
Proof
  rpt strip_tac
  \\ drule_all IMP_assi_values
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse_append]
  \\ simp [MAP_ZIP]
QED

Theorem IN_freevars_conj:
  ∀xs n. n ∈ freevars (conj xs) ⇒ ∃x. MEM x xs ∧ n ∈ freevars x
Proof
  ho_match_mp_tac conj_ind \\ rw [conj_def] \\ fs [freevars_def]
  \\ simp [SF DNF_ss]
  \\ res_tac \\ gvs [] \\ metis_tac []
QED

Theorem no_Old_conj:
  ∀xs. no_Old (conj xs) = EVERY no_Old xs
Proof
  ho_match_mp_tac conj_ind \\ rw [conj_def] \\ fs [no_Old_def]
QED

Theorem value_same_type_refl:
  ∀x. value_same_type x x
Proof
  Cases \\ simp [value_same_type_def]
QED

Theorem eval_true_CanEval_Var:
  eval_true st env (CanEval (Var v)) ⇔ ∃val. ALOOKUP st.locals v = SOME (SOME val)
Proof
  fs [eval_true_def,eval_exp_def,evaluate_exp_def,CanEval_def,read_local_def]
  \\ simp [AllCaseEqs(),PULL_EXISTS,do_sc_def,do_bop_def]
  \\ simp [state_component_equality,SF CONJ_ss,value_same_type_refl]
QED

Theorem eval_true_Let_IMP:
  eval_true st env (Let (ZIP (ns,exps)) p) ∧ LENGTH exps = LENGTH ns ⇒
  ∃vs. LIST_REL (eval_exp st env) exps vs
Proof
  cheat
QED

Theorem IMP_eval_rhs_exps_MAP_ExpRhs:
  LIST_REL (eval_exp st env) exps vs ⇒
  eval_rhs_exps st env (MAP ExpRhs exps) st vs
Proof
  cheat
QED

Theorem stmt_wp_sound:
  ∀m reqs stmt post ens decs.
    stmt_wp m reqs stmt post ens decs ⇒
    ∀st env.
      (∀st' name' mspec' body'.
          ($< LEX SHORTLEX opt_lt)
            (eval_measure st' env (mspec'.rank,mspec'.decreases))
            (eval_measure st env (wrap_old decs)) ∧
          Method name' mspec' body' ∈ m ∧ st'.locals_old = st'.locals ∧
          st'.heap_old = st'.heap ∧ conditions_hold st' env mspec'.reqs ∧
          compatible_env env m ⇒
          ∃st'' out_vs.
            eval_stmt st' env body' st'' (Rstop Sret) ∧
            conditions_hold st'' env mspec'.ens ∧
            LIST_REL (eval_exp st'' env) (MAP (Var o FST) mspec'.outs) out_vs) ∧
      conditions_hold st env reqs ∧ compatible_env env m ⇒
      ∃st' ret.
        eval_stmt st env stmt st' ret ∧
        case ret of
        | Rstop Sret => conditions_hold st' env ens
        | Rcont => conditions_hold st' env post
        | _ => F
Proof
  Induct_on ‘stmt_wp’ \\ rpt strip_tac
  >~ [‘Skip’] >-
   (irule_at (Pos hd) eval_stmt_Skip \\ simp [])
  >~ [‘Assert e’] >-
   (irule_at (Pos hd) eval_stmt_Assert \\ simp []
    \\ gvs [conditions_hold_cons])
  >~ [‘Return’] >-
   (irule_at (Pos hd) eval_stmt_Return \\ simp [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (last_x_assum drule \\ simp []
    \\ disch_then $ qx_choosel_then [‘st₁’, ‘ret₁’] mp_tac
    \\ strip_tac
    \\ reverse $ namedCases_on ‘ret₁’ ["", "stp"] \\ gvs []
    >-
     (Cases_on ‘stp’ \\ gvs []
      (* First statement has returned *)
      \\ irule_at (Pos hd) eval_stmt_Then_ret
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    \\ last_x_assum $ drule_at (Pos last)
    \\ disch_then $ drule_at (Pos last)
    \\ imp_res_tac Rcont_eval_measure \\ gvs []
    \\ impl_tac >- (gvs [])
    \\ disch_then $ qx_choosel_then [‘st₂’, ‘ret₂’] mp_tac
    \\ strip_tac
    \\ reverse $ namedCases_on ‘ret₂’ ["", "stp"] \\ gvs []
    >-
     (Cases_on ‘stp’ \\ gvs []
      (* Second statement has returned *)
      \\ irule_at (Pos hd) eval_stmt_Then_cont_ret
      \\ first_assum $ irule_at (Pos hd) \\ simp []
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    (* Both statements continued *)
    \\ irule_at (Pos hd) eval_stmt_Then_cont
    \\ first_assum $ irule_at (Pos hd) \\ simp []
    \\ first_assum $ irule_at (Pos hd) \\ simp [])
  >~ [‘If grd thn els’] >-
   (dxrule conditions_hold_imp_case_split \\ strip_tac \\ gvs []
    >- (* Execute thn branch *)
     (last_x_assum $ drule_at (Pos $ el 2) \\ simp []
      \\ impl_tac >- (gvs [])
      \\ disch_then $ qx_choosel_then [‘st₁’, ‘ret₁’] mp_tac
      \\ strip_tac
      \\ irule_at (Pos hd) eval_stmt_If_thn
      \\ gvs [conditions_hold_def]
      \\ first_assum $ irule_at (Pos hd) \\ simp []
      \\ namedCases_on ‘ret₁’ ["", "err"] \\ gvs []
      \\ Cases_on ‘err’ \\ gvs [])
    (* Execute els branch *)
    \\ last_x_assum $ drule_at (Pos $ el 2) \\ simp []
    \\ impl_tac >- (gvs [])
    \\ disch_then $ qx_choosel_then [‘st₁’, ‘ret₁’] mp_tac
    \\ strip_tac
    \\ irule_at (Pos hd) eval_stmt_If_els
    \\ gvs [conditions_hold_def]
    \\ first_assum $ irule_at (Pos hd) \\ simp []
    \\ namedCases_on ‘ret₁’ ["", "err"] \\ gvs []
    \\ Cases_on ‘err’ \\ gvs [])
  >~ [‘Assign ass’] >-
   (irule_at (Pos hd) eval_stmt_Assign \\ simp []
    \\ qpat_x_assum ‘∀x._’ kall_tac
    \\ fs [conditions_hold_def]
    \\ drule eval_true_Let_IMP \\ simp []
    \\ strip_tac
    \\ irule_at Any IMP_eval_rhs_exps_MAP_ExpRhs
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [GSYM MAP_MAP_o]
    \\ drule IMP_assi_values
    \\ disch_then $ qspec_then ‘vs’ mp_tac
    \\ imp_res_tac LIST_REL_LENGTH
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd
    \\ simp [eval_true_def,GSYM eval_true_conj_every]
    \\ irule $ iffLR eval_exp_freevars
    \\ qexists_tac ‘ZIP (ret_names,MAP SOME vs) ++ st.locals’
    \\ conj_tac
    >- (rpt strip_tac \\ gvs []
        \\ irule $ SRULE [FUN_EQ_THM] ALOOKUP_APPEND_same
        \\ strip_tac
        \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
        \\ simp [MAP_ZIP])
    \\ qpat_x_assum ‘eval_true st env (Let _ _)’ mp_tac
    \\ simp [eval_true_def]
    \\ strip_tac
    \\ drule_at (Pos last) eval_exp_Let_lr
    \\ disch_then drule
    \\ impl_tac >- simp []
    \\ match_mp_tac EQ_IMPLIES
    \\ match_mp_tac eval_exp_freevars
    \\ simp [ALOOKUP_APPEND] \\ rw []
    \\ DEP_REWRITE_TAC [alistTheory.alookup_distinct_reverse]
    \\ simp [MAP_ZIP])
  \\ rename [‘MetCall rets mname args’]
  \\ irule_at Any eval_stmt_MetCall \\ gvs []
  \\ qpat_assum ‘compatible_env env m’ mp_tac
  \\ rewrite_tac [compatible_env_def]
  \\ strip_tac
  \\ pop_assum drule
  \\ strip_tac \\ gvs []
  \\ gvs [conditions_hold_def]
  \\ qpat_x_assum ‘EVERY (eval_true st env) (MAP CanEval args)’ assume_tac
  \\ drule EVERY_eval_true_CanEval \\ strip_tac
  \\ first_assum $ irule_at Any
  \\ gvs [set_up_call_def]
  \\ simp [safe_zip_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ qpat_abbrev_tac ‘new_l = REVERSE _’
  \\ qmatch_goalsub_abbrev_tac ‘eval_stmt st1’
  \\ first_x_assum $ drule_at $ Pos $ el 2
  \\ disch_then $ qspec_then ‘st1’ mp_tac
  \\ impl_tac
  >-
   (reverse $ rpt conj_tac
    >-
     (rewrite_tac [GSYM eval_true_conj_every]
      \\ qpat_x_assum ‘eval_true st env (Let _ (conj mspec.reqs))’ mp_tac
      \\ rewrite_tac [eval_true_def]
      \\ strip_tac
      \\ irule eval_exp_no_old_IMP
      \\ conj_tac >-
       (simp [no_Old_conj,EVERY_MEM] \\ rw [] \\ fs [EVERY_MEM] \\ res_tac)
      \\ qexists_tac ‘st.heap_old’
      \\ qexists_tac ‘st.locals_old’
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC [eval_exp_Let_equiv |> Q.INST [‘l’|->‘new_l’,‘vs’|->‘in_vs’]]
      \\ fs [Abbr‘st1’]
      \\ conj_tac
      >- (fs [ALL_DISTINCT_APPEND] \\ rw []
          \\ drule IN_freevars_conj \\ strip_tac
          \\ fs [EVERY_MEM]
          \\ first_x_assum drule
          \\ simp [SUBSET_DEF,MEM_MAP,EXISTS_PROD]
          \\ strip_tac
          \\ first_x_assum drule \\ strip_tac
          \\ unabbrev_all_tac
          \\ rewrite_tac [REVERSE_APPEND]
          \\ simp [ALOOKUP_APPEND,CaseEq"option"]
          \\ simp [SF DNF_ss] \\ disj1_tac
          \\ simp [MEM_MAP,FORALL_PROD]
          \\ DEP_REWRITE_TAC [alistTheory.alookup_distinct_reverse]
          \\ simp [MAP_ZIP,ALOOKUP_MAP_SOME,SF CONJ_ss]
          \\ simp [GSYM PULL_EXISTS]
          \\ conj_tac >-
           (DEP_REWRITE_TAC [ALOOKUP_ZIP_FAIL] \\ gvs []
            \\ last_x_assum irule
            \\ fs [MEM_MAP,EXISTS_PROD]
            \\ first_x_assum $ irule_at Any)
          \\ qpat_abbrev_tac ‘opt = ALOOKUP _ n’
          \\ Cases_on ‘opt’ \\ gvs []
          \\ pop_assum mp_tac
          \\ simp [ALOOKUP_NONE, MAP_ZIP]
          \\ fs [MEM_MAP,EXISTS_PROD]
          \\ first_x_assum $ irule_at Any)
      \\ match_mp_tac EQ_IMPLIES
      \\ rpt AP_THM_TAC \\ AP_TERM_TAC
      \\ simp [state_component_equality])
    >- gvs [Abbr‘st1’]
    >- gvs [Abbr‘st1’]
    \\ PairCases_on ‘decs’ \\ gvs [wrap_old_def]
    \\ qpat_x_assum ‘EVERY _ (decreases_check _ _)’ mp_tac
    \\ simp [decreases_check_def]
    \\ Cases_on ‘mspec.rank ≠ decs0’ \\ simp []
      >-
       (‘mspec.rank < decs0 ∨ decs0 < mspec.rank’ by decide_tac
        \\ simp [LEX_DEF,eval_measure_def]
        \\ simp [eval_true_def,eval_exp_def,evaluate_exp_def])
    \\ gvs [eval_measure_def,LEX_DEF]
    \\ simp [decrease_lt_def]
    \\ reverse $ rw []
    >- (irule listTheory.LENGTH_LT_SHORTLEX
        \\ gvs [eval_decreases_def])
    \\ drule eval_true_lex_lt
    \\ simp []
    \\ qsuff_tac
       ‘eval_decreases st1 env mspec.decreases =
        eval_decreases st env
                       (MAP (Let (ZIP (MAP FST mspec.ins,args))) mspec.decreases)’
    >- simp []
    \\ simp [eval_decreases_def]
    \\ simp [MAP_MAP_o,MAP_EQ_f] \\ rw []
    \\ gvs [evaluate_exp_num_def,evaluate_exp_total_def]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ simp [FUN_EQ_THM]
    \\ gen_tac
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ irule EQ_TRANS
    \\ irule_at (Pos hd) eval_exp_Let_equiv
    \\ first_x_assum $ irule_at $ Pos hd
    \\ simp [] \\ fs [ALL_DISTINCT_APPEND]
    \\ qexists_tac ‘new_l’
    \\ reverse conj_tac
    >- (irule EQ_TRANS
        \\ irule_at (Pos hd) eval_exp_no_old
        \\ qexistsl [‘new_l’,‘st.heap’]
        \\ fs [EVERY_MEM] \\ res_tac \\ simp [])
    \\ rw []
    \\ ‘MEM n (MAP FST mspec.ins)’ by
      (fs [EVERY_MEM,SUBSET_DEF] \\ res_tac \\ simp [])
    \\ unabbrev_all_tac
    \\ simp [REVERSE_APPEND,ALOOKUP_APPEND]
    \\ gvs [CaseEq"option"]
    \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
    \\ simp [ALOOKUP_NONE,MAP_ZIP]
    \\ fs [ALOOKUP_MAP_SOME]
    \\ pop_assum mp_tac
    \\ qpat_x_assum ‘LENGTH mspec.ins = LENGTH in_vs’ mp_tac
    \\ qid_spec_tac ‘in_vs’
      \\ qspec_tac (‘mspec.ins’,‘xs’)
    \\ Induct_on ‘xs’ \\ gvs [] \\ gen_tac
    \\ Cases \\ gvs [] \\ rw [] \\ gvs [])
  \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ fs [GSYM MAP_MAP_o]
  \\ drule LIST_REL_eval_exp_MAP_Var
  \\ disch_then $ irule_at Any
  \\ drule LIST_REL_LENGTH \\ strip_tac \\ fs []
  \\ gvs [GSYM conditions_hold_def]
  \\ drule eval_true_Foralls_distinct
  \\ simp [MAP_ZIP] \\ strip_tac
  \\ gvs [conditions_hold_def]
  \\ rename [‘restore_caller st2 st’]
  \\ qabbrev_tac ‘st3 = restore_caller st2 st’
  \\ ‘EVERY (eval_true st3 env) (MAP CanEval (MAP Var ret_names))’ by
   (qpat_x_assum ‘EVERY _ (MAP CanEval (MAP Var ret_names))’ mp_tac
    \\ simp [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ rpt strip_tac \\ first_x_assum dxrule
    \\ simp [eval_true_CanEval_Var,Abbr‘st3’,restore_caller_def])
  \\ drule IMP_assi_values_distinct
  \\ disch_then $ qspec_then ‘out_vs’ mp_tac
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ rewrite_tac [GSYM eval_true_conj_every]
  \\ rewrite_tac [eval_true_def]
  \\ irule (iffLR eval_exp_swap_locals_alt)
  \\ pop_assum $ irule_at Any o GSYM
  \\ cheat
QED

Triviality evaluate_exp_total_old:
  st.locals_old = st.locals ∧ st.heap_old = st.heap ∧ ¬env.is_running ⇒
  evaluate_exp_total st env (Old e) = evaluate_exp_total st env e
Proof
  rpt strip_tac
  \\ simp [evaluate_exp_total_def, eval_exp_old_eq_not_old]
QED

Triviality eval_decreases_map_old:
  ∀es st env.
    st.locals_old = st.locals ∧ st.heap_old = st.heap ∧ ¬env.is_running ⇒
    eval_decreases st env (MAP Old es) = eval_decreases st env es
Proof
  Induct \\ gvs []
  \\ simp [eval_decreases_def, evaluate_exp_total_old,
           evaluate_exp_num_def,MAP_MAP_o,MAP_EQ_f]
QED

Theorem eval_measure_wrap_old:
  st.locals_old = st.locals ∧ st.heap_old = st.heap ∧ ¬env.is_running ⇒
  eval_measure st env (wrap_old decs) =
  eval_measure st env decs
Proof
  rpt strip_tac
  \\ namedCases_on ‘decs’ ["rank es"]
  \\ simp [wrap_old_def, eval_measure_def, eval_decreases_map_old]
QED

Theorem methods_lemma[local]:
  ∀m.
    proved_methods m ⇒
    ∀x st name mspec body env.
      x = eval_measure st env (mspec.rank, mspec.decreases) ∧
      Method name mspec body ∈ m ∧
      st.locals_old = st.locals ∧
      st.heap_old = st.heap ∧
      conditions_hold st env mspec.reqs ∧ compatible_env env m ⇒
      ∃st' out_vs.
        eval_stmt st env body st' (Rstop Sret) ∧
        conditions_hold st' env mspec.ens ∧
        LIST_REL (eval_exp st' env) (MAP (Var o FST) mspec.outs) out_vs
Proof
  gen_tac
  \\ disch_tac
  \\ ho_match_mp_tac WF_ind
  \\ rpt strip_tac
  \\ gvs [PULL_FORALL]
  \\ last_x_assum (drule o SRULE [proved_methods_def])
  \\ strip_tac
  \\ drule stmt_wp_sound
  \\ disch_then $ qspecl_then [‘st’,‘env’] mp_tac
  \\ impl_tac >-
   (asm_rewrite_tac []
    \\ drule_all imp_conditions_hold \\ strip_tac \\ gvs []
    \\ rpt strip_tac
    \\ gvs [eval_measure_wrap_old, compatible_env_def]
    \\ simp [SF SFY_ss])
  \\ gvs [False_thm]
  \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ rpt $ first_assum $ irule_at Any
  \\ fs [conditions_hold_def]
  \\ fs [GSYM MAP_MAP_o]
  \\ drule EVERY_eval_true_CanEval
  \\ strip_tac \\ pop_assum $ irule_at Any
QED

Theorem methods_correct = SRULE [] methods_lemma;

(*
Theorem stmt_wp_sound:
  ∀m reqs stmt post ens.
    stmt_wp m reqs stmt post ens ⇒
    ∀st env.
      methods_sound m ∧
      conditions_hold st env reqs ∧ compatible_env env m ⇒
      ∃st' ret.
        eval_stmt st env stmt st' ret ∧
        case ret of
        | Rstop Sret => conditions_hold st' env ens
        | Rcont => conditions_hold st' env post
        | _ => F
Proof
  Induct_on ‘stmt_wp’ \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [eval_stmt_def,evaluate_stmt_def,PULL_EXISTS]
    \\ last_x_assum $ irule_at Any
    \\ gvs [dafny_semanticPrimitivesTheory.state_component_equality])
  >~ [‘Assert’] >-
   (gvs [eval_stmt_def,evaluate_stmt_def,PULL_EXISTS,AllCaseEqs(),SF DNF_ss]
    \\ gvs [compatible_env_def,conditions_hold_def]
    \\ first_x_assum $ irule_at Any
    \\ gvs [eval_true_def]
    \\ first_x_assum $ irule_at Any)
  >~ [‘Return’] >-
   (gvs [eval_stmt_def,evaluate_stmt_def,PULL_EXISTS]
    \\ last_x_assum $ irule_at Any
    \\ gvs [dafny_semanticPrimitivesTheory.state_component_equality])
  \\ cheat
QED

Theorem proved_methods_sound:
  ∀m. proved_methods m ⇒ methods_sound m
Proof
  ho_match_mp_tac proved_methods_ind
  \\ rpt conj_tac
  >- (* empty *) simp [methods_sound_def]
  >- (* nonrec *)
   (rewrite_tac [methods_sound_def]
    \\ rpt strip_tac
    \\ reverse $ fs [IN_INSERT]
    >-
     (last_x_assum drule
      \\ disch_then irule
      \\ gvs [compatible_env_def])
    \\ gvs []
    \\ drule_all imp_conditions_hold \\ strip_tac
    \\ drule stmt_wp_sound
    \\ gvs [GSYM methods_sound_def]
    \\ disch_then drule
    \\ impl_tac
    >- gvs [compatible_env_def]
    \\ strip_tac
    \\ gvs [False_thm]
    \\ Cases_on ‘ret’ \\ gvs []
    \\ rename [‘eval_stmt _ _ _ _ (Rstop ret)’] \\ Cases_on ‘ret’ \\ gvs []
    \\ first_x_assum $ irule_at $ Pos hd \\ asm_rewrite_tac [])
  (* mutrec *)
  \\ rewrite_tac [methods_sound_def]
  \\ rpt strip_tac
  \\ reverse $ gvs [IN_UNION]
  >-
   (last_x_assum drule
    \\ disch_then irule
    \\ gvs [compatible_env_def])
  \\ rename [‘Method name mspec body ∈ mutrec’]
  \\ first_assum drule
  \\ strip_tac \\ gvs []
  \\ drule_all imp_conditions_hold \\ strip_tac
  \\ drule stmt_wp_sound
  \\ gvs [False_thm]
  \\ cheat
QED
*)
