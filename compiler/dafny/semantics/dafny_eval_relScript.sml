(*
  Proves relational big-step-style theorems about Dafny semantics
*)
Theory dafny_eval_rel
Ancestors
  dafny_ast
  dafny_semanticPrimitives
  dafnyProps
  dafny_evaluate
  dafny_evaluateProps
Libs
  preamble

Overload True = “Lit (BoolL T)”;
Overload False = “Lit (BoolL F)”;

Overload "not" = “UnOp Not”;
Overload "imp" = “BinOp Imp”;
Overload "dfy_eq" = “BinOp Eq”;

Definition eval_exp_def:
  eval_exp st env e v ⇔
    ∃ck1 ck2.
      evaluate_exp (st with clock := ck1) env e =
        (st with clock := ck2, Rval v)
End

Definition eval_rhs_exp_def:
  eval_rhs_exp st env e st' v ⇔
    ∃ck1 ck2.
      evaluate_rhs_exp (st with clock := ck1) env e =
        (st' with clock := ck2, Rval v)
End

Definition eval_rhs_exps_def:
  eval_rhs_exps st env es st' vs ⇔
    ∃ck1 ck2.
      evaluate_rhs_exps (st with clock := ck1) env es =
        (st' with clock := ck2, Rval vs)
End

Definition assi_values_def:
  assi_values st env lhss rhss st' ⇔
    ∃ck1 ck2.
      assign_values (st with clock := ck1) env lhss rhss =
      (st' with clock := ck2, Rcont)
End

Definition eval_stmt_def:
  eval_stmt st env body st' ret =
    ∃ck1 ck2.
      evaluate_stmt (st with clock := ck1) env body =
        (st' with clock := ck2, ret) ∧ ret ≠ Rstop (Serr Rtimeout)
End

Definition eval_true_def:
  eval_true st env e ⇔ eval_exp st env e (BoolV T)
End

Definition valid_def:
  valid e = ∀st env. eval_true st env e
End
Overload "⊢" = “valid”;

Definition CanEval_def: (* beautiful or not.. *)
  CanEval e = dfy_eq e e
End

Definition IsBool_def:
  IsBool e = CanEval $ dfy_eq e True
End

Definition conj_def:
  conj [] = Lit (BoolL T) ∧
  conj [x] = x ∧
  conj (x::xs) = BinOp And (x) (conj xs)
End

(* simp *)

Theorem eval_true_true[simp]:
  eval_true st env True
Proof
  gvs [eval_true_def, eval_exp_def, evaluate_exp_def]
  \\ qexistsl [‘0’, ‘0’] \\ simp []
QED

Theorem conj_empty[simp]:
  conj [] = True
Proof
  rewrite_tac [conj_def]
QED

Theorem value_same_type_same_value[simp]:
  value_same_type v v
Proof
  Cases_on ‘v’ \\ gvs [value_same_type_def]
QED

(* *** *)

Theorem eval_true_mp:
  eval_true st env (imp p q) ∧ eval_true st env p ⇒ eval_true st env q
Proof
  gvs [eval_true_def, eval_exp_def]
  \\ gvs [PULL_EXISTS]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’]
  \\ rpt strip_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ mp_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ mp_tac
  \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, do_sc_def, do_bop_def, AllCaseEqs()]
  \\ first_assum $ irule_at $ Pos hd
QED

Theorem eval_true_cons:
  eval_true st env (conj (x::xs)) =
  (eval_true st env x ∧ eval_true st env (conj xs))
Proof
  namedCases_on ‘xs’ ["", "x₁ xs₁"] \\ simp [conj_def]
  \\ gvs [eval_true_def, eval_exp_def]
  \\ gvs [evaluate_exp_def, do_sc_def, PULL_EXISTS, do_bop_def, AllCaseEqs()]
  \\ iff_tac
  >- (rpt strip_tac
      \\ rev_drule (cj 1 evaluate_exp_with_clock)
      \\ rpt strip_tac \\ gvs []
      \\ last_x_assum $ irule_at (Pos hd)
      \\ last_x_assum $ irule_at (Pos hd))
  \\ disch_then $ qx_choosel_then [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’] mp_tac
  \\ rpt strip_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ mp_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ mp_tac
  \\ rpt strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos hd
QED

Theorem eval_true_conj_every:
  ∀xs st env. eval_true st env (conj xs) ⇔ EVERY (eval_true st env) xs
Proof
  Induct \\ simp []
  \\ qx_genl_tac [‘x’, ‘st’, ‘env’]
  \\ simp [eval_true_cons]
QED

Theorem eval_exp_evaluate_exps:
  ∀es vs st env.
    LIST_REL (eval_exp st env) es vs ⇒
    ∃ck ck₁.
      evaluate_exps (st with clock := ck) env es =
      (st with clock := ck₁, Rval vs)
Proof
  Induct >-
   (simp [evaluate_exp_def] \\ gen_tac \\ qexistsl [‘0’, ‘0’] \\ simp [])
  \\ qx_genl_tac [‘e’, ‘vs’, ‘st’, ‘env’] \\ disch_tac
  \\ namedCases_on ‘vs’ ["", "v vs₁"] \\ gvs []
  \\ simp [evaluate_exp_def]
  \\ fs [eval_exp_def]
  \\ rename
       [‘evaluate_exp (_ with clock := ck₁) _ _ = (_ with clock := ck₂, _) ’]
  \\ last_x_assum drule
  \\ disch_then $ qx_choosel_then [‘ck₃’, ‘ck₄’] assume_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ qexistsl [‘ck₁ + ck₃’, ‘ck₂ + ck₄’] \\ gvs []
QED

Theorem eval_true_CanEval:
  eval_true st env (CanEval e) ⇒ ∃v. eval_exp st env e v
Proof
  gvs [eval_true_def,CanEval_def,evaluate_exp_def,eval_exp_def]
  \\ gvs [AllCaseEqs(),PULL_EXISTS,do_sc_def,do_bop_def]
  \\ gvs []
  \\ rpt strip_tac
  \\ rev_drule (cj 1 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
  \\ last_assum $ irule_at Any
QED

Theorem EVERY_eval_true_CanEval:
  EVERY (eval_true st env) (MAP CanEval args) ⇒
  ∃in_vs. LIST_REL (eval_exp st env) args in_vs
Proof
  Induct_on ‘args’ \\ gvs [] \\ rw []
  \\ res_tac \\ drule eval_true_CanEval \\ strip_tac
  \\ rpt $ pop_assum $ irule_at Any
QED

Theorem eval_exp_not_not:
  eval_exp st env (not (not x)) (BoolV b) ⇒ eval_exp st env x (BoolV b)
Proof
  strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_def, do_uop_def, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
QED

Theorem eval_exp_bool_not:
  eval_exp st env a (BoolV b) ⇒ eval_exp st env (not a) (BoolV ¬b)
Proof
  strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_def, do_uop_def, PULL_EXISTS, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
QED

Theorem eval_true_isbool:
  eval_true st env (IsBool a) ⇒ ∃b. eval_exp st env a (BoolV b)
Proof
  strip_tac
  \\ gvs [eval_true_def, eval_exp_def, IsBool_def, CanEval_def,
          evaluate_exp_def, do_sc_def, do_bop_def, value_same_type_def,
          AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
  \\ rename [‘_ ⇔ v₀ = _’]
  \\ Cases_on ‘v₀’ \\ gvs []
  \\ last_x_assum $ irule_at (Pos hd)
QED

Theorem eval_true_isbool_cases:
  eval_true st env (IsBool a) ⇒
  eval_true st env a ∨ eval_true st env (not a)
Proof
  strip_tac
  \\ drule eval_true_isbool
  \\ disch_then $ qx_choose_then ‘b’ assume_tac
  \\ Cases_on ‘b’
  \\ gvs [eval_true_def]
  \\ drule eval_exp_bool_not \\ simp []
QED

Theorem eval_true_imp:
  eval_true st env (imp a b) ⇒
  (eval_true st env a ⇒ eval_true st env b)
Proof
  simp [eval_true_def, eval_exp_def, PULL_EXISTS, PULL_FORALL]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’]
  \\ rpt strip_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ gvs [evaluate_exp_def]
  \\ gvs [do_sc_def, do_bop_def, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
QED

Theorem eval_stmt_Skip:
  eval_stmt st env Skip st Rcont
Proof
  gvs [eval_stmt_def, evaluate_stmt_def, state_component_equality]
QED

Theorem eval_stmt_Assert:
  eval_true st env e
  ⇒
  eval_stmt st env (Assert e) st Rcont
Proof
  strip_tac
  \\ gvs [eval_stmt_def, evaluate_stmt_def, eval_true_def, eval_exp_def,
          AllCaseEqs()]
  \\ last_assum $ irule_at (Pos hd)
  \\ simp [state_component_equality]
QED

Theorem eval_stmt_Return:
  eval_stmt st env Return st (Rstop Sret)
Proof
  gvs [eval_stmt_def, evaluate_stmt_def, state_component_equality]
QED

Theorem eval_stmt_Then_cont:
  eval_stmt st env stmt₁ st₁ Rcont ∧
  eval_stmt st₁ env stmt₂ st₂ Rcont
  ⇒
  eval_stmt st env (Then stmt₁ stmt₂) st₂ Rcont
Proof
  strip_tac
  \\ gvs [eval_stmt_def]
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₃) _ _ = (_ with clock := ck₄, _)’]
  \\ pop_assum mp_tac
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₁) _ _ = (_ with clock := ck₂, _)’]
  \\ disch_tac
  \\ rev_dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ rev_dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ simp [evaluate_stmt_def, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
  \\ gvs [state_component_equality]
QED

Theorem eval_stmt_Then_ret:
  eval_stmt st env stmt₁ st₁ (Rstop Sret)
  ⇒
  eval_stmt st env (Then stmt₁ stmt₂) st₁ (Rstop Sret)
Proof
  strip_tac
  \\ gvs [eval_stmt_def, evaluate_stmt_def, AllCaseEqs()]
  \\ last_assum $ irule_at (Pos hd) \\ simp [state_component_equality]
QED

Theorem eval_stmt_Then_cont_ret:
  eval_stmt st env stmt₁ st₁ Rcont ∧
  eval_stmt st₁ env stmt₂ st₂ (Rstop Sret)
  ⇒
  eval_stmt st env (Then stmt₁ stmt₂) st₂ (Rstop Sret)
Proof
  strip_tac
  \\ gvs [eval_stmt_def]
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₃) _ _ = (_ with clock := ck₄, _)’]
  \\ pop_assum mp_tac
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₁) _ _ = (_ with clock := ck₂, _)’]
  \\ disch_tac
  \\ rev_dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ rev_dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ simp [evaluate_stmt_def, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
  \\ gvs [state_component_equality]
QED

Theorem eval_stmt_If_thn:
  eval_true st env grd ∧
  eval_stmt st env thn st₁ ret
  ⇒
  eval_stmt st env (If grd thn els) st₁ ret
Proof
  gvs [eval_stmt_def, eval_true_def, eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’]
  \\ strip_tac
  \\ simp [evaluate_stmt_def]
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ gvs []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ dxrule evaluate_stmt_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ qexists ‘ck₁ + ck₃’ \\ gvs []
  \\ simp [do_cond_def, state_component_equality]
QED

Theorem eval_stmt_If_els:
  eval_true st env (not grd) ∧
  eval_stmt st env els st₁ ret
  ⇒
  eval_stmt st env (If grd thn els) st₁ ret
Proof
  gvs [eval_stmt_def, eval_true_def]
  \\ strip_tac
  \\ dxrule_then assume_tac eval_exp_bool_not
  \\ dxrule_then assume_tac eval_exp_not_not \\ gvs []
  \\ gvs [eval_exp_def]
  \\ rename
       [‘evaluate_exp (_ with clock := ck₁) _ _ = (_ with clock := ck₂, _)’,
        ‘evaluate_stmt (_ with clock := ck₃) _ _ = (_ with clock := ck₄, _)’]
  \\ simp [evaluate_stmt_def]
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ gvs []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ dxrule evaluate_stmt_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ qexists ‘ck₁ + ck₃’ \\ gvs []
  \\ simp [do_cond_def, state_component_equality]
QED

Theorem eval_stmt_Assign:
  eval_rhs_exps st env (MAP SND ass) st₁ vs ∧
  assi_values st₁ env (MAP FST ass) vs st'
  ⇒
  eval_stmt st env (Assign ass) st' Rcont
Proof
  fs [eval_rhs_exps_def, assi_values_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’]
  \\ strip_tac
  \\ simp [eval_stmt_def, evaluate_stmt_def]
  \\ dxrule evaluate_rhs_exps_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ dxrule assign_values_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac
  \\ simp [AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
  \\ full_simp_tac std_ss [AC ADD_COMM ADD_ASSOC]
  \\ simp [state_component_equality]
QED

Theorem eval_stmt_MetCall:
  get_member mname env.prog =
    SOME (Method name ins reqs ens rds decrs outs mods body) ∧
  LIST_REL (eval_exp st env) args in_vs ∧
  set_up_call st (MAP FST ins) in_vs (MAP FST outs) = SOME st₁ ∧
  eval_stmt st₁ env body st₂ (Rstop Sret) ∧
  OPT_MMAP (read_local st₂.locals) (MAP FST outs) = SOME out_vs ∧
  LENGTH rets = LENGTH out_vs ∧
  assi_values (restore_caller st₂ st) env rets out_vs st'
  ⇒
  eval_stmt st env (MetCall rets mname args) st' Rcont
Proof
  rpt strip_tac
  \\ simp [eval_stmt_def, evaluate_stmt_def]
  \\ dxrule_then mp_tac eval_exp_evaluate_exps
  \\ disch_then $ qx_choosel_then [‘ck’, ‘ck₁’] assume_tac \\ simp []
  \\ fs [eval_stmt_def, assi_values_def]
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₂) _ _ = (_ with clock := ck₃, _)’,
        ‘assign_values (_ with clock := ck₄) _ _ _ = (_ with clock := ck₅, _)’]
  \\ qexists ‘st₂.clock + ck + ck₂ + ck₄ + 1’
  \\ dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then assume_tac
  \\ qmatch_goalsub_abbrev_tac ‘set_up_call (_ with clock := ck₆)’
  \\ dxrule set_up_call_some_with_clock
  \\ disch_then assume_tac
  \\ simp [Abbr ‘ck₆’, dec_clock_def]
  \\ dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁ + ck₄ + st₂.clock’ assume_tac \\ gvs []
  \\ rewrite_tac [restore_caller_cur_with_clock, restore_caller_prev_with_clock]
  \\ dxrule assign_values_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁ + ck₃ + st₂.clock’ assume_tac \\ gvs []
  \\ simp [state_component_equality]
QED

Theorem eval_stmt_Rcont_const:
  eval_stmt st env stmt st' Rcont ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
  st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  simp [eval_stmt_def] \\ strip_tac
  \\ imp_res_tac evaluate_stmt_Rcont_const \\ gvs []
QED

Theorem eval_exp_old_eq[local]:
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ∧
  st₁.locals_prev = st.locals_prev ∧ st₁.heap_prev = st.heap_prev ∧
  eval_exp st₁ env (Old e) v ⇒
  eval_exp st env (Old e) v
Proof
  strip_tac
  \\ gvs [eval_exp_def]
  \\ drule evaluate_exp_old_Rval_eq \\ gvs []
  \\ disch_then $ qspec_then ‘st’ mp_tac \\ simp []
  \\ disch_then $ qx_choosel_then [‘ck’, ‘st'’] assume_tac
  \\ qexists ‘ck’ \\ gvs []
  \\ imp_res_tac evaluate_exp_with_clock
  \\ gvs [state_component_equality]
QED

Theorem eval_exp_old_eq:
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ∧
  st₁.locals_prev = st.locals_prev ∧ st₁.heap_prev = st.heap_prev ⇒
  eval_exp st₁ env (Old e) v = eval_exp st env (Old e) v
Proof
  metis_tac [eval_exp_old_eq]
QED

Theorem eval_exp_old_eq_not_old:
  st.locals_old = st.locals ∧ st.heap_old = st.heap ⇒
  eval_exp st env (Old e) v = eval_exp st env e v
Proof
  rpt strip_tac
  \\ iff_tac
  \\ gvs [eval_exp_def]
  \\ disch_then $ qx_choosel_then [‘ck’, ‘ck₁’] mp_tac
  \\ gvs [evaluate_exp_def, use_old_def, unuse_old_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
  \\ qexistsl [‘ck’, ‘ck₁’] \\ gvs [state_component_equality]
  (* The big part is in the goal in one case, and in the assumptions in the
     other case *)
  \\ ‘st with <|clock := ck; locals := st.locals; heap := st.heap|> =
      st with clock := ck’ by
    (gvs [state_component_equality])
  \\ gvs []
QED
