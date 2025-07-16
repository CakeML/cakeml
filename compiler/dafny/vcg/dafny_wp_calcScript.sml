(*
  Calculus for VCG for Dafny
*)
Theory dafny_wp_calc
Ancestors
  dafny_ast dafny_semanticPrimitives dafnyProps dafny_evaluate
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
Overload "dfy_eq" = “BinOp Eq”

Overload "not" = “UnOp Not”

(* TODO Move to dafny_eval_rel *)
Definition CanEval_def: (* beautiful or not.. *)
  CanEval e = dfy_eq e e
End

(* TODO Move to dafny_eval_rel *)
Definition IsBool_def:
  IsBool e = CanEval $ dfy_eq e True
End

(* TODO Make this a simp *)
Triviality value_same_type_same_value:
  value_same_type v v
Proof
  Cases_on ‘v’ \\ gvs [value_same_type_def]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_true_CanEval:
  eval_true st env (CanEval e) ⇒ ∃v. eval_exp st env e v
Proof
  gvs [eval_true_def,CanEval_def,evaluate_exp_def,eval_exp_def]
  \\ gvs [AllCaseEqs(),PULL_EXISTS,do_sc_def,do_bop_def]
  \\ gvs [value_same_type_same_value]
  \\ rpt strip_tac
  \\ rev_drule (cj 1 evaluate_exp_with_clock)
  \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
  \\ last_assum $ irule_at Any
QED

(* TODO Move to dafny_eval_rel *)
Theorem EVERY_eval_true_CanEval:
  EVERY (eval_true st env) (MAP CanEval args) ⇒
  ∃in_vs. LIST_REL (eval_exp st env) args in_vs
Proof
  Induct_on ‘args’ \\ gvs [] \\ rw []
  \\ res_tac \\ drule eval_true_CanEval \\ strip_tac
  \\ rpt $ pop_assum $ irule_at Any
QED

Definition decrease_lt_def:
  decrease_lt [] [] = False ∧
  decrease_lt [] ys = True ∧
  decrease_lt xs [] = False ∧
  decrease_lt (x::xs) (y::ys) =
    if LENGTH xs = LENGTH ys then
      If (dfy_eq x y) (decrease_lt xs ys) (int_lt x y)
    else if LENGTH xs < LENGTH ys then True else False
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
    LIST_REL (λr n. r = VarLhs n) (MAP FST l) ret_names ∧
    LIST_REL (λr e. r = ExpRhs e) (MAP SND l) exps
    ⇒
    stmt_wp m [Let (ZIP (ret_names,exps)) (conj post)] (Assign l) post ens decs
[~MetCall:]
  ∀m mname mspec mbody args ret_names rets post ens.
    Method mname mspec mbody ∈ m ∧
    LENGTH mspec.ins = LENGTH args ∧
    ALL_DISTINCT (MAP FST mspec.ins ++ MAP FST mspec.outs) ∧
    LIST_REL (λr rn. r = VarLhs rn) rets ret_names ∧
    ⊢ (imp (conj mspec.ens)
         (Let (ZIP (ret_names,MAP (λ(m,ty). Var m) mspec.outs)) (conj post)))
    ⇒
    stmt_wp m (Let (ZIP (MAP FST mspec.ins,args)) (conj mspec.reqs) ::
               MAP CanEval args ++
               decreases_check (mspec.rank,
                                MAP (Let (ZIP (MAP FST mspec.ins,args))) mspec.decreases)
                               (wrap_old decs))
              (MetCall rets mname args) post ens decs
End

Definition proved_methods_def:
  proved_methods m ⇔
    ∀name mspec body.
      Method name mspec body ∈ m ⇒
      ∃wp_pre.
        stmt_wp m wp_pre body [False] mspec.ens (mspec.rank, mspec.decreases) ∧
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

Triviality WF_lemma:
  WF (prim_rec$< LEX SHORTLEX prim_rec$<)
Proof
  irule pairTheory.WF_LEX
  \\ irule_at Any listTheory.WF_SHORTLEX
  \\ rewrite_tac [prim_recTheory.WF_LESS]
QED

Triviality WF_ind =
  MATCH_MP relationTheory.WF_INDUCTION_THM WF_lemma;

Definition evaluate_exp_total_def:
  evaluate_exp_total st env e =
    some v. eval_exp st env e v
End

Definition eval_decreases_def:
  eval_decreases st env [] = SOME [] ∧
  eval_decreases st env (e::es) =
    case evaluate_exp_total st env e, eval_decreases st env es of
    | (SOME (IntV i), SOME rest) =>
        if i < 0 then NONE else SOME (Num i :: rest)
    | _ => NONE
End

Definition eval_measure_def:
  eval_measure st env (rank:num,es) =
    (rank, THE (eval_decreases st env es))
End

Theorem False_thm[simp,local]:
  conditions_hold st env [False] = F
Proof
  simp [conditions_hold_def,eval_true_def,evaluate_exp_def,eval_exp_def]
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Skip:
  eval_stmt st env Skip st Rcont
Proof
  gvs [eval_stmt_def, evaluate_stmt_def, state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Assert:
  eval_true st env e
  ⇒
  eval_stmt st env (Assert e) st Rcont
Proof
  strip_tac
  \\ gvs [eval_stmt_def, evaluate_stmt_def]
  \\ Cases_on ‘env.is_running’ \\ simp []
  >- (gvs [state_component_equality])
  \\ gvs [eval_true_def, eval_exp_def, AllCaseEqs()]
  \\ last_assum $ irule_at (Pos hd)
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Return:
  eval_stmt st env Return st (Rstop Sret)
Proof
  gvs [eval_stmt_def, evaluate_stmt_def, state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Then_cont:
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Then_ret:
  eval_stmt st env stmt₁ st₁ (Rstop Sret)
  ⇒
  eval_stmt st env (Then stmt₁ stmt₂) st₁ (Rstop Sret)
Proof
  strip_tac
  \\ gvs [eval_stmt_def, evaluate_stmt_def, AllCaseEqs()]
  \\ last_assum $ irule_at (Pos hd) \\ simp [state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Then_cont_ret:
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_If_thn:
  eval_true st env grd ∧
  eval_stmt st env thn st₁ ret ∧
  ret ≠ Rstop (Serr Rtimeout_error)
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_exp_not_not:
  eval_exp st env (not (not x)) (BoolV b) ⇒ eval_exp st env x (BoolV b)
Proof
  strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_def, do_uop_def, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_exp_bool_not:
  eval_exp st env a (BoolV b) ⇒ eval_exp st env (not a) (BoolV ¬b)
Proof
  strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_def, do_uop_def, PULL_EXISTS, AllCaseEqs()]
  \\ last_x_assum $ irule_at (Pos hd)
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_If_els:
  eval_true st env (not grd) ∧
  eval_stmt st env els st₁ ret ∧
  ret ≠ Rstop (Serr Rtimeout_error)
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

(* TODO Move to dafny_eval_rel *)
Definition eval_rhs_exp_def:
  eval_rhs_exp st env e st' v ⇔
    ∃ck1 ck2.
      evaluate_rhs_exp (st with clock := ck1) env e =
        (st' with clock := ck2, Rval v)
End

(* TODO Move to dafny_eval_rel *)
Definition eval_rhs_exps_def:
  eval_rhs_exps st env es st' vs ⇔
    ∃ck1 ck2.
      evaluate_rhs_exps (st with clock := ck1) env es =
        (st' with clock := ck2, Rval vs)
End

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Assign:
  eval_rhs_exps st env (MAP SND ass) st₁ vs ∧
  assign_values st₁ env (MAP FST ass) vs = (st', Rcont)
  ⇒
  eval_stmt st env (Assign ass) st' Rcont
Proof
  strip_tac
  \\ simp [eval_stmt_def, evaluate_stmt_def]
  \\ fs [eval_rhs_exps_def, PULL_EXISTS, AllCaseEqs()]
  \\ dxrule evaluate_rhs_exps_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘st₁.clock’ assume_tac
  \\ last_x_assum $ irule_at (Pos hd)
  \\ dxrule assign_values_add_to_clock \\ simp []
  \\ simp [state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_stmt_MetCall:
  get_member mname env.prog =
    SOME (Method name ins reqs ens rds decrs outs mods body) ∧
  LIST_REL (eval_exp st env) args in_vs ∧
  set_up_call st (MAP FST ins) in_vs (MAP FST outs) = SOME st₁ ∧
  eval_stmt st₁ env body st₂ (Rstop Sret) ∧
  OPT_MMAP (read_local st₂.locals) (MAP FST outs) = SOME out_vs ∧
  LENGTH rets = LENGTH out_vs ∧
  assign_values (restore_caller st₂ st) env rets out_vs = (st',Rcont)
  ⇒
  eval_stmt st env (MetCall rets mname args) st' Rcont
Proof
  rpt strip_tac
  \\ simp [eval_stmt_def, evaluate_stmt_def]
  \\ dxrule_then mp_tac eval_exp_evaluate_exps
  \\ disch_then $ qx_choosel_then [‘ck’, ‘ck₁’] assume_tac \\ simp []
  \\ fs [eval_stmt_def]
  \\ rename
       [‘evaluate_stmt (_ with clock := ck₂) _ _ = (_ with clock := ck₃, _)’]
  \\ qexists ‘st₂.clock + ck + ck₂ + 1’
  \\ dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then assume_tac
  \\ qmatch_goalsub_abbrev_tac ‘set_up_call (_ with clock := ck₄)’
  \\ dxrule set_up_call_some_with_clock
  \\ disch_then assume_tac
  \\ simp [Abbr ‘ck₄’, dec_clock_def]
  \\ dxrule evaluate_stmt_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁ + st₂.clock’ assume_tac \\ gvs []
  \\ rewrite_tac [restore_caller_cur_with_clock, restore_caller_prev_with_clock]
  \\ dxrule assign_values_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘ck₁ + ck₃’ assume_tac \\ gvs []
  \\ simp [state_component_equality]
QED

Triviality conditions_hold_cons:
  conditions_hold st env (e::es) ⇔
  eval_true st env e ∧ conditions_hold st env es
Proof
  gvs [conditions_hold_def]
QED

(* TODO Move to dafny_evaluateProps *)
Triviality assign_value_Rcont_old:
  assign_value st env lhs v = (st', Rcont) ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  disch_tac
  \\ Cases_on ‘lhs’
  \\ gvs [assign_value_def, update_local_def, update_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

(* TODO Move to dafny_evaluateProps *)
Triviality assign_values_Rcont_old:
  ∀lhss vs st env st'.
    assign_values st env lhss vs = (st', Rcont) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  Induct \\ namedCases_on ‘vs’ ["", "v vs₁"]
  \\ simp [assign_values_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac assign_value_Rcont_old
  \\ res_tac \\ gvs []
QED

(* TODO Move to dafny_evaluateProps *)
Triviality evaluate_rhs_exp_Rval_old:
  evaluate_rhs_exp st env rhs = (st', Rval v) ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  disch_tac
  \\ Cases_on ‘rhs’
  \\ gvs [evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

(* TODO Move to dafny_evaluateProps *)
Triviality evaluate_rhs_exps_Rval_old:
  ∀rhss st st' env vs.
    evaluate_rhs_exps st env rhss = (st', Rval vs) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  Induct \\ gvs [evaluate_rhs_exps_def]
  \\ rpt gen_tac \\ disch_tac
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ imp_res_tac evaluate_rhs_exp_Rval_old \\ gvs []
QED

(* TODO Move to dafny_evaluateProps *)
Triviality evaluate_stmt_Rcont_old:
  ∀st env stmt st'.
    evaluate_stmt st env stmt = (st', Rcont) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_tac)
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ res_tac \\ gvs [])
  >~ [‘If grd thn els’] >-
   (strip_tac
    \\ gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ gvs [oneline do_cond_def, AllCaseEqs()]
    \\ res_tac \\ gvs [])
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [pop_locals_def, safe_drop_def, declare_local_def, AllCaseEqs()]
    \\ last_x_assum drule \\ gvs [])
  >~ [‘Assign ass’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_rhs_exps_Rval_old
    \\ imp_res_tac assign_values_Rcont_old \\ gvs [])
  >~ [‘While grd invs decrs mods body’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [dec_clock_def])
  >~ [‘Print e t’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock
    \\ gvs [print_string_def, AllCaseEqs()])
  >~ [‘MetCall lhss name args’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ imp_res_tac assign_values_Rcont_old \\ gvs []
    \\ gvs [restore_caller_def])
  >~ [‘Return’] >-
   (gvs [evaluate_stmt_def])
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_stmt_Rcont_old:
  eval_stmt st env stmt st' Rcont ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old
Proof
  simp [eval_stmt_def] \\ strip_tac
  \\ imp_res_tac evaluate_stmt_Rcont_old \\ gvs []
QED

(* TODO Move to dafny_evaluateProps *)
Triviality evaluate_exp_Rval_eq:
  (∀st env e st' v st₁.
     evaluate_exp st env e = (st', Rval v) ∧
     st₁.locals = st.locals ∧ st₁.heap = st.heap ∧
     st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ⇒
     ∃st₁'. evaluate_exp st₁ env e = (st₁', Rval v)) ∧
  (∀st env es st' vs st₁.
     evaluate_exps st env es = (st', Rval vs) ∧
     st₁.locals = st.locals ∧ st₁.heap = st.heap ∧
     st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ⇒
     ∃st₁'. evaluate_exps st₁ env es = (st₁', Rval vs))
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Lit l’] >-
   (gvs [evaluate_exp_def])
  >~ [‘Var name’] >-
   (gvs [evaluate_exp_def, AllCaseEqs()])
  >~ [‘If grd thn els’] >-
   (gvs [evaluate_exp_def]
    (* st -> st₂ -> st₄, since st₁ is already used (I know, I know.) *)
    \\ namedCases_on ‘evaluate_exp st env grd’ ["st₂ r₂"] \\ gvs []
    \\ Cases_on ‘r₂’ \\ gvs []
    \\ first_x_assum drule_all
    \\ strip_tac \\ gvs []
    \\ CASE_TAC \\ gvs []
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, PULL_EXISTS, AllCaseEqs()]
    \\ last_x_assum drule \\ simp []
    \\ strip_tac
    \\ first_assum $ irule_at (Pos hd) \\ simp [])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp st env e₀’ ["st₂ r₂"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ namedCases_on ‘r₂’ ["v₀", "err"] \\ gvs []
    \\ first_x_assum drule_all
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘do_sc bop v₀’ \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ gvs []
    \\ namedCases_on ‘evaluate_exp (st with clock := ck) env e₁’ ["st₄ r₄"]
    \\ gvs []
    \\ Cases_on ‘r₄’ \\ gvs []
    \\ last_x_assum $ qspec_then ‘st₁ with clock := ck₁’ mp_tac \\ simp []
    \\ strip_tac \\ simp []
    \\ CASE_TAC \\ gvs [])
  >~ [‘ArrLen arr’] >-
   (gvs [evaluate_exp_def, PULL_EXISTS, AllCaseEqs()]
    \\ last_x_assum drule \\ simp []
    \\ strip_tac
    \\ first_assum $ irule_at (Pos hd) \\ simp [])
  >~ [‘ArrSel arr idx’] >-
   (gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp st env arr’ ["st₂ r₂"]\\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ namedCases_on ‘r₂’ ["v₀", "err"] \\ gvs []
    \\ first_x_assum drule_all
    \\ strip_tac \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ gvs []
    \\ namedCases_on ‘evaluate_exp (st with clock := ck) env idx’ ["st₄ r₄"]
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₂’ assume_tac \\ gvs []
    \\ gvs []
    \\ Cases_on ‘r₄’ \\ gvs []
    \\ last_x_assum $ qspec_then ‘st₁ with clock := ck₁’ mp_tac \\ simp []
    \\ strip_tac \\ simp []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ rpt strip_tac \\ gvs []
    \\ gvs [index_array_def, AllCaseEqs()])
  >~ [‘FunCall name args’] >-

   (gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "mem₁"] \\ gvs []
    \\ Cases_on ‘mem₁’ \\ gvs []
    \\ rename [‘get_member _ _ = SOME (Function _ _ _ _ _ _ body)’]
    \\ namedCases_on ‘evaluate_exps st env args’ ["st₂ r₂"] \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []

    \\ namedCases_on ‘r₂’ ["in_vs", "err"] \\ gvs []
    \\ first_x_assum drule_all
    \\ strip_tac \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ gvs []
    (* TODO Is the statement even true? I feel like we need to assume that
       evaluate_exp st₁ env e = Rval, or at least does not timeout *)
    \\ gvs [set_up_call_def, AllCaseEqs()]

   )

  \\ cheat
QED

(* TODO Move to dafny_evaluateProps *)
Triviality evaluate_exp_old_Rval_eq:
  evaluate_exp st₁ env (Old e) = (st₁', Rval v) ∧
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ⇒
  ∃st'. evaluate_exp st env (Old e) = (st', Rval v)
Proof
  rpt strip_tac
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
  \\ drule (cj 1 evaluate_exp_Rval_eq)  \\ gvs [use_old_def]
QED

(* TODO Move to dafny_eval_rel - Keep as triviality *)
Triviality eval_exp_old_eq:
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ∧
  eval_exp st₁ env (Old e) v ⇒
  eval_exp st env (Old e) v
Proof
  strip_tac
  \\ gvs [eval_exp_def]
  \\ drule evaluate_exp_old_Rval_eq \\ gvs []
  \\ disch_then $ qspec_then ‘st’ mp_tac \\ simp []
  \\ rpt strip_tac
  \\ qexists ‘st.clock’ \\ gvs []
  \\ imp_res_tac evaluate_exp_with_clock
  \\ gvs [state_component_equality]
QED

(* TODO Move to dafny_eval_rel *)
Theorem eval_exp_old_eq:
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ⇒
  eval_exp st₁ env (Old e) v =
  eval_exp st env (Old e) v
Proof
  metis_tac [eval_exp_old_eq]
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
  \\ simp [eval_decreases_def]
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_true_isbool:
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_true_isbool_cases:
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

(* TODO Move to dafny_eval_rel *)
Triviality eval_true_imp:
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

Theorem stmt_wp_sound:
  ∀m reqs stmt post ens decs.
    stmt_wp m reqs stmt post ens decs ⇒
    ∀st env.
      (∀st' name' mspec' body'.
          ($< LEX SHORTLEX $<)
            (eval_measure st' env (mspec'.rank,mspec'.decreases))
            (eval_measure st env (wrap_old decs)) ∧
          Method name' mspec' body' ∈ m ∧ st'.locals_old = st'.locals ∧
          st'.heap_old = st'.heap ∧ conditions_hold st' env mspec'.reqs ∧
          compatible_env env m ⇒
          ∃st''.
            eval_stmt st' env body' st'' (Rstop Sret) ∧
            conditions_hold st'' env mspec'.ens) ∧
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
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    (* Execute els branch *)
    \\ last_x_assum $ drule_at (Pos $ el 2) \\ simp []
    \\ impl_tac >- (gvs [])
    \\ disch_then $ qx_choosel_then [‘st₁’, ‘ret₁’] mp_tac
    \\ strip_tac
    \\ irule_at (Pos hd) eval_stmt_If_els
    \\ gvs [conditions_hold_def]
    \\ first_assum $ irule_at (Pos hd) \\ simp [])
  >~ [‘Assign ass’] >-
   (irule_at (Pos hd) eval_stmt_Assign
    \\ cheat)
  >~ [‘MetCall rets mname args’] >-
   (irule_at Any eval_stmt_MetCall \\ gvs []
    \\ qpat_assum ‘compatible_env env m’ mp_tac
    \\ rewrite_tac [compatible_env_def]
    \\ strip_tac
    \\ pop_assum drule
    \\ strip_tac \\ gvs []
    \\ gvs [conditions_hold_def]
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
      >- cheat
      >- gvs [Abbr‘st1’]
      >- gvs [Abbr‘st1’]
      \\ PairCases_on ‘decs’ \\ gvs [wrap_old_def]
      \\ qpat_x_assum ‘EVERY _ (decreases_check _ _)’ mp_tac
      \\ simp [decreases_check_def] \\ cheat)
    \\ cheat)
  \\ cheat
QED

Theorem eval_measure_wrap_old:
  st.locals_old = st.locals ∧ st.heap_old = st.heap ⇒
  eval_measure st env (wrap_old decs) =
  eval_measure st env decs
Proof
  cheat
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
      ∃st'. eval_stmt st env body st' (Rstop Sret) ∧
            conditions_hold st' env mspec.ens
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
    \\ gvs [eval_measure_wrap_old]
    \\ simp [SF SFY_ss])
  \\ gvs [False_thm]
  \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ rpt $ first_assum $ irule_at Any
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
