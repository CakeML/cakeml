(*
  Calculus for VCG for Dafny
*)
Theory dafny_wp_calc
Ancestors
  dafny_ast dafny_semanticPrimitives dafny_evaluate
Libs
  preamble


(*
  TODO:
   - drop types from Let
   - prove cheats up tp and incl stmt_wp_sound
*)

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

Overload True = “Lit (BoolL T)”;
Overload False = “Lit (BoolL F)”;

Definition eval_exp_def:
  eval_exp st env e v ⇔
    ∃ck1 ck2.
      evaluate_exp (st with clock := ck1) env e =
        (st with clock := ck2, Rval v)
End

Definition eval_stmt_def:
  eval_stmt st env body st' ret =
    ∃ck1 ck2.
      evaluate_stmt (st with clock := ck1) env body =
        (st' with clock := ck2, ret)
End

Definition eval_true_def:
  eval_true st env e ⇔ eval_exp st env e (BoolV T)
End

Definition valid_def:
  valid e = ∀st env. eval_true st env e
End

Overload "⊢" = “valid”;

Definition conj_def:
  conj [] = Lit (BoolL T) ∧
  conj [x] = x ∧
  conj (x::xs) = BinOp And (x) (conj xs)
End

Overload "imp" = “BinOp Imp”
Overload "int_lt" = “BinOp Lt”
Overload "dfy_eq" = “BinOp Eq”

Overload "not" = “UnOp Not”

Definition CanEval_def: (* beautiful or not.. *)
  CanEval e = dfy_eq e e
End

Theorem eval_true_CanEval:
  eval_true st env (CanEval e) ⇒ ∃v. eval_exp st env e v
Proof
  gvs [eval_true_def,CanEval_def,evaluate_exp_def,eval_exp_def]
  \\ gvs [AllCaseEqs(),PULL_EXISTS,do_sc_def,do_bop_def]
  \\ cheat
QED

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
    stmt_wp m [imp g (conj pre1); imp (not g) (conj pre2)] (If g s1 s2) post ens decs
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
  \\ cheat
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

Theorem evaluate_stmt_MetCall:
  get_member mname env.prog =
    SOME (Method name ins reqs ens rds decrs outs mods body) ∧
  LIST_REL (eval_exp st env) args in_vs ∧
  set_up_call st (MAP FST ins) in_vs (MAP FST outs) = SOME st1 ∧
  eval_stmt st1 env body st2 (Rstop Sret) ∧
  OPT_MMAP (read_local st2.locals) out_ns = SOME out_vs ∧
  LENGTH rets = LENGTH out_vs ∧
  assign_values (restore_caller st2 st0) env rets out_vs = (st',Rcont)
  ⇒
  eval_stmt st env (MetCall rets mname args) st' Rcont
Proof
  cheat
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
  >~ [‘MetCall rets mname args’] >-
   (irule_at Any evaluate_stmt_MetCall \\ gvs []
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
