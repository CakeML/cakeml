(*
  Calculus for VCG for Dafny
*)
Theory dafny_wp_calc
Ancestors
  dafny_evaluate
Libs
  preamble


(*
  TODO:
    - add ‘Let [(n,e1);(m,e2)] rest’ to expressions
    - exp needs to take two states
    - and Old switches to old state
*)

Overload False = “Lit (BoolL F)”;

Definition eval_true_def:
  eval_true st env e ⇔
    ∃ck1 ck2.
      evaluate_exp (st with clock := ck1) env e =
        (st with clock := ck2, Rval (BoolV T))
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

Overload "not" = “UnOp Not”

Inductive stmt_wp:
[~Skip:]
  ∀m ens post.
    stmt_wp m post Skip (post:exp list) (ens:exp list)
[~Assert:]
  ∀m ens post.
    stmt_wp m (e::post) (Assert e) (post:exp list) (ens:exp list)
[~Return:]
  ∀m ens post.
    stmt_wp m (ens:exp list) Return (post:exp list) (ens:exp list)
[~Then:]
  ∀m s1 s2 pre1 pre2 post ens.
    stmt_wp m pre1 s1 pre2 ens ∧
    stmt_wp m pre2 s2 post ens
    ⇒
    stmt_wp m pre1 (Then s1 s2) post ens
[~If:]
  ∀m s1 s2 pre1 pre2 post ens.
    stmt_wp m pre1 s1 post ens ∧
    stmt_wp m pre2 s2 post ens
    ⇒
    stmt_wp m [imp g (conj pre1); imp (not g) (conj pre2)] (If g s1 s2) post ens
[~Assign:]
  ∀m ret_names exps l post ens.
    LIST_REL (λr (n,ty). r = VarLhs n) (MAP FST l) ret_names ∧
    LIST_REL (λr e. r = ExpRhs e) (MAP SND l) exps
    ⇒
    stmt_wp m [Let (ZIP (ret_names,exps)) (conj post)] (Assign l) post ens
[~MetCall:]
  ∀m mname mins mreqs mens mreads mdecreases mouts mmods mbody ret_names args ens post rets.
    Method mname mins mreqs mens mreads mdecreases mouts mmods mbody ∈ m ∧
    LENGTH mins = LENGTH args ∧
    LIST_REL (λr rn. r = VarLhs (FST rn)) rets ret_names ∧
    ⊢ (imp (conj mens) (Let (ZIP (ret_names,MAP (λ(m,ty). Var m) mouts)) (conj post)))
    ⇒
    stmt_wp m [Let (ZIP (mins,args)) (conj mreqs)] (MetCall rets mname args) post ens
End

Inductive adjust_calls:
  T ⇒
  adjust_calls decreases mutrec body adjusted_body
End

Inductive mspec:
[~empty:]
  mspec {}
[~nonrec:]
  mspec m ∧
  stmt_wp m wp_pre body [False] ens ∧
  ⊢ (imp (conj reqs) (conj wp_pre))
  ⇒
  mspec ((Method name ins reqs ens reads decreases outs mods body) INSERT m)
[~mutrec:]
  mspec m ∧
  (∀name ins reqs ens reads outs decreases mods body.
     Method name ins reqs ens reads decreases outs mods body ∈ mutrec ⇒
     ∃adjusted_body.
       adjust_calls decreases mutrec body adjusted_body ∧
       stmt_wp (mutrec ∪ m) reqs adjusted_body [False] ens)
  ⇒
  mspec (mutrec ∪ m)
End

Definition eval_stmt_def:
  eval_stmt st env body st' ret =
    ∃ck1 ck2.
      evaluate_stmt (st with clock := ck1) env body =
        (st' with clock := ck2, ret)
End

Definition conditions_hold_def:
  conditions_hold st env ⇔ EVERY (eval_true st env)
End

Definition compatible_env_def:
  compatible_env env m = ¬env.is_running
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

Theorem stmt_wp_sound:
  ∀m reqs stmt post ens.
    stmt_wp m reqs stmt post ens ⇒
    ∀st env.
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

Theorem False_thm:
  conditions_hold st env [False] = F
Proof
  simp [conditions_hold_def,eval_true_def,evaluate_exp_def]
QED

Theorem mspec_sound:
  ∀m. mspec m ⇒
      ∀name ins reqs ens reads decreases outs mods body env.
        Method name ins reqs ens reads decreases outs mods body ∈ m ⇒
        ∀st. conditions_hold st env reqs ∧ compatible_env env m ⇒
             ∃st'. eval_stmt st env body st' (Rstop Sret) ∧
                   conditions_hold st' env ens
Proof
  ho_match_mp_tac mspec_ind
  \\ rpt conj_tac
  >- (* empty *) simp []
  >- (* nonrec *)
   (rpt strip_tac
    \\ reverse $ gvs [IN_INSERT]
    >-
     (last_x_assum drule
      \\ disch_then irule
      \\ gvs [compatible_env_def])
    \\ drule_all imp_conditions_hold \\ strip_tac
    \\ drule stmt_wp_sound
    \\ disch_then drule
    \\ impl_tac
    >- gvs [compatible_env_def]
    \\ strip_tac
    \\ gvs [False_thm]
    \\ Cases_on ‘ret’ \\ gvs []
    \\ rename [‘eval_stmt _ _ _ _ (Rstop ret)’] \\ Cases_on ‘ret’ \\ gvs []
    \\ first_x_assum $ irule_at $ Pos hd \\ asm_rewrite_tac [])
  (*mutrec *)
  \\ rpt strip_tac
  \\ reverse $ gvs [IN_UNION]
  >-
   (last_x_assum drule
    \\ disch_then irule
    \\ gvs [compatible_env_def])
  \\ cheat
QED

