(*
  Calculus for VCG for Dafny
*)
Theory dafny_wp_calc
Ancestors
  integer result_monad topological_sort
  dafny_ast dafny_semanticPrimitives dafnyProps
  dafny_evaluate dafny_evaluateProps dafny_eval_rel
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

Definition is_ArrT_def:
  is_ArrT (ArrT _ ) = T ∧
  is_ArrT _ = F
End

Definition dest_ArrT_def:
  dest_ArrT (ArrT t) = return t ∧
  dest_ArrT _ = fail «dest_ArrT: Not ArrT»
End

Definition get_type_def:
  get_type _ (Lit l) =
  (case l of
   | BoolL _ => return BoolT
   | IntL _ => return IntT
   | StrL _ => return StrT) ∧
  get_type ls (Var v) =
  (case ALOOKUP ls v of
   | NONE => fail «get_type:Var: Could not find variable in type context»
   | SOME ty => return ty) ∧
  get_type ls (If grd thn els) =
  do
    grd_ty <- get_type ls grd;
    () <- if grd_ty = BoolT then return () else
            (fail «get_type:If: Guard is not of type bool»);
    thn_ty <- get_type ls thn;
    els_ty <- get_type ls els;
    () <- if thn_ty = els_ty then return () else
            (fail «get_type:If: Arms have different types»);
    return thn_ty
  od ∧
  get_type ls (UnOp uop e) =
  do
    e_ty <- get_type ls e;
    (case uop of
     | Not => if e_ty = BoolT then return e_ty else
                (fail «get_type:UnOp:Not: Expected bool type»))
  od ∧
  get_type ls (BinOp bop e₀ e₁) =
  do
    e₀_ty <- get_type ls e₀;
    e₁_ty <- get_type ls e₁;
    (case bop of
     | Lt => if e₀_ty = IntT ∧ e₁_ty = IntT then return BoolT else
               (fail «get_type:BinOp:Lt: Expected int types»)
     | Le => if e₀_ty = IntT ∧ e₁_ty = IntT then return BoolT else
               (fail «get_type:BinOp:Le: Expected int types»)
     | Ge => if e₀_ty = IntT ∧ e₁_ty = IntT then return BoolT else
               (fail «get_type:BinOp:Ge: Expected int types»)
     | Eq => if e₁_ty  = e₀_ty then return BoolT else
               (fail «get_type:BinOp:Eq: Expected same types»)
     | Neq => if e₁_ty  = e₀_ty then return BoolT else
                (fail «get_type:BinOp:Neq: Expected same types»)
     | Sub => if e₀_ty = IntT ∧ e₁_ty = IntT then return IntT else
                (fail «get_type:BinOp:Sub: Expected int types»)
     | Add => if e₀_ty = IntT ∧ e₁_ty = IntT then return IntT else
                (fail «get_type:BinOp:Add: Expected int types»)
     | Mul => if e₀_ty = IntT ∧ e₁_ty = IntT then return IntT else
                (fail «get_type:BinOp:Mul: Expected int types»)
     | Div => if e₀_ty = IntT ∧ e₁_ty = IntT then return IntT else
                (fail «get_type:BinOp:Div: Expected int types»)
     | Mod => if e₀_ty = IntT ∧ e₁_ty = IntT then return IntT else
                (fail «get_type:BinOp:Mod: Expected int types»)
     | And => if e₀_ty = BoolT ∧ e₁_ty = BoolT then return BoolT else
                (fail «get_type:BinOp:And: Expected bool types»)
     | Or => if e₀_ty = BoolT ∧ e₁_ty = BoolT then return BoolT else
               (fail «get_type:BinOp:Or: Expected bool types»)
     | Imp => if e₀_ty = BoolT ∧ e₁_ty = BoolT then return BoolT else
                (fail «get_type:BinOp:Imp: Expected bool types»))
  od ∧
  get_type ls (ArrLen arr) =
  do
    arr_ty <- get_type ls arr;
    () <- if is_ArrT arr_ty then return () else
            (fail «get_type:ArrLen: Expected array type»);
    return IntT
  od ∧
  get_type ls (ArrSel arr idx) =
  do
    idx_ty <- get_type ls idx;
    () <- if idx_ty = IntT then return () else
            (fail «get_type:ArrSel: Expected int index»);
    arr_ty <- get_type ls arr;
    dest_ArrT arr_ty
  od ∧
  get_type _ _ = fail «get_type: Unsupported expression»
End

Definition get_types_def:
  get_types ls tys = result_mmap (get_type ls) tys
End

Definition get_vars_exp_def:
  get_vars_exp (Lit _) = [] ∧
  get_vars_exp (Var v) = [v] ∧
  get_vars_exp (If grd thn els) =
    get_vars_exp grd ++ get_vars_exp thn ++ get_vars_exp els ∧
  get_vars_exp (UnOp _ e) = get_vars_exp e ∧
  get_vars_exp (BinOp _ e₀ e₁) = get_vars_exp e₀ ++ get_vars_exp e₁ ∧
  get_vars_exp (ArrLen arr) = get_vars_exp arr ∧
  get_vars_exp (ArrSel arr idx) = get_vars_exp arr ++ get_vars_exp idx ∧
  get_vars_exp (FunCall _ args) = FLAT (MAP get_vars_exp args) ∧
  get_vars_exp (Forall _ e) = get_vars_exp e ∧
  get_vars_exp (Old e) = get_vars_exp e ∧
  get_vars_exp (Let binds body) =
    FLAT (MAP get_vars_exp (MAP SND binds)) ++ get_vars_exp body ∧
  get_vars_exp (ForallHeap mods term) =
    FLAT (MAP get_vars_exp mods) ++ get_vars_exp term
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_exp_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Definition get_vars_lhs_exp_def:
  get_vars_lhs_exp (VarLhs v) = [v] ∧
  get_vars_lhs_exp (ArrSelLhs arr idx) =
    get_vars_exp arr ++ get_vars_exp idx
End

Definition get_vars_rhs_exp_def:
  get_vars_rhs_exp (ExpRhs e) = get_vars_exp e ∧
  get_vars_rhs_exp (ArrAlloc len init) =
    get_vars_exp len ++ get_vars_exp init
End

Definition get_vars_stmt_def:
  get_vars_stmt Skip = [] ∧
  get_vars_stmt (Assert e) = get_vars_exp e ∧
  get_vars_stmt (Then stmt₁ stmt₂) =
    get_vars_stmt stmt₁ ++ get_vars_stmt stmt₂ ∧
  get_vars_stmt (Dec _ scope) = get_vars_stmt scope ∧
  get_vars_stmt (Assign ass) =
    FLAT (MAP get_vars_lhs_exp (MAP FST ass)) ++
    FLAT (MAP get_vars_rhs_exp (MAP SND ass)) ∧
  get_vars_stmt (While grd invs decrs mods body) =
    get_vars_exp grd ++ FLAT (MAP get_vars_exp invs) ++
    FLAT (MAP get_vars_exp decrs) ++ FLAT (MAP get_vars_exp mods) ++
    get_vars_stmt body ∧
  get_vars_stmt (Print e _) = get_vars_exp e ∧
  get_vars_stmt (MetCall lhss _ args) =
    FLAT (MAP get_vars_lhs_exp lhss) ++ FLAT (MAP get_vars_exp args) ∧
  get_vars_stmt Return = []
End

Definition assigned_in_def:
  assigned_in (Then stmt₁ stmt₂) v =
    (assigned_in stmt₁ v ∨ assigned_in stmt₂ v) ∧
  assigned_in (If _ stmt₁ stmt₂) v =
    (assigned_in stmt₁ v ∨ assigned_in stmt₂ v) ∧
  assigned_in (Dec n_ty stmt) v =
    (if v = FST n_ty then F else assigned_in stmt v) ∧
  assigned_in (Assign ass) v = MEM (VarLhs v) (MAP FST ass) ∧
  assigned_in (While grd invs decrs mods body) v = assigned_in body v ∧
  assigned_in (MetCall lhss _ _) v = MEM (VarLhs v) lhss ∧
  assigned_in _ v = F
End

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

Definition require_def:
  require p ⇔ freevars p = ∅ ∧ ⊢ p
End

Definition dec_assum_def:
  dec_assum v e = dfy_eq (Var v) e
End

Inductive stmt_wp:
[~Skip:]
  ∀m ens post.
    stmt_wp m post Skip (post:exp list) (ens:exp list) decs (ls:(mlstring # type) list)
[~Assert:]
  ∀m ens post e.
    stmt_wp m (e::post) (Assert e) (post:exp list) (ens:exp list) decs ls
[~Return:]
  ∀m ens post.
    stmt_wp m (ens:exp list) Return (post:exp list) (ens:exp list) decs ls
[~Then:]
  ∀m s1 s2 pre1 pre2 post ens.
    stmt_wp m pre1 s1 pre2 ens decs ls ∧
    stmt_wp m pre2 s2 post ens decs ls
    ⇒
    stmt_wp m pre1 (Then s1 s2) post ens decs ls
[~If:]
  ∀m s1 s2 pre1 pre2 post ens g.
    stmt_wp m pre1 s1 post ens decs ls ∧
    stmt_wp m pre2 s2 post ens decs ls
    ⇒
    stmt_wp m [IsBool g; imp g (conj pre1); imp (not g) (conj pre2)]
      (If g s1 s2) post ens decs ls
[~Dec:]
  ∀m wp stmt post ens decs n ty ls.
    stmt_wp m wp stmt post ens decs ((n,ty)::ls) ∧
    EVERY (λe. n ∉ freevars e) wp ∧
    EVERY (λe. n ∉ freevars e) post ∧
    EVERY (λe. n ∉ freevars e) ens ∧
    ¬MEM n (MAP FST ls)
    ⇒
    stmt_wp m wp (Dec (n,ty) stmt) post ens decs ls
[~Assign:]
  ∀m ret_names exps l post ens rhs_tys.
    (MAP FST l) = (MAP VarLhs ret_names) ∧
    (MAP SND l) = (MAP ExpRhs exps) ∧
    ALL_DISTINCT ret_names ∧
    LENGTH exps = LENGTH ret_names ∧
    set ret_names ⊆ set (MAP FST ls) ∧
    get_types ls exps = INR rhs_tys ∧
    get_types ls (MAP Var ret_names) = INR lhs_tys ∧
    lhs_tys = rhs_tys
    ⇒
    stmt_wp m [Let (ZIP (ret_names,exps)) (conj post)] (Assign l) post ens decs ls
[~While:]
  ∀m guard invs ds mods body post ens decs ls ds_vars.
    DISJOINT (set ds_vars) (set (MAP FST ls ++ get_vars_stmt body)) ∧
    LENGTH ds_vars = LENGTH ds ∧
    get_type ls guard = INR BoolT ∧
    (* when executing the body, invs are maintained *)
    require (Foralls (MAP (λv. (v,IntT)) ds_vars ++ ls)
               (imp (conj (guard :: invs ++ MAP2 dec_assum ds_vars ds))
                    (conj body_wp))) ∧
    stmt_wp m body_wp body
      (invs ++ MAP CanEval ds ++ decreases_check (0, ds) (0, MAP Var ds_vars))
      ens decs (MAP (λv. (v,IntT)) ds_vars ++ ls)
    ⇒
    stmt_wp m (invs ++ MAP CanEval ds ++
               (* on exit of loop, invs and not guard imply post *)
               [Foralls (FILTER (λ(v,ty). assigned_in body v) ls)
                  (imp (conj (not guard :: invs)) (conj post))])
            (While guard invs ds mods body) post ens decs ls
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
    EVERY (λe. freevars e ⊆ set (MAP FST mspec.ins) ∧ no_Old e) mspec.decreases ∧
    EVERY (λe. freevars e ⊆ set (MAP FST mspec.ins ++ MAP FST mspec.outs) ∧
               no_Old e) mspec.ens ∧
    set ret_names ⊆ set (MAP FST ls) ∧
    get_types ls args = INR (MAP SND mspec.ins) ∧
    get_types ls (MAP Var ret_names) = INR (MAP SND mspec.outs)
    ⇒
    stmt_wp m (Let (ZIP (MAP FST mspec.ins,args)) (conj mspec.reqs) ::
               MAP CanEval args ++
               decreases_check (mspec.rank,
                                MAP (Let (ZIP (MAP FST mspec.ins,args))) mspec.decreases)
                               (wrap_old decs) ++
               [Foralls (ZIP (ret_names, MAP SND mspec.outs))
                  (imp (Let (ZIP(MAP FST mspec.ins ++ MAP FST mspec.outs,
                                 args              ++ MAP Var ret_names))
                          (conj mspec.ens))
                       (conj post))])
              (MetCall rets mname args) post ens decs ls
End

(* TODO rename definition *)
Definition wrap_Old_def:
  wrap_Old vs (Var v) =
  (if v ∈ vs then Old (Var v) else Var v) ∧
  wrap_Old _ (Lit l) = Lit l ∧
  wrap_Old vs (If grd thn els) =
  If (wrap_Old vs grd) (wrap_Old vs thn) (wrap_Old vs els) ∧
  wrap_Old vs (UnOp uop e) =
  UnOp uop (wrap_Old vs e) ∧
  wrap_Old vs (BinOp bop e₀ e₁) =
  BinOp bop (wrap_Old vs e₀) (wrap_Old vs e₁) ∧
  wrap_Old vs (ArrLen arr) =
  ArrLen (wrap_Old vs arr) ∧
  wrap_Old vs (ArrSel arr idx) =
  ArrSel (wrap_Old vs arr) (wrap_Old vs idx) ∧
  wrap_Old vs (FunCall name args) =
  FunCall name (MAP (wrap_Old vs) args) ∧
  wrap_Old vs (Forall (vn,vt) term) =
  Forall (vn,vt) (wrap_Old (vs DELETE vn) term) ∧
  wrap_Old vs (Old e) =
  Old (wrap_Old vs e) ∧
  wrap_Old vs (Let binds body) =
  Let (MAP (λ(n,e). (n, wrap_Old vs e)) binds)
      ((wrap_Old (vs DIFF (set (MAP FST binds)))) body) ∧
  wrap_Old vs (ForallHeap mods term) =
  ForallHeap (MAP (wrap_Old vs) mods) (wrap_Old vs term)
End

Definition proved_methods_def:
  proved_methods m ⇔
    ∀name mspec body.
      Method name mspec body ∈ m ⇒
      ∃wp_pre.
        stmt_wp m wp_pre body [False]
                (MAP (wrap_Old (set (MAP FST mspec.ins))) mspec.ens ++
                 MAP (CanEval o Var o FST) mspec.outs)
                (mspec.rank, mspec.decreases)
                (mspec.ins ++ mspec.outs) ∧
        ∃p.
          p = Foralls mspec.ins (imp (conj mspec.reqs) (conj wp_pre)) ∧
          freevars p = {} ∧
          ⊢ p
End

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

Triviality eval_true_swap_locals_alt:
  ALOOKUP l' = ALOOKUP l ⇒
  eval_true (st with locals := l') env e =
  eval_true (st with locals := l) env e
Proof
  strip_tac
  \\ simp [eval_true_def]
  \\ drule eval_exp_swap_locals_alt \\ simp []
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

(* TODO Move to dafnyProps *)
Theorem is_some_alookup_update_local_aux:
  ∀(xs: (mlstring # value option) list) n.
    IS_SOME (ALOOKUP xs n) ⇒
    ∃ys. update_local_aux xs n v' = SOME ys ∧
         ALOOKUP ys = ALOOKUP ((n,SOME v')::xs)
Proof
  Induct >- (simp [])
  \\ qx_genl_tac [‘x’, ‘n’]
  \\ gvs [IS_SOME_EXISTS, PULL_EXISTS]
  \\ namedCases_on ‘x’ ["xn xv"] \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  >-
   (simp [update_local_aux_def]
    \\ simp [FUN_EQ_THM])
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then assume_tac
  \\ simp [update_local_aux_def]
  \\ CASE_TAC \\ gvs []
  \\ gvs [FUN_EQ_THM]
  \\ strip_tac
  \\ IF_CASES_TAC \\ gvs []
QED

(* TODO Move to dafnyProps *)
Theorem is_some_alookup_update_local:
  IS_SOME (ALOOKUP st.locals n) ⇒
  ∃l. update_local st n v = SOME (st with locals := l) ∧
      ALOOKUP l = ALOOKUP ((n, SOME v)::st.locals)
Proof
  strip_tac
  \\ rpt strip_tac
  \\ drule is_some_alookup_update_local_aux
  \\ disch_then $ qspec_then ‘v’ assume_tac
  \\ gvs [update_local_def, state_component_equality]
QED

Definition is_initialized_def:
  is_initialized locals var ⇔
    ∃val. ALOOKUP locals var = SOME (SOME val)
End

Theorem eval_true_CanEval_Var:
  eval_true st env (CanEval (Var v)) ⇔ is_initialized st.locals v
Proof
  fs [eval_true_def,eval_exp_def,evaluate_exp_def,CanEval_def,read_local_def]
  \\ simp [AllCaseEqs(),PULL_EXISTS,do_sc_def,do_bop_def]
  \\ simp [state_component_equality,SF CONJ_ss,is_initialized_def]
QED

Theorem can_eval_vars:
  ∀ns.
    EVERY (eval_true st env) (MAP CanEval (MAP Var ns)) ∧
    (∀n. is_initialized st.locals n ⇒ is_initialized l n) ⇒
    EVERY (eval_true (st' with locals := l) env) (MAP CanEval (MAP Var ns))
Proof
  Induct >- (gvs [])
  \\ qx_gen_tac ‘n’
  \\ rpt strip_tac \\ gvs []
  \\ gvs [eval_true_CanEval_Var]
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

Triviality ALOOKUP_APPEND_same_prefix:
  ALOOKUP ys = ALOOKUP zs ⇒ ALOOKUP (xs ++ ys) = ALOOKUP (xs ++ zs)
Proof
  simp [FUN_EQ_THM, ALOOKUP_APPEND]
QED

Definition locals_ok_def:
  locals_ok (locals: (mlstring # type) list)
            (s_locals: (mlstring # value option) list) ⇔
    (∀n ty.
       MEM (n,ty) locals ⇒
       ∃oval. ALOOKUP s_locals n = SOME oval ∧
              ∀val. oval = SOME val ⇒ val ∈ all_values ty) ∧
    ALL_DISTINCT (MAP FST locals)
End

Definition strict_locals_ok_def:
  strict_locals_ok (locals: (mlstring # type) list)
                   (s_locals: (mlstring # value option) list) ⇔
    (∀n ty.
       MEM (n,ty) locals ⇒
       ∃val. ALOOKUP s_locals n = SOME (SOME val) ∧ val ∈ all_values ty) ∧
    ALL_DISTINCT (MAP FST locals)
End

Triviality strict_locals_ok_IMP_LIST_REL:
  ∀vs st_locals.
    strict_locals_ok vs st_locals ⇒
    ∃xs.
      LIST_REL
        (λ(n,ty) (m,x).
           m = n ∧ ALOOKUP st_locals n = SOME x ∧
           ∃v. v ∈ all_values ty ∧ x = SOME v)
        vs xs
Proof
  Induct \\ gvs []
  \\ namedCases ["n ty"]
  \\ gvs [strict_locals_ok_def, PULL_EXISTS]
  \\ rpt strip_tac
  \\ first_assum $ qspecl_then [‘n’, ‘ty’] mp_tac
  \\ impl_tac >- (simp [])
  \\ rpt strip_tac
  \\ rename [‘ALOOKUP _ _ = SOME (SOME val)’]
  \\ qexists ‘(n, SOME val)’ \\ simp []
QED

Triviality LIST_REL_ALOOKUP:
  ∀xs vs.
    LIST_REL
      (λ(n,ty) (m,x).
         m = n ∧ ALOOKUP st_locals n = SOME x ∧
         ∃v. v ∈ all_values ty ∧ x = SOME v) vs xs ∧
    MEM x (MAP FST xs) ⇒
    ALOOKUP xs x = ALOOKUP st_locals x
Proof
  Induct \\ gvs []
  \\ gvs [PULL_EXISTS]
  \\ qx_genl_tac [‘x₁’, ‘v₁’]
  \\ namedCases_on ‘x₁’ ["n oval"]
  \\ namedCases_on ‘v₁’ ["m ty"]
  \\ rpt strip_tac \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum drule \\ simp []
QED

Triviality MEM_MAP_FST:
  ∀xs. MEM (x,y) xs ⇒ MEM x (MAP FST xs)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac \\ gvs []
QED

Triviality ALOOKUP_MEM_FST:
  ALOOKUP xs x = SOME y ⇒ MEM x (MAP FST xs)
Proof
  rpt strip_tac
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ drule MEM_MAP_FST \\ simp []
QED

Theorem forall_imp_conditions_hold:
  ⊢ (Foralls vs (imp (conj reqs) (conj wp_pre))) ∧
  ALL_DISTINCT (MAP FST vs) ∧
  conditions_hold st env reqs ∧
  strict_locals_ok vs st.locals ⇒
  conditions_hold st env wp_pre
Proof
  rw [valid_def]
  \\ last_x_assum $ qspecl_then [‘st’,‘env’] assume_tac
  \\ dxrule eval_true_Foralls_distinct
  \\ disch_then $ dxrule_then assume_tac
  \\ drule strict_locals_ok_IMP_LIST_REL
  \\ disch_then $ qx_choose_then ‘xs’ mp_tac
  \\ strip_tac
  \\ first_x_assum $ qspec_then ‘xs’ mp_tac
  \\ impl_tac >-
   (pop_assum mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ PairCases \\ PairCases \\ gvs [])
  \\ simp []
  \\ ‘ALOOKUP (xs ++ st.locals) = ALOOKUP st.locals’ by
    (simp [FUN_EQ_THM]
     \\ strip_tac
     \\ simp [ALOOKUP_APPEND]
     \\ CASE_TAC \\ gvs []
     \\ drule ALOOKUP_MEM_FST \\ strip_tac
     \\ drule_all LIST_REL_ALOOKUP \\ simp [])
  \\ drule eval_true_swap_locals_alt \\ simp [] \\ disch_then kall_tac
  \\ strip_tac
  \\ gvs [conditions_hold_def]
  \\ drule eval_true_mp
  \\ gvs [eval_true_conj_every]
QED

Theorem locals_ok_append_left:
  locals_ok (xs ++ ys) ls ⇔
    locals_ok xs ls ∧ locals_ok ys ls ∧
    ALL_DISTINCT (MAP FST xs ++ MAP FST ys)
Proof

  iff_tac \\ strip_tac
  >- (gvs [locals_ok_def, ALL_DISTINCT_APPEND])
  \\ gvs [locals_ok_def,SF DNF_ss]
QED

Theorem strict_locals_ok_IMP_locals_ok:
  strict_locals_ok xs ls ⇒ locals_ok xs ls
Proof
  simp [locals_ok_def,strict_locals_ok_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality locals_ok_is_some_alookup:
  locals_ok locals st_locals ⇒
  EVERY (λn. IS_SOME (ALOOKUP st_locals n)) (MAP FST locals)
Proof
  simp [locals_ok_def, EVERY_MEM, MEM_MAP]
  \\ rpt strip_tac \\ gvs []
  \\ rename [‘MEM l _’]
  \\ namedCases_on ‘l’ ["n ty"]
  \\ last_x_assum drule
  \\ rpt strip_tac \\ simp []
QED

Triviality subset_every:
  set xs ⊆ set ys ∧ EVERY P ys ⇒ EVERY P xs
Proof
  simp [EVERY_MEM, SUBSET_DEF]
QED

Theorem IMP_assi_values:
  ∀ret_names out_vs st.
    EVERY (λn. IS_SOME (ALOOKUP st.locals n)) ret_names ∧
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
  \\ drule is_some_alookup_update_local
  \\ disch_then $ qspec_then ‘v’ mp_tac
  \\ disch_then $ qx_choose_then ‘l’ mp_tac
  \\ strip_tac
  \\ irule_at (Pos hd) assi_value_VarLhs
  \\ first_assum $ irule_at (Pos hd)
  \\ last_x_assum $ qspecl_then [‘out_vs'’, ‘st with locals := l’] mp_tac
  \\ simp []
  \\ impl_tac >-
   (gvs [EVERY_MEM]
    \\ rpt strip_tac
    \\ IF_CASES_TAC \\ gvs [])
  \\ disch_then $ qx_choose_then ‘l₁’ mp_tac
  \\ strip_tac
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ irule ALOOKUP_APPEND_same_prefix \\ simp []
QED

Triviality IMP_assi_values_distinct:
  ∀ret_names out_vs st.
    EVERY (λn. IS_SOME (ALOOKUP st.locals n)) ret_names ∧
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

(* TODO Move to dafny_eval_rel *)
Theorem eval_exp_with_clock:
  eval_exp (st with clock := ck) = eval_exp st
Proof
  gvs [FUN_EQ_THM, eval_exp_def]
QED

(* TODO Move to dafny_eval_rel *)
Theorem evaluate_exps_eval_exp:
  ∀es vs st.
    evaluate_exps st env es = (st', Rval vs) ⇒
    LIST_REL (eval_exp st env) es vs
Proof
  Induct >- (gvs [evaluate_exp_def])
  \\ qx_genl_tac [‘e’, ‘vs’, ‘st’]
  \\ simp [evaluate_exp_def]
  \\ namedCases_on ‘evaluate_exp st env e’ ["st₁ r"] \\ gvs []
  \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
  \\ namedCases_on ‘evaluate_exps st₁ env es’ ["st₂ r"] \\ gvs []
  \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
  \\ rpt strip_tac \\ gvs []
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
  \\ last_x_assum $ drule_then assume_tac
  \\ gvs [eval_exp_with_clock]
  \\ simp [eval_exp_def]
  \\ qexists ‘st.clock’ \\ simp []
  \\ simp [state_component_equality]
QED

Theorem eval_true_Let_IMP:
  eval_true st env (Let (ZIP (ns,exps)) p) ∧ LENGTH exps = LENGTH ns ⇒
  ∃vs. LIST_REL (eval_exp st env) exps vs
Proof
  rpt strip_tac
  \\ gvs [eval_true_def, eval_exp_def, evaluate_exp_def, AllCaseEqs()]
  \\ drule_then assume_tac evaluate_exps_eval_exp
  \\ gvs [eval_exp_with_clock]
  \\ first_assum $ irule_at (Pos hd)
QED

(* TODO move to dafny_evaluateprops *)
Theorem evaluate_rhs_exps_exprhs_eq:
  ∀es st env.
    evaluate_rhs_exps st env (MAP ExpRhs es) = evaluate_exps st env es
Proof
  Induct >- (simp [evaluate_rhs_exps_def, evaluate_exp_def])
  \\ qx_genl_tac [‘e’, ‘st’, ‘env’]
  \\ simp [evaluate_rhs_exps_def, evaluate_exp_def, evaluate_rhs_exp_def]
QED

Theorem IMP_eval_rhs_exps_MAP_ExpRhs:
  LIST_REL (eval_exp st env) exps vs ⇒
  eval_rhs_exps st env (MAP ExpRhs exps) st vs
Proof
  strip_tac
  \\ drule eval_exp_evaluate_exps
  \\ simp [eval_rhs_exps_def, evaluate_rhs_exps_exprhs_eq]
QED

Theorem eval_exp_swap_state:
  eval_exp st2 env e v ∧
  (∀ck. (st3 with clock := ck) = (st2 with clock := ck)) ⇒
  eval_exp st3 env e v
Proof
  simp [eval_exp_def]
QED

Triviality conj_MAP_wrap_Old:
  ∀xs vs. conj (MAP (wrap_Old vs) xs) = wrap_Old vs (conj xs)
Proof
  ho_match_mp_tac conj_ind \\ fs [conj_def,wrap_Old_def]
QED

(* *** *)

(* TODO Move to dafnyProps? *)
Triviality do_cond_none:
  do_cond v (x₀:exp) (x₁:exp) = NONE ⇒ do_cond v (y₀:exp) (y₁:exp) = NONE
Proof
  Cases_on ‘v’ \\ gvs [do_cond_def]
QED

Triviality fst_lambda:
  FST ∘ (λ(x, y). (x, f y)) = FST
Proof
  simp [FUN_EQ_THM] \\ Cases \\ simp []
QED

Triviality snd_lambda:
  SND ∘ (λ(x, y). (x, f y)) = f ∘ SND
Proof
  simp [FUN_EQ_THM] \\ Cases \\ simp []
QED

Triviality ALOOKUP_ZIP_SOME:
  ∀A B x. LENGTH A = LENGTH B ∧ MEM x A ⇒ ∃v. ALOOKUP (ZIP (A,B)) x = SOME v
Proof
  rpt strip_tac
  \\ Cases_on ‘ALOOKUP (ZIP (A,B)) x’
  \\ gvs [ALOOKUP_ZIP_FAIL]
QED

Triviality index_array_with_locals:
  index_array (st with locals := l) arr idx = index_array st arr idx
Proof
  gvs [index_array_def]
QED

Triviality set_up_call_with_clock_locals:
  set_up_call (st with <|clock := ck; locals := l|>) in_ns in_vs outs =
  set_up_call (st with clock := ck) in_ns in_vs outs
Proof
  gvs [set_up_call_def]
QED

Triviality not_mem_alookup_zip_none =
SRULE [AND_IMP_INTRO] $ iffRL ALOOKUP_ZIP_FAIL

Theorem evaluate_exp_wrap_Old_locals:
  (∀st env e' nss e st' r l.
     evaluate_exp st env e' = (st', r) ∧
     e' = wrap_Old nss e ∧
     (∀n. n ∈ nss ⇒
          ∃v. read_local st.locals_old n = SOME v ∧
              ALOOKUP l n = SOME (SOME v)) ∧
     (∀n. n ∉ nss ⇒ ALOOKUP l n = ALOOKUP st.locals n) ∧
     ¬env.is_running ⇒
     evaluate_exp (st with locals := l) env e = (st' with locals := l, r)) ∧
  (∀st env es' nss es st' r l.
     evaluate_exps st env es' = (st', r) ∧
     es' = MAP (wrap_Old nss) es ∧
     (∀n. n ∈ nss ⇒
          ∃v. read_local st.locals_old n = SOME v ∧
              ALOOKUP l n = SOME (SOME v)) ∧
     (∀n. n ∉ nss ⇒ ALOOKUP l n = ALOOKUP st.locals n) ∧
     ¬env.is_running ⇒
     evaluate_exps (st with locals := l) env es = (st' with locals := l, r))
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Var’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_exp_def, read_local_def, AllCaseEqs()])
  >~ [‘Lit’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_exp_def])
  >~ [‘If’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘If grd thn els’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp st env (wrap_Old nss grd)’ ["st₁ r₁"]
    \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ strip_tac \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘grd’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ namedCases_on ‘r₁’ ["v", "err"] \\ gvs []
    \\ namedCases_on ‘do_cond v (wrap_Old nss thn) (wrap_Old nss els)’
                     ["", "branch"]
    \\ gvs []
    >- (imp_res_tac do_cond_none \\ gvs [])
    \\ imp_res_tac do_cond_some_cases \\ gvs [do_cond_def]
    >- (last_x_assum $ qspecl_then [‘nss’, ‘thn’] mp_tac \\ simp [])
    \\ last_x_assum $ qspecl_then [‘nss’, ‘els’] mp_tac \\ simp [])
  >~ [‘Forall’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘Forall (vn,vt) e’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def, eval_forall_def, wrap_Old_def]
    \\ simp [GSYM AND_IMP_INTRO]
    \\ strip_tac \\ gvs []
    \\ ‘∀v. SND (evaluate_exp (push_local st vn v) env
                              (wrap_Old (nss DELETE vn) e)) =
            SND (evaluate_exp (push_local (st with locals := l) vn v) env e)’ by
      (gen_tac
       \\ namedCases_on
          ‘evaluate_exp (push_local st vn v) env (wrap_Old (nss DELETE vn) e)’
          ["s₁ r₁"]
       \\ gvs [snd_tuple]
       \\ last_x_assum drule
       \\ disch_then $ qspecl_then [‘nss DELETE vn’, ‘e’] mp_tac
       \\ simp [push_local_def]
       \\ disch_then $ irule_at (Pos hd)
       \\ rpt strip_tac \\ gvs [])
    \\ gvs [])
  >~ [‘Let’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘Let binds body’]
    \\ gvs [evaluate_exp_def]
    \\ gvs [UNZIP_MAP, fst_lambda, snd_lambda, MAP_MAP_o, MAP_ZIP]
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [GSYM MAP_MAP_o]
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exps _ _ wrapped_es’
    \\ namedCases_on ‘evaluate_exps st env wrapped_es’ ["st₁ r₁"] \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘MAP SND binds’] mp_tac
    \\ simp [Abbr ‘wrapped_es’, SF ETA_ss]
    \\ disch_then $ drule_all_then assume_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ imp_res_tac evaluate_exps_len_eq \\ gvs []
    (* unfold push_locals before we instantiate the IH, we qmatch gets the
       right evaluate_exp *)
    \\ simp [push_locals_def]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate_exp (_ with locals := lcls)’
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp st₁' _ wrapped_body’
    \\ namedCases_on ‘evaluate_exp st₁' env wrapped_body’ ["st₂ r₂"] \\ gvs []
    \\ last_x_assum $
                    qspecl_then [‘nss DIFF set (MAP FST binds)’, ‘body’] mp_tac
    \\ gvs [Abbr ‘wrapped_body’, Abbr ‘st₁'’]
    \\ gvs [push_locals_with_locals]
    \\ gvs [push_locals_def]
    \\ disch_then $ qspec_then ‘lcls’ mp_tac
    \\ gvs [Abbr ‘lcls’]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ impl_tac >-
     (rpt strip_tac
      >-
       (first_x_assum drule \\ strip_tac
        \\ first_assum $ irule_at (Pos hd)
        \\ DEP_REWRITE_TAC [map_lambda_pair_zip] \\ simp []
        \\ simp [ALOOKUP_APPEND]
        \\ simp [REVERSE_ZIP]
        \\ DEP_REWRITE_TAC [not_mem_alookup_zip_none]
        \\ simp [])
      >- (simp [ALOOKUP_APPEND])
      \\ simp [ALOOKUP_APPEND]
      \\ DEP_REWRITE_TAC [map_lambda_pair_zip] \\ simp []
      \\ simp [REVERSE_ZIP]
      \\ CASE_TAC \\ gvs []
      \\ gvs [ALOOKUP_ZIP_FAIL])
    \\ strip_tac \\ gvs []
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ gvs [state_component_equality]
    \\ gvs [DROP_APPEND])
  >~ [‘ForallHeap’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘ForallHeap mods e’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exps st env (MAP (λa. wrap_Old nss a) mods)’
                     ["s₁ r₁"]
    \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘mods’] mp_tac
    \\ simp [SF ETA_ss]
    \\ disch_then $ drule_all_then assume_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    >- (simp [state_component_equality])
    \\ namedCases_on ‘get_locs vs’ ["", "locs"] \\ gvs []
    >- (simp [state_component_equality])
    \\ rewrite_tac [GSYM AND_IMP_INTRO]
    \\ strip_tac \\ gvs []
    \\ simp [eval_forall_def]
    \\ ‘∀hs. SND (evaluate_exp (st with <|clock := ck; heap := hs|>) env
                               (wrap_Old nss e))
             = SND (evaluate_exp
                    (st with <|clock := ck; locals := l; heap := hs|>) env e)’
      by
      (gen_tac
       \\ namedCases_on
          ‘evaluate_exp (st with <|clock := ck; heap := hs|>) env
           (wrap_Old nss e)’
          ["s₁ r₁"]
       \\ gvs [snd_tuple]
       \\ last_x_assum drule
       \\ disch_then $ qspecl_then [‘nss’, ‘e’] mp_tac \\ gvs [])
    \\ gvs [])
  >~ [‘UnOp’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘UnOp uop e’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp st env (wrap_Old nss e)’ ["st₁ r₁"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ last_x_assum $ qspecl_then [‘nss’, ‘e’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ CASE_TAC \\ gvs []
    \\ CASE_TAC \\ gvs [])
  >~ [‘BinOp’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘BinOp bop e₀ e₁’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp st env (wrap_Old nss e₀)’ ["st₁ r₁"]
    \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘e₀’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    \\ pop_assum mp_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘e₁’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [])
  >~ [‘ArrLen’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘ArrLen arr’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ gvs [evaluate_exp_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘arr’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [])
  >~ [‘ArrSel’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘ArrSel arr idx’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ gvs [evaluate_exp_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock) \\ strip_tac \\ gvs []
    \\ last_x_assum $ qspecl_then [‘nss’, ‘arr’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (simp [state_component_equality])
    \\ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘idx’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ simp [index_array_with_locals]
    \\ TOP_CASE_TAC \\ gvs [])
  >~ [‘FunCall’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘FunCall name args’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock) \\ strip_tac \\ gvs []
    \\ last_x_assum $ qspecl_then [‘nss’, ‘args’] mp_tac \\ simp [SF ETA_ss]
    \\ disch_then $ drule_all_then assume_tac
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (simp [state_component_equality])
    \\ simp [set_up_call_with_clock_locals]
    \\ TOP_CASE_TAC \\ gvs []
    >- (simp [state_component_equality])
    \\ IF_CASES_TAC \\ gvs []
    >- (simp [restore_caller_def, state_component_equality])
    \\ TOP_CASE_TAC \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    \\ simp [restore_caller_def, state_component_equality])
  >~ [‘Old e’] >-
   (qpat_x_assum ‘_ = wrap_Old _ _’ mp_tac
    \\ simp [Once $ oneline wrap_Old_def]
    \\ simp [AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    >-
     (rename [‘Var n’]
      \\ drule (cj 1 evaluate_exp_with_clock) \\ strip_tac \\ gvs []
      \\ gvs [evaluate_exp_def]
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ gvs [read_local_def, use_old_def, unuse_old_def,
              state_component_equality])
    \\ rename [‘Old e'’]
    \\ qpat_x_assum ‘evaluate_exp _ _ _ = _’ mp_tac
    \\ simp [evaluate_exp_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘e'’] mp_tac \\ simp []
    \\ simp [use_old_def]
    \\ disch_then $ qspec_then ‘st.locals_old’ mp_tac
    \\ impl_tac \\ gvs []
    >- (rpt strip_tac
        \\ last_x_assum drule
        \\ rpt strip_tac
        \\ first_assum $ irule_at (Pos hd)
        \\ gvs [read_local_def, AllCaseEqs()])
    \\ gvs [unuse_old_def, state_component_equality])
  >~ [‘[]’] >-
   (gvs [evaluate_exp_def])
  >~ [‘e::es’] >-
   (rename [‘MAP (wrap_Old _) es₁’]
    \\ qpat_x_assum ‘evaluate_exps _ _ _ = _’ mp_tac
    \\ namedCases_on ‘es₁’ ["", "e' es'"] \\ gvs []
    \\ simp [evaluate_exp_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock) \\ strip_tac \\ gvs []
    \\ last_x_assum $ qspecl_then [‘nss’, ‘e'’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (simp [state_component_equality])
    \\ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ qspecl_then [‘nss’, ‘es'’] mp_tac \\ simp []
    \\ disch_then $ drule_all_then assume_tac
    \\ TOP_CASE_TAC \\ gvs [])
QED

Triviality list_rel_eval_exp_old_var:
  ∀ns vs n st env.
    LIST_REL (eval_exp st env) (MAP (Old ∘ Var) ns) vs ∧ MEM n ns ⇒
    ∃v.
      read_local st.locals_old n = SOME v ∧
      ALOOKUP (ZIP (ns,MAP SOME vs) ++ st.locals) n = SOME (SOME v)
Proof
  Induct \\ gvs [PULL_EXISTS]
  \\ qx_genl_tac [‘n'’, ‘n’, ‘st’, ‘env’, ‘v’, ‘vs’]
  \\ rpt strip_tac \\ gvs []
  >- (gvs [eval_exp_def, evaluate_exp_def, use_old_def, AllCaseEqs()])
  \\ IF_CASES_TAC \\ gvs []
  >- (gvs [eval_exp_def, evaluate_exp_def, use_old_def, AllCaseEqs()])
  \\ last_x_assum drule_all \\ simp []
QED

Theorem eval_exp_wrap_Old_IMP:
  eval_exp st env (wrap_Old (set ns) x) v ∧
  LIST_REL (eval_exp st env) (MAP (Old ∘ Var) ns) vs ∧
  ¬env.is_running ⇒
  eval_exp (st with locals := ZIP (ns,MAP SOME vs) ++ st.locals) env x v
Proof
  simp [eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ drule (cj 1 evaluate_exp_wrap_Old_locals) \\ gvs []
  \\ disch_then $
       qspecl_then [‘set ns’, ‘x’, ‘ZIP (ns, MAP SOME vs) ++ st.locals’] mp_tac
  \\ simp []
  \\ impl_tac >-
   (rpt strip_tac
    >- (drule_all list_rel_eval_exp_old_var \\ simp [])
    \\ simp [ALOOKUP_APPEND]
    \\ simp [AllCaseEqs()]
    \\ disj1_tac
    \\ irule $ iffRL ALOOKUP_ZIP_FAIL \\ simp [])
  \\ disch_then $ irule_at (Pos hd)
QED

Theorem IMP_LIST_REL_eval_exp_MAP_Var:
  st5.locals = ZIP (ret_names,MAP SOME out_vs) ++ rest ∧
  LENGTH ret_names = LENGTH out_vs ∧
  ALL_DISTINCT ret_names ⇒
  LIST_REL (eval_exp st5 env) (MAP Var ret_names) out_vs
Proof
  rw [LIST_REL_EL_EQN] \\ gvs [EL_MAP]
  \\ gvs [eval_exp_def,evaluate_exp_def,read_local_def,AllCaseEqs()]
  \\ simp [state_component_equality]
  \\ simp [ALOOKUP_APPEND,CaseEq "option"] \\ disj2_tac
  \\ ‘ALL_DISTINCT (MAP FST (ZIP (ret_names,MAP SOME out_vs)))’ by
    (imp_res_tac LIST_REL_LENGTH \\ fs [MAP_ZIP])
  \\ drule (GSYM MEM_ALOOKUP)
  \\ simp [] \\ disch_then kall_tac
  \\ simp [MEM_EL,EL_ZIP]
  \\ first_assum $ irule_at $ Pos hd
  \\ simp [MEM_EL,EL_ZIP,EL_MAP]
QED

Theorem freevars_conj:
  ∀xs n. n ∈ freevars (conj xs) ⇔ ∃x. MEM x xs ∧ n ∈ freevars x
Proof
  ho_match_mp_tac conj_ind \\ fs [conj_def,freevars_def,SF DNF_ss]
QED

Triviality read_out_lemma:
  ∀names out_vs n st.
    OPT_MMAP (read_local st.locals) names = SOME out_vs ∧
    MEM n names ∧ ALL_DISTINCT names ⇒
    ∃v. ALOOKUP st.locals n = SOME v ∧
        ALOOKUP (ZIP (names,MAP SOME out_vs)) n = SOME v
Proof
  Induct \\ simp [PULL_EXISTS]
  \\ qx_genl_tac [‘n'’, ‘n’, ‘st’, ‘val’, ‘vals’]
  \\ rpt strip_tac \\ gvs []
  >- (gvs [read_local_def, CaseEq "option"])
  \\ IF_CASES_TAC \\ gvs []
QED

Triviality value_same_type_bool:
  value_same_type v (BoolV b) ⇒ v ∈ all_values BoolT
Proof
  Cases_on ‘v’ \\ gvs [all_values_def]
QED

Triviality value_same_type_int:
  value_same_type v (IntV i) ⇒ v ∈ all_values IntT
Proof
  Cases_on ‘v’ \\ gvs [all_values_def]
QED

(* TODO Move to dafny_eval_rel *)
Triviality eval_exp_eq_value:
  eval_exp st env e v ∧ eval_exp st env e v' ⇒ v' = v
Proof
  gvs [eval_exp_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck’, ‘ck₁’, ‘ck₂’, ‘ck₃’]
  \\ rpt strip_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ rev_dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck’ assume_tac \\ gvs []
QED

Triviality is_some_none:
  IS_SOME x ⇔ x ≠ NONE
Proof
  Cases_on ‘x’ \\ simp []
QED

(* TODO move to eval_rel *)
Theorem eval_stmt_Dec:
  eval_stmt (st with locals := (n, NONE)::st.locals) env stmt st₁ ret ∧
  pop_locals 1 st₁ = SOME st'
  ⇒
  eval_stmt st env (Dec (n,ty) stmt) st' ret
Proof
  simp [eval_stmt_def, PULL_EXISTS]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’]
  \\ rpt strip_tac
  \\ qexistsl [‘ck₁’, ‘ck₂’]
  \\ simp [evaluate_stmt_def]
  \\ simp [declare_local_def]
  \\ gvs [pop_locals_def, AllCaseEqs()]
QED

(* TODO move to eval_rel *)
Theorem eval_stmt_locals:
  eval_stmt st env stmt st' ret ⇒
  MAP FST st'.locals = MAP FST st.locals
Proof
  simp [eval_stmt_def]
  \\ rpt strip_tac
  \\ imp_res_tac evaluate_stmt_locals
  \\ gvs [state_component_equality]
QED

Triviality eval_measure_with_locals_wrap_old:
  eval_measure (st with locals := xs) env (wrap_old r_es) =
  eval_measure st env (wrap_old r_es)
Proof
  namedCases_on ‘r_es’ ["r es"]
  \\ simp [wrap_old_def]
  \\ simp [eval_measure_def, eval_decreases_def]
  \\ irule MAP_CONG \\ simp [MEM_MAP]
  \\ rpt strip_tac \\ gvs []
  \\ simp [evaluate_exp_num_def, evaluate_exp_total_def]
  \\ rpt AP_THM_TAC \\ rpt AP_TERM_TAC
  \\ simp [FUN_EQ_THM] \\ rpt strip_tac
  \\ DEP_REWRITE_TAC [eval_exp_old_eq] \\ simp []
QED

Triviality locals_ok_cons:
  locals_ok xs ys ∧ ¬MEM n (MAP FST xs) ⇒
  locals_ok ((n,ty)::xs) ((n,NONE)::ys)
Proof
  simp [locals_ok_def]
  \\ rpt strip_tac \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum drule \\ gvs []
QED

Triviality map_fst_alookup_some:
  ∀(xs: (α # β) list) (ys: (α # β) list) n v.
    MAP FST xs = MAP FST ys ∧ ALOOKUP ys n = SOME v ⇒
    ∃v'. ALOOKUP xs n = SOME v'
Proof
  Induct \\ gvs []
  \\ qx_genl_tac [‘x’, ‘ys’, ‘n’, ‘v’]
  \\ rpt strip_tac \\ gvs []
  \\ namedCases_on ‘ys’ ["", "y ys'"] \\ gvs []
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum irule \\ simp []
  \\ first_x_assum $ irule_at $ Pos last
  \\ simp []
QED

Triviality locals_ok_cons_drop:
  locals_ok ((n,ty)::xs) ys ∧
  locals_ok xs zs ∧
  ¬MEM n (MAP FST xs) ∧
  MAP FST ys = n::MAP FST zs ⇒
  locals_ok xs (DROP 1 ys)
Proof
  simp [locals_ok_def]
  \\ rpt strip_tac
  \\ rename [‘MEM (n',ty') _’]
  \\ last_x_assum $ qspecl_then [‘n'’, ‘ty'’] mp_tac \\ simp []
  \\ rpt strip_tac
  \\ namedCases_on ‘ys’ ["", "y ys'"] \\ simp []
  \\ Cases_on ‘y’ \\ gvs [AllCaseEqs()]
  \\ drule MEM_MAP_FST \\ gvs []
QED

Triviality conditions_hold_cons_not_free:
  EVERY (λe. n ∉ freevars e) es ∧
  conditions_hold (st with locals := xs) env es ⇒
  conditions_hold (st with locals := (n,v)::xs) env es
Proof
  simp [conditions_hold_def]
  \\ simp [EVERY_MEM]
  \\ rpt strip_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gvs [eval_true_def]
  \\ irule $ iffLR eval_exp_freevars
  \\ first_assum $ irule_at $ Pos last \\ simp []
  \\ rpt strip_tac
  \\ IF_CASES_TAC \\ gvs []
QED

Triviality conditions_hold_cons_drop:
  EVERY (λe. n ∉ freevars e) es ∧
  conditions_hold st env es ∧
  MAP FST st.locals = n::ys ⇒
  conditions_hold (st with locals := DROP 1 st.locals) env es
Proof
  simp [conditions_hold_def]
  \\ simp [EVERY_MEM]
  \\ rpt strip_tac
  \\ namedCases_on ‘st.locals’ ["", "x xs"] \\ gvs []
  \\ namedCases_on ‘x’ ["n v"] \\ gvs []
  \\ last_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gvs [eval_true_def]
  \\ irule $ iffLR eval_exp_freevars
  \\ qexists ‘st.locals’ \\ simp []
  \\ rpt strip_tac
  \\ IF_CASES_TAC \\ gvs []
QED

Triviality ALOOKUP_append_distinct:
  ALL_DISTINCT (MAP FST xs ++ MAP FST ys) ⇒
  ALOOKUP (xs ++ ys) = ALOOKUP (ys ++ xs)
Proof
  simp [FUN_EQ_THM]
  \\ rpt strip_tac
  \\ simp [ALOOKUP_APPEND]
  \\ rpt CASE_TAC \\ gvs []
  \\ gvs [ALL_DISTINCT_APPEND]
  \\ qpat_x_assum ‘ALOOKUP xs _ = _ ’ assume_tac
  \\ imp_res_tac ALOOKUP_MEM_FST \\ gvs []
QED

Triviality MEM_MAP_FST_ALOOKUP:
  MEM n (MAP FST xs) ⇒ ALOOKUP (xs ++ ys) n = ALOOKUP xs n
Proof
  rpt strip_tac
  \\ simp [ALOOKUP_APPEND]
  \\ CASE_TAC \\ gvs []
  \\ gvs [ALOOKUP_NONE]
QED

Triviality ALOOKUP_ZIP_REPLICATE:
  ∀xs cnt n val.
    MEM n xs ∧ LENGTH xs = cnt ⇒
    ALOOKUP (ZIP (xs, REPLICATE cnt val)) n = SOME val
Proof
  Induct \\ gvs []
  \\ rpt strip_tac \\ gvs []
QED

Triviality ALOOKUP_locals_ok_eq:
  ALOOKUP xs = ALOOKUP ys ⇒
  locals_ok ls xs = locals_ok ls ys
Proof
  gvs [locals_ok_def]
QED

Triviality locals_ok_append_right:
  locals_ok ls ys ∧
  (∀n ty. MEM (n, ty) ls ∧ MEM n (MAP FST xs) ⇒
          ∃oval.
            ALOOKUP xs n = SOME oval ∧
            ∀val. oval = SOME val ⇒ val ∈ all_values ty) ⇒
  locals_ok ls (xs ++ ys)
Proof
  simp [locals_ok_def]
  \\ rpt strip_tac
  \\ simp [ALOOKUP_APPEND]
  \\ CASE_TAC \\ gvs []
  \\ drule_then assume_tac ALOOKUP_MEM_FST
  \\ rpt strip_tac \\ gvs []
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
QED

Triviality eval_exp_get_type:
  ∀locals e ty.
    get_type locals e = INR ty ∧
    eval_exp st env e val ∧
    locals_ok locals st.locals ⇒
    val ∈ all_values ty
Proof
  ho_match_mp_tac get_type_ind
  \\ rpt strip_tac
  >~ [‘Var var’] >-
   (gvs [get_type_def, eval_exp_def, evaluate_exp_def, read_local_def,
         locals_ok_def, AllCaseEqs()]
    \\ rev_drule_then assume_tac ALOOKUP_MEM
    \\ last_x_assum drule
    \\ rpt strip_tac \\ gvs [])
  >~ [‘If’] >-
   (gvs [get_type_def, oneline bind_def, eval_exp_def, evaluate_exp_def,
         PULL_EXISTS, AllCaseEqs()]
    \\ imp_res_tac do_cond_some_cases \\ gvs [do_cond_def]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ last_x_assum drule \\ simp [])
  >~ [‘UnOp’] >-
   (gvs [get_type_def, oneline bind_def, eval_exp_def, evaluate_exp_def,
         oneline do_uop_def, all_values_def, PULL_EXISTS, AllCaseEqs()])
  >~ [‘BinOp’] >-
   (gvs [get_type_def, oneline bind_def, eval_exp_def, evaluate_exp_def,
         do_sc_def, do_bop_def, all_values_def, AllCaseEqs()])
  >~ [‘ArrSel’] >-
   (* TODO fix all_values for array *)
   (cheat)
  \\ gvs [get_type_def, oneline bind_def, eval_exp_def, evaluate_exp_def,
          all_values_def, AllCaseEqs()]
QED

Triviality list_rel_eval_exp_get_types:
  ∀exps vs tys.
    LIST_REL (eval_exp st env) exps vs ∧
    get_types locals exps = INR tys ∧
    locals_ok locals st.locals ⇒
    LIST_REL (λv ty. v ∈ all_values ty) vs tys
Proof
  Induct \\ gvs [PULL_EXISTS]
  >- (simp [get_types_def, result_mmap_def])
  \\ rpt strip_tac
  \\ gvs [get_types_def, result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ drule_all eval_exp_get_type \\ simp []
QED

Triviality get_types_var:
  ∀ns tys.
    get_types ls (MAP Var ns) = INR tys ⇒
    LIST_REL (λn ty. MEM (n,ty) ls) ns tys
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ gvs [get_types_def, result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ gvs [get_type_def, CaseEq "option"]
  \\ drule ALOOKUP_MEM \\ simp []
QED

Triviality lookup_ret_name:
  ∀vs lhs_tys ret_names n locals.
    MEM n ret_names ∧
    LIST_REL (λv ty. v ∈ all_values ty) vs lhs_tys ∧
    LIST_REL (λn ty. MEM (n,ty) locals) ret_names lhs_tys ⇒
    ∃val lhs_ty.
      ALOOKUP (ZIP (ret_names,vs)) n = SOME val ∧
      val ∈ all_values lhs_ty ∧ MEM lhs_ty lhs_tys ∧
      MEM (n,lhs_ty) locals
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  >- (first_assum $ irule_at $ Pos hd \\ simp [])
  \\ IF_CASES_TAC \\ gvs []
  >- (first_assum $ irule_at $ Pos hd \\ simp [])
  \\ last_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
  \\ first_assum $ irule_at $ Pos hd \\ simp []
QED

Triviality ALL_DISTINCT_MAP_FST_EQ:
  ∀xs x y y'.
    ALL_DISTINCT (MAP FST xs) ∧ MEM (x,y) xs ∧ MEM (x,y') xs ⇒ y' = y
Proof
  Induct \\ gvs [] \\ Cases
  \\ rpt strip_tac \\ gvs []
  >- (drule MEM_MAP_FST \\ simp [])
  >- (drule MEM_MAP_FST \\ simp [])
  \\ last_x_assum dxrule_all \\ simp []
QED

Triviality locals_unique_types:
  locals_ok locals st_locals ∧ MEM (n,ty) locals ∧ MEM (n,ty') locals ⇒
  ty' = ty
Proof
  simp [locals_ok_def]
  \\ rpt strip_tac
  \\ dxrule_all ALL_DISTINCT_MAP_FST_EQ \\ simp []
QED

Triviality ALOOKUP_ZIP_MAP_SOME:
  ∀ns vs.
    LENGTH ns = LENGTH vs ⇒
    (ALOOKUP (ZIP (ns,MAP SOME vs)) n = SOME (SOME val) ⇔
       ALOOKUP (ZIP (ns,vs)) n = SOME val)
Proof
  Induct \\ gvs []
  \\ gen_tac
  \\ Cases \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
QED

Triviality locals_ok_restore_caller:
  locals_ok locals st.locals ⇒ locals_ok locals (restore_caller st' st).locals
Proof
  simp [locals_ok_def, restore_caller_def]
QED

Triviality eval_exp_var_eq:
  eval_exp st env (Var n) v' ∧ eval_exp st env (Var n) v ⇒ v' = v
Proof
  rpt strip_tac
  \\ gvs [eval_exp_def, evaluate_exp_def, AllCaseEqs()]
QED

Triviality strict_locals_ok_swap_imp:
  (∀n ty. MEM (n,ty) ls ⇒ ALOOKUP xs n = ALOOKUP ys n)
  ⇒
  strict_locals_ok ls xs ⇒ strict_locals_ok ls ys
Proof
  simp [strict_locals_ok_def]
  \\ rpt strip_tac
  \\ last_x_assum drule \\ strip_tac
  \\ last_x_assum drule \\ strip_tac
  \\ gvs []
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Triviality strict_locals_ok_swap:
  (∀n ty. MEM (n,ty) ls ⇒ ALOOKUP xs n = ALOOKUP ys n)
  ⇒
  (strict_locals_ok ls xs ⇔ strict_locals_ok ls ys)
Proof
  metis_tac [strict_locals_ok_swap_imp]
QED

Triviality strict_locals_ok_cons_lr:
  strict_locals_ok ((n,ty)::ls) ((n,SOME v)::rs) ⇒
  v ∈ all_values ty ∧ strict_locals_ok ls rs ∧ ¬MEM n (MAP FST ls)
Proof
  gvs [strict_locals_ok_def]
  \\ rpt strip_tac
  >- (last_x_assum $ qspecl_then [‘n’, ‘ty’] mp_tac \\ simp [])
  \\ rpt strip_tac
  \\ rename [‘MEM (n', ty') _’]
  \\ last_x_assum $ qspecl_then [‘n'’, ‘ty'’] mp_tac \\ simp []
  \\ IF_CASES_TAC \\ gvs []
  \\ drule MEM_MAP_FST \\ simp []
QED

Triviality strict_locals_ok_cons_rl:
  v ∈ all_values ty ∧ strict_locals_ok ls rs ∧ ¬MEM n (MAP FST ls) ⇒
  strict_locals_ok ((n,ty)::ls) ((n,SOME v)::rs)
Proof
  simp [strict_locals_ok_def]
  \\ rpt strip_tac \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ drule MEM_MAP_FST \\ simp []
QED

Triviality strict_locals_ok_cons:
  strict_locals_ok ((n,ty)::ls) ((n,SOME v)::rs) ⇔
    v ∈ all_values ty ∧ strict_locals_ok ls rs ∧ ¬MEM n (MAP FST ls)
Proof
  metis_tac [strict_locals_ok_cons_rl, strict_locals_ok_cons_lr]
QED

Triviality locals_ok_append_left:
  locals_ok (xs ++ ys) zs ⇔
    (locals_ok xs zs ∧ locals_ok ys zs ∧
     (∀e. MEM e (MAP FST xs) ⇒ ¬MEM e (MAP FST ys)))
Proof
  iff_tac
  >- (simp [locals_ok_def, ALL_DISTINCT_APPEND])
  \\ simp [locals_ok_def, ALL_DISTINCT_APPEND]
  \\ rpt strip_tac \\ gvs []
QED

Triviality strict_locals_ok_zip_some:
  ∀ls vs.
    LENGTH vs = LENGTH ls ⇒
    (strict_locals_ok ls (ZIP (MAP FST ls, MAP SOME vs)) ⇔
       ALL_DISTINCT (MAP FST ls) ∧
       LIST_REL (λv ty. v ∈ all_values ty) vs (MAP SND ls))
Proof
  Induct \\ gvs []
  >- (simp [strict_locals_ok_def])
  \\ namedCases ["n ty"]
  \\ namedCases ["", "v vs'"] \\ gvs []
  \\ strip_tac
  \\ last_x_assum drule \\ strip_tac
  \\ simp [strict_locals_ok_cons, AC CONJ_COMM CONJ_ASSOC]
QED

Triviality MEM_MAP_FST_TUPLE:
  MEM x (MAP FST xs) ⇒ ∃y. MEM (x,y) xs
Proof
  simp [MEM_MAP]
  \\ strip_tac \\ rename [‘MEM y _’]
  \\ Cases_on ‘y’ \\ gvs [SF SFY_ss]
QED

Triviality strict_locals_ok_opt_mmap_read_local:
  ∀ys xs st_ls.
    strict_locals_ok xs st_ls ∧ (∀y. MEM y ys ⇒ MEM y (MAP FST xs)) ⇒
    ∃out_vs. OPT_MMAP (read_local st_ls) ys = SOME out_vs
Proof
  Induct \\ gvs []
  \\ qx_genl_tac [‘y’, ‘xs’, ‘st_ls’]
  \\ rpt strip_tac \\ simp [PULL_EXISTS]
  \\ last_x_assum drule \\ simp []
  \\ strip_tac \\ first_x_assum $ irule_at (Pos last)
  \\ gvs [strict_locals_ok_def]
  \\ first_x_assum $ qspec_then ‘y’ mp_tac \\ simp []
  \\ strip_tac
  \\ dxrule MEM_MAP_FST_TUPLE \\ simp [PULL_EXISTS]
  \\ qx_gen_tac ‘ty’ \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ simp [read_local_def]
QED

(* TODO Upstream? *)
Triviality OPT_MMAP_LENGTH:
  ∀xs ys. OPT_MMAP f xs = SOME ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct \\ simp []
  \\ gen_tac \\ Cases \\ simp []
QED

Triviality strict_locals_ok_cons_left:
  strict_locals_ok ((n,ty)::ls) st_ls ⇔
    strict_locals_ok ls st_ls ∧
    ∃v.
      ALOOKUP st_ls n = SOME (SOME v) ∧ v ∈ all_values ty ∧ ¬MEM n (MAP FST ls)
Proof
  iff_tac
  \\ simp [strict_locals_ok_def]
  \\ rpt strip_tac \\ gvs []
QED

Triviality locals_ok_cons_left:
  locals_ok ((n,ty)::ls) st_ls ⇔
    locals_ok ls st_ls ∧ ¬MEM n (MAP FST ls) ∧
    ∃oval.
      ALOOKUP st_ls n = SOME oval ∧
      ∀v. oval = SOME v ⇒ v ∈ all_values ty
Proof
  iff_tac
  \\ simp [locals_ok_def]
  \\ rpt strip_tac \\ gvs []
QED

Triviality strict_locals_ok_opt_mmap_read_local:
  ∀ls st_ls.
    strict_locals_ok ls st_ls ⇒
    ∃vs.
      OPT_MMAP (read_local st_ls) (MAP FST ls) = SOME vs ∧
      LIST_REL (λv ty. v ∈ all_values ty) vs (MAP SND ls)
Proof
  Induct \\ simp [PULL_EXISTS]
  \\ namedCases ["n ty"] \\ rpt strip_tac \\ simp []
  \\ fs [strict_locals_ok_cons_left]
  \\ simp [read_local_def]
QED

Triviality locals_ok_list_rel_all_values:
  ∀ls vals st env.
    locals_ok ls st.locals ∧
    LIST_REL (eval_exp st env) (MAP Var (MAP FST ls)) vals
    ⇒
    LIST_REL (λv ty. v ∈ all_values ty) vals (MAP SND ls)
Proof
  Induct \\ simp [PULL_EXISTS]
  \\ namedCases ["n ty"] \\ simp []
  \\ qx_genl_tac [‘st’, ‘env’, ‘v’, ‘vals’]
  \\ simp [locals_ok_cons_left]
  \\ rpt strip_tac \\ simp []
  >- (gvs [eval_exp_def, evaluate_exp_def, read_local_def, AllCaseEqs()])
  \\ last_assum drule_all \\ simp []
QED

Theorem stmt_wp_sound:
  ∀m reqs stmt post ens decs locals.
    stmt_wp m reqs stmt post ens decs locals ⇒
    ∀st env.
      (∀st' name' mspec' body'.
          ($< LEX SHORTLEX opt_lt)
            (eval_measure st' env (mspec'.rank,mspec'.decreases))
            (eval_measure st env (wrap_old decs)) ∧
          Method name' mspec' body' ∈ m ∧ st'.locals_old = st'.locals ∧
          st'.heap_old = st'.heap ∧ conditions_hold st' env mspec'.reqs ∧
          compatible_env env m ∧
          strict_locals_ok mspec'.ins st'.locals ∧
          locals_ok mspec'.outs st'.locals ∧
          ALL_DISTINCT (MAP FST mspec'.ins ++ MAP FST mspec'.outs) ⇒
          ∃st'' out_vs.
            eval_stmt st' env body' st'' (Rstop Sret) ∧
            conditions_hold st'' env (MAP (wrap_Old (set (MAP FST mspec'.ins))) mspec'.ens) ∧
            st''.locals_old = st'.locals_old ∧
            st''.heap = st'.heap ∧
            st''.heap_old = st'.heap_old ∧
            locals_ok (mspec'.ins ++ mspec'.outs) st''.locals ∧
            LIST_REL (eval_exp st'' env) (MAP (Var o FST) mspec'.outs) out_vs) ∧
      conditions_hold st env reqs ∧ compatible_env env m ∧
      locals_ok locals st.locals ⇒
      ∃st' ret.
        eval_stmt st env stmt st' ret ∧
        st'.locals_old = st.locals_old ∧
        st'.heap = st.heap ∧
        st'.heap_old = st.heap_old ∧
        locals_ok locals st'.locals ∧
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
  >~ [‘Dec (n,ty) stmt’] >-
   (irule_at (Pos hd) eval_stmt_Dec \\ simp []
    \\ qmatch_goalsub_abbrev_tac ‘eval_stmt st_inner’
    \\ last_x_assum $ qspecl_then [‘st_inner’, ‘env’] mp_tac \\ simp []
    \\ impl_tac >-
     (simp [Abbr ‘st_inner’]
      \\ conj_tac >-
       (simp [eval_measure_with_locals_wrap_old, SF SFY_ss]
        \\ rpt strip_tac
        \\ first_x_assum drule_all
        \\ rpt strip_tac \\ gvs []
        \\ rpt $ pop_assum $ irule_at Any)
      \\ drule locals_ok_cons \\ simp [] \\ disch_then kall_tac
      \\ irule conditions_hold_cons_not_free \\ simp [])
    \\ rpt strip_tac
    \\ first_assum $ irule_at $ Pos hd
    \\ drule eval_stmt_locals
    \\ simp [Abbr ‘st_inner’]
    \\ strip_tac
    \\ simp [pop_locals_def, safe_drop_def]
    \\ ‘1 ≤ LENGTH st'.locals’ by
      (qsuff_tac ‘1 ≤ LENGTH (MAP FST st'.locals)’ >- (simp [])
       \\ asm_rewrite_tac [] \\ simp [])
    \\ simp []
    \\ drule_all locals_ok_cons_drop \\ simp [] \\ disch_then kall_tac
    \\ rpt CASE_TAC
    \\ gvs [conditions_hold_cons_drop])
  >~ [‘Assign ass’] >-
   (irule_at (Pos hd) eval_stmt_Assign \\ simp []
    \\ qpat_x_assum ‘∀x._’ kall_tac
    \\ fs [conditions_hold_def]
    \\ drule eval_true_Let_IMP \\ simp []
    \\ strip_tac
    \\ irule_at Any IMP_eval_rhs_exps_MAP_ExpRhs
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [GSYM MAP_MAP_o]
    \\ drule_then mp_tac locals_ok_is_some_alookup
    \\ strip_tac
    \\ dxrule_all subset_every \\ strip_tac
    \\ drule IMP_assi_values
    \\ disch_then $ qspecl_then [‘env’, ‘vs’] mp_tac
    \\ imp_res_tac LIST_REL_LENGTH
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd
    \\ simp [eval_true_def,GSYM eval_true_conj_every]
    \\ conj_tac >-
     (pop_assum mp_tac
      \\ DEP_REWRITE_TAC [alookup_distinct_reverse_append] \\ simp [MAP_ZIP]
      \\ disch_tac
      \\ drule ALOOKUP_locals_ok_eq \\ simp [] \\ disch_then kall_tac
      \\ irule locals_ok_append_right \\ simp [MAP_ZIP]
      \\ qx_genl_tac [‘n’, ‘ty’]
      \\ strip_tac \\ gvs []
      \\ qrefine ‘SOME val’
      \\ simp [ALOOKUP_ZIP_MAP_SOME]
      \\ drule_all_then assume_tac list_rel_eval_exp_get_types
      \\ drule_all_then assume_tac get_types_var
      \\ drule_all lookup_ret_name
      \\ disch_then $ qx_choosel_then [‘val’, ‘lhs_ty’] mp_tac
      \\ strip_tac \\ gvs []
      \\ drule locals_unique_types
      \\ disch_then $ qspecl_then [‘ty’, ‘lhs_ty’, ‘n’] mp_tac \\ simp [])
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
  >~ [‘While guard invs ds mods body’] >-

   (qsuff_tac
    ‘∀st.
       conditions_hold st env (invs ++ MAP CanEval ds) ⇒
       ∃st' ret.
         eval_stmt st env (While guard invs ds mods body) st' ret ∧
         st'.locals_old = st.locals_old ∧ st'.heap = st.heap ∧
         st'.heap_old = st.heap_old ∧
         locals_ok locals st'.locals ∧
         case ret of
         | Rcont => conditions_hold st' env (not guard::invs)
         | Rstop Sret => conditions_hold st' env ens
         | Rstop (Serr v3) => F’
    >-
     (disch_then $ qspec_then ‘st’ mp_tac
      \\ impl_tac >- gvs [conditions_hold_def]
      \\ strip_tac
      \\ first_assum $ irule_at $ Pos hd \\ asm_rewrite_tac []
      \\ Cases_on ‘ret’ \\ gvs []
      \\ gvs [conditions_hold_def]
      \\ gvs [GSYM conditions_hold_def]

      \\ cheat)

    \\ cheat)
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
     (simp [])
    >-
     (unabbrev_all_tac
      \\ simp [locals_ok_def]
      \\ reverse $ conj_tac
      >- (gvs [ALL_DISTINCT_APPEND])
      \\ rpt strip_tac
      \\ DEP_ONCE_REWRITE_TAC [alookup_distinct_reverse] \\ simp [MAP_ZIP]
      \\ DEP_ONCE_REWRITE_TAC [ALOOKUP_append_distinct] \\ simp [MAP_ZIP]
      \\ drule MEM_MAP_FST \\ strip_tac
      \\ DEP_ONCE_REWRITE_TAC [MEM_MAP_FST_ALOOKUP] \\ simp [MAP_ZIP]
      \\ DEP_ONCE_REWRITE_TAC [ALOOKUP_ZIP_REPLICATE] \\ simp [])
    >-
     (simp [Abbr‘st1’]
      \\ ‘∀n ty. MEM (n,ty) mspec.ins ⇒
                 ALOOKUP new_l n =
                 ALOOKUP (ZIP (MAP FST mspec.ins,MAP SOME in_vs)) n’ by
        (rpt strip_tac
         \\ simp [Abbr ‘new_l’]
         \\ DEP_ONCE_REWRITE_TAC [alookup_distinct_reverse] \\ simp [MAP_ZIP]
         \\ simp [ALOOKUP_APPEND]
         \\ CASE_TAC
         \\ simp [ALOOKUP_NONE] \\ simp [MAP_ZIP]
         \\ drule MEM_MAP_FST
         \\ gvs [ALL_DISTINCT_APPEND])
      \\ drule strict_locals_ok_swap \\ simp [] \\ disch_then kall_tac
      \\ simp [strict_locals_ok_zip_some]
      \\ conj_tac
      >- (full_simp_tac std_ss [ALL_DISTINCT_APPEND])
      \\ drule_all list_rel_eval_exp_get_types \\ simp [])
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
  \\ disch_tac
  \\ first_assum $ irule_at (Pos hd)
  \\ drule_then assume_tac OPT_MMAP_LENGTH \\ simp []
  \\ gvs [GSYM conditions_hold_def]
  \\ rename [‘restore_caller st2 st’]
  \\ qabbrev_tac ‘st3 = restore_caller st2 st’
  \\ ‘locals_ok (mspec.outs) st2.locals’ by (fs [locals_ok_append_left])
  \\ drule_all locals_ok_list_rel_all_values \\ strip_tac
  \\ drule eval_true_Foralls_distinct
  \\ simp [MAP_ZIP] \\ strip_tac
  \\ gvs [conditions_hold_def]
  \\ ‘EVERY (λn. IS_SOME (ALOOKUP st3.locals n)) ret_names’ by
    (unabbrev_all_tac
     \\ gvs [restore_caller_def]
     \\ rev_drule locals_ok_is_some_alookup
     \\ strip_tac
     \\ drule_all subset_every \\ simp [])
  \\ drule IMP_assi_values_distinct
  \\ disch_then $ qspecl_then [‘env’, ‘out_vs’] mp_tac
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ conj_tac >- (unabbrev_all_tac \\ fs [restore_caller_def])
  \\ conj_tac >- (unabbrev_all_tac \\ fs [restore_caller_def])
  \\ conj_tac >- (unabbrev_all_tac \\ fs [restore_caller_def])
  \\ conj_tac >-
   (gvs []
    \\ drule ALOOKUP_locals_ok_eq \\ simp [] \\ disch_then kall_tac
    \\ irule locals_ok_append_right \\ simp [MAP_ZIP]
    \\ simp [Abbr ‘st3’]
    \\ irule_at (Pos last) locals_ok_restore_caller \\ simp []
    \\ qx_genl_tac [‘n’, ‘ty’]
    \\ strip_tac \\ gvs []
    \\ qrefine ‘SOME val’
    \\ simp [ALOOKUP_ZIP_MAP_SOME]
    \\ drule_all_then assume_tac list_rel_eval_exp_get_types
    \\ drule_all_then assume_tac get_types_var
    \\ drule_all lookup_ret_name
    \\ disch_then $ qx_choosel_then [‘val’, ‘lhs_ty’] mp_tac
    \\ strip_tac \\ gvs []
    \\ rev_drule locals_unique_types
    \\ disch_then $ qspecl_then [‘ty’, ‘lhs_ty’, ‘n’] mp_tac \\ simp [])
  \\ rewrite_tac [GSYM eval_true_conj_every]
  \\ rewrite_tac [eval_true_def]
  \\ irule (iffLR eval_exp_swap_locals_alt)
  \\ pop_assum $ irule_at Any o GSYM
  \\ first_x_assum $ qspec_then ‘ZIP (ret_names,MAP SOME out_vs)’ mp_tac
  \\ impl_tac >- (gvs [LIST_REL_EL_EQN,EL_ZIP,EL_MAP])
  \\ strip_tac
  \\ dxrule eval_true_imp
  \\ ‘st3.locals = st.locals’ by fs [Abbr‘st3’,restore_caller_def]
  \\ strip_tac
  \\ irule eval_exp_swap_state
  \\ simp [GSYM eval_true_def]
  \\ pop_assum $ irule_at Any
  \\ reverse conj_tac
  >- simp [state_component_equality,Abbr‘st3’,Abbr‘st1’,restore_caller_def]
  \\ fs [GSYM eval_true_def,GSYM eval_true_conj_every]
  \\ qmatch_goalsub_abbrev_tac ‘eval_true st5’
  \\ ‘LIST_REL (eval_exp st5 env)
        (args ++ MAP Var ret_names) (in_vs ++ out_vs)’ by
   (irule listTheory.LIST_REL_APPEND_suff
    \\ reverse conj_tac
    >- (irule IMP_LIST_REL_eval_exp_MAP_Var \\ simp [Abbr‘st5’])
    \\ qpat_x_assum ‘LIST_REL (eval_exp st env) args in_vs’ mp_tac
    \\ qpat_x_assum ‘EVERY _ args’ mp_tac
    \\ simp [LIST_REL_EL_EQN,EVERY_EL]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ first_x_assum drule
    \\ strip_tac \\ simp [Abbr‘st5’]
    \\ match_mp_tac EQ_IMPLIES
    \\ irule EQ_TRANS
    \\ irule_at (Pos last) eval_exp_freevars
    \\ qexists_tac ‘st.locals’ \\ fs []
    \\ rpt strip_tac
    \\ simp [ALOOKUP_APPEND,CaseEq"option"]
    \\ disj1_tac
    \\ simp [ALOOKUP_NONE]
    \\ simp [MAP_ZIP] \\ fs [IN_DISJOINT]
    \\ metis_tac [])
  \\ drule eval_exp_Let
  \\ rewrite_tac [eval_true_def]
  \\ disch_then $ DEP_REWRITE_TAC o single
  \\ conj_tac >- fs []
  \\ simp [Abbr‘st5’]
  \\ fs [conj_MAP_wrap_Old]
  \\ qpat_x_assum ‘eval_true st2 env (wrap_Old _ _)’ assume_tac
  \\ fs [eval_true_def]
  \\ drule eval_exp_wrap_Old_IMP
  \\ disch_then $ qspec_then ‘in_vs’ mp_tac
  \\ impl_tac
  >-
   (conj_tac
    \\ simp [Once listTheory.LIST_REL_MAP1]
    \\ simp [LIST_REL_EL_EQN,eval_exp_def,evaluate_exp_def,
             use_old_def,AllCaseEqs()]
    \\ simp [AllCaseEqs(),unuse_old_def,read_local_def,
             state_component_equality]
    \\ fs [Abbr‘st1’,Abbr‘new_l’] \\ rpt gen_tac
    \\ DEP_REWRITE_TAC [alookup_distinct_reverse] \\ fs [MAP_ZIP]
    \\ fs [ALOOKUP_APPEND,CaseEq"option"]
    \\ strip_tac \\ disj2_tac
    \\ DEP_REWRITE_TAC [GSYM MEM_ALOOKUP]
    \\ fs [MAP_ZIP,MEM_ZIP,ALL_DISTINCT_APPEND]
    \\ first_assum $ irule_at $ Pos hd \\ fs [EL_MAP])
  \\ qmatch_goalsub_abbrev_tac ‘eval_exp (_ with locals := l1) _ _ _ ⇒ _’
  \\ qmatch_goalsub_abbrev_tac ‘_ ⇒ eval_exp (_ with locals := l2) _ _ _’
  \\ strip_tac
  \\ irule eval_exp_no_old_IMP
  \\ conj_tac
  >- (fs [no_Old_conj,EVERY_MEM] \\ rw [] \\ res_tac \\ fs [])
  \\ qexists_tac ‘st2.heap_old’
  \\ qexists_tac ‘st2.locals_old’
  \\ irule eval_exp_swap_state
  \\ qexists_tac ‘st2 with locals := l2’
  \\ conj_tac
  >- gvs [state_component_equality,Abbr‘st1’]
  \\ pop_assum mp_tac
  \\ match_mp_tac EQ_IMPLIES
  \\ irule_at (Pos hd) eval_exp_freevars
  \\ simp [freevars_conj]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘EVERY _ mspec.ens’ mp_tac
  \\ simp [EVERY_MEM]
  \\ disch_then drule
  \\ simp [SUBSET_DEF]
  \\ strip_tac
  \\ fs [Abbr‘l1’,Abbr‘l2’]
  \\ simp [ALOOKUP_APPEND]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
  \\ DEP_REWRITE_TAC [GSYM rich_listTheory.ZIP_APPEND] \\ fs []
  \\ simp [ALOOKUP_APPEND]
  \\ simp [MAP_ZIP |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL]
  \\ CASE_TAC \\ fs []
  \\ pop_assum mp_tac
  \\ simp [ALOOKUP_NONE,MAP_ZIP] \\ strip_tac
  \\ first_x_assum drule \\ simp []
  \\ strip_tac
  \\ fs [ALL_DISTINCT_APPEND]
  \\ drule_all read_out_lemma
  \\ strip_tac \\ fs []
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

Triviality caneval_dfy_eq_lhs_imp:
  eval_true st env (CanEval (dfy_eq (Var n) e)) ⇒
  eval_true st env (CanEval (Var n))
Proof
  simp [eval_true_def, eval_exp_def, CanEval_def]
  \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, do_sc_def, do_bop_def, AllCaseEqs()]
  \\ simp [state_component_equality]
QED

Theorem methods_lemma[local]:
  ∀m.
    proved_methods m ⇒
    ∀x st name mspec body env.
      x = eval_measure st env (mspec.rank, mspec.decreases) ∧
      Method name mspec body ∈ m ∧
      st.locals_old = st.locals ∧
      st.heap_old = st.heap ∧
      conditions_hold st env mspec.reqs ∧ compatible_env env m ∧
      strict_locals_ok mspec.ins st.locals ∧
      locals_ok mspec.outs st.locals ∧
      (* TODO ∀e. MEM e (MAP FST mspec.ins) ⇒ ¬MEM e (MAP FST mspec.outs)
           should be enough *)
      ALL_DISTINCT (MAP FST mspec.ins ++ MAP FST mspec.outs) ⇒
      ∃st' out_vs.
        eval_stmt st env body st' (Rstop Sret) ∧
        st'.locals_old = st.locals_old ∧
        st'.heap = st.heap ∧
        st'.heap_old = st.heap_old ∧
        locals_ok (mspec.ins ++ mspec.outs) st'.locals ∧
        conditions_hold st' env (MAP (wrap_Old (set (MAP FST mspec.ins))) mspec.ens) ∧
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
    \\ ‘ALL_DISTINCT (MAP FST mspec.ins)’ by (gvs [ALL_DISTINCT_APPEND])
    \\ drule_all forall_imp_conditions_hold
    \\ strip_tac \\ gvs []
    \\ imp_res_tac strict_locals_ok_IMP_locals_ok
    \\ simp [locals_ok_append_left]
    \\ reverse conj_tac >- (fs [ALL_DISTINCT_APPEND])
    \\ rpt strip_tac
    \\ gvs [eval_measure_wrap_old, compatible_env_def]
    \\ last_x_assum $ drule_then drule
    \\ impl_tac >- (simp [SF SFY_ss])
    \\ strip_tac \\ gvs [locals_ok_append_left]
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ gvs [False_thm]
  \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ rpt $ first_assum $ irule_at Any
  \\ fs [conditions_hold_def]
  \\ fs [GSYM MAP_MAP_o]
  \\ drule EVERY_eval_true_CanEval \\ simp []
QED

Theorem methods_correct = SRULE [] methods_lemma;

(*************)

Definition dest_VarLhs_def:
  dest_VarLhs (VarLhs var) = return var ∧
  dest_VarLhs _ = fail «dest_VarLhs: Not VarLhs»
End

Triviality result_mmap_dest_VarLhs:
  ∀lhss vars. result_mmap dest_VarLhs lhss = INR vars ⇒ lhss = MAP VarLhs vars
Proof
  Induct \\ simp [result_mmap_def, oneline bind_def]
  \\ Cases \\ simp [dest_VarLhs_def]
  \\ Cases \\ simp [CaseEq "sum"]
QED

Definition dest_ExpRhs_def:
  dest_ExpRhs (ExpRhs e) = return e ∧
  dest_ExpRhs _ = fail «dest_ExpRhs: Not ExpRhs»
End

Triviality result_mmap_dest_ExpRhs:
  ∀lhss vars. result_mmap dest_ExpRhs lhss = INR vars ⇒ lhss = MAP ExpRhs vars
Proof
  Induct \\ simp [result_mmap_def, oneline bind_def]
  \\ Cases \\ simp [dest_ExpRhs_def]
  \\ Cases \\ simp [CaseEq "sum"]
QED

Definition find_met_def:
  find_met name [] = fail «find_met: Could not find method» ∧
  find_met name (Method name' spec body::rest) =
    if name' = name
    then return (Method name' spec body)
    else find_met name rest
End

Triviality find_met_inr:
  ∀methods name method.
    find_met name methods = INR method ⇒
    ∃spec body. method = Method name spec body ∧ MEM method methods
Proof
  Induct \\ simp [find_met_def]
  \\ Cases \\ simp [find_met_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp []
  \\ strip_tac \\ gvs []
  \\ last_x_assum drule
  \\ rpt strip_tac \\ simp []
QED

Definition dest_met_def[simp]:
  dest_met (Method name spec body) = (name, spec, body)
End

Definition freevars_list_def:
  (freevars_list (Let binds body) ⇔
     (FLAT (MAP freevars_list (MAP SND binds)))
      ++ (FILTER (λx. ¬MEM x (MAP FST binds)) (freevars_list body))) ∧
  (freevars_list (Var n) ⇔ [n]) ∧
  (freevars_list (Lit _) ⇔ []) ∧
  (freevars_list (If grd thn els) ⇔
     freevars_list grd ++ freevars_list thn ++ freevars_list els) ∧
  (freevars_list (UnOp _ e) ⇔ freevars_list e) ∧
  (freevars_list (BinOp _ e₀ e₁) ⇔
     (freevars_list e₀) ++ (freevars_list e₁)) ∧
  (freevars_list (ArrLen arr) ⇔ freevars_list arr) ∧
  (freevars_list (ArrSel arr idx) ⇔
     freevars_list arr ++ freevars_list idx) ∧
  (freevars_list (FunCall _ args) ⇔
     FLAT (MAP freevars_list args)) ∧
  (freevars_list (Forall (vn,_) e) ⇔
     (FILTER (λx. x ≠ vn) (freevars_list e))) ∧
  (freevars_list (Old e) ⇔ freevars_list e) ∧
  (freevars_list (ForallHeap mods e) ⇔
     FLAT (MAP freevars_list mods) ++ freevars_list e)
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_exp_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Triviality mem_freevars_list_eq:
  (∀e. MEM e xs ⇒ set (freevars_list e) = freevars e) ⇒
  MAP set (MAP (λe. freevars_list e) xs) = MAP (λe. freevars e) xs
Proof
  rpt strip_tac
  \\ simp [MAP_MAP_o, o_DEF]
  \\ irule MAP_CONG \\ gvs []
QED

Theorem freevars_list_eq:
  ∀e. set (freevars_list e) = freevars e
Proof
  ho_match_mp_tac freevars_list_ind
  \\ rpt strip_tac
  \\ simp [freevars_list_def, freevars_def]
  \\ simp [LIST_TO_SET_FLAT]
  \\ simp [LIST_TO_SET_FILTER]
  \\ simp [mem_freevars_list_eq]
  \\ SET_TAC []
QED

(* TODO Move? *)
Definition list_disjoint_def:
  list_disjoint xs ys ⇔
    list_inter xs ys = []
End

(* TODO Move? *)
Triviality LIST_TO_SET_DISJOINT:
  list_disjoint xs ys = DISJOINT (set xs) (set ys)
Proof
  simp [list_disjoint_def, list_inter_def, FILTER_EQ_NIL, EVERY_MEM]
  \\ SET_TAC []
QED

(* TODO Move? *)
Definition list_subset_def:
  list_subset xs ys ⇔
    EVERY (λx. MEM x ys) xs
End

(* TODO Move? *)
Triviality LIST_TO_SET_SUBSET:
  list_subset xs ys ⇔ (set xs) ⊆ (set ys)
Proof
  simp [list_subset_def, EVERY_MEM]
  \\ SET_TAC []
QED

Definition stmt_vcg_def:
  stmt_vcg _ Skip post _ _ _ = return post ∧
  stmt_vcg _ (Assert e) post _ _ _ = return (e::post) ∧
  stmt_vcg _ (Return) _ ens _ _ = return ens ∧
  stmt_vcg m (Then s₁ s₂) post ens decs ls =
    do
      pre' <- stmt_vcg m s₂ post ens decs ls;
      stmt_vcg m s₁ pre' ens decs ls;
    od ∧
  stmt_vcg m (If grd thn els) post ens decs ls =
  do
    pre_thn <- stmt_vcg m thn post ens decs ls;
    pre_els <- stmt_vcg m els post ens decs ls;
    return [IsBool grd; imp grd (conj pre_thn); imp (not grd) (conj pre_els)]
  od ∧
  stmt_vcg m (Dec (n,ty) stmt) post ens decs ls =
  do
    wp <- stmt_vcg m stmt post ens decs ((n,ty)::ls);
    () <- if EVERY (λe. ¬MEM n (freevars_list e)) wp then return () else
            (fail «stmt_vcg:Dec: Name occurs freely in wp»);
    () <- if EVERY (λe. ¬MEM n (freevars_list e)) post then return () else
            (fail «stmt_vcg:Dec: Name occurs freely in post»);
    () <- if EVERY (λe. ¬MEM n (freevars_list e)) ens then return () else
            (fail «stmt_vcg:Dec: Name occurs freely in ens»);
    () <- if ¬MEM n (MAP FST ls) then return () else
            (fail «stmt_vcg:Dec: Shadowing variables disallowed»);
    return wp
  od ∧
  stmt_vcg _ (Assign ass) post _ _ ls =
  do
    (lhss, rhss) <<- UNZIP ass;
    vars <- result_mmap dest_VarLhs lhss;
    es <- result_mmap dest_ExpRhs rhss;
    () <- if ALL_DISTINCT vars then return () else
            (fail «stmt_vcg:Assign: variables not distinct»);
    () <- if list_subset vars (MAP FST ls) then return () else
            (fail «stmt_vcg:Assign: Trying to assign to undeclared variables»);
    es_tys <- get_types ls es;
    vars_tys <- get_types ls (MAP Var vars);
    () <- if es_tys = vars_tys then return () else
            (fail «stmt_vcg:Assign: lhs and rhs types do not match»);
    return [Let (ZIP (vars, es)) (conj post)]
  od ∧
  stmt_vcg m (MetCall lhss name args) post ens decs ls =
  do
    method <- find_met name m;
    (name, spec, body) <<- dest_met method;
    () <- if LENGTH spec.ins = LENGTH args then return () else
            (fail «stmt_vcg:MetCall: Bad number of arguments»);
    () <- if LENGTH spec.outs = LENGTH lhss then return () else
            (fail «stmt_vcg:MetCall: Bad number of left-hand sides»);
    () <- if ALL_DISTINCT (MAP FST spec.ins ++ MAP FST spec.outs)
          then return ()
          else (fail «stmt_vcg:MetCall: Method ins and outs not distinct»);
    vars <- result_mmap dest_VarLhs lhss;
    () <- if ALL_DISTINCT vars then return () else
            (fail «stmt_vcg:MetCall: left-hand side names not distinct»);
    () <- if EVERY (λe. list_disjoint (freevars_list e) vars) args
          then return ()
          else (fail «stmt_vcg:MetCall: Cannot read and assign a variable in one statement»);
    () <- if EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins) ∧
                        no_Old e) spec.reqs
          then return ()
          else (fail «stmt_vcg:MetCall: Bad requires spec»);
    () <- if EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins) ∧
                        no_Old e) spec.decreases
          then return ()
          else (fail «stmt_vcg:MetCall: Bad decreases spec»);
    () <- if EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins
                                                   ++ MAP FST spec.outs) ∧
                        no_Old e) spec.ens
          then return ()
          else (fail «stmt_vcg:MetCall: Bad ensures spec»);
    () <- if list_subset vars (MAP FST ls) then return () else
            (fail «stmt_vcg:MetCall: Trying to assign to undeclared variables»);
    arg_tys <- get_types ls args;
    () <- if arg_tys = MAP SND spec.ins then return () else
            (fail «stmt_vcg:MetCall: Argument and parameters types do not match»);
    var_tys <- get_types ls (MAP Var vars);
    () <- if var_tys = MAP SND spec.outs then return () else
            (fail «stmt_vcg:MetCall: lhs variable types do not match»);
    return
      (Let (ZIP (MAP FST spec.ins,args)) (conj spec.reqs)
       :: MAP CanEval args
       ++ decreases_check
          (spec.rank,
           MAP (Let (ZIP (MAP FST spec.ins,args))) spec.decreases)
          (wrap_old decs)
       ++ [Foralls (ZIP (vars, MAP SND spec.outs))
                   (imp (Let (ZIP(MAP FST spec.ins ++ MAP FST spec.outs,
                                  args             ++ MAP Var vars))
                             (conj spec.ens))
                        (conj post))])
  od ∧
  stmt_vcg _ _ _ _ _ _ = fail «stmt_vcg: Unsupported statement»
End

Theorem stmt_vcg_correct:
  ∀m stmt post ens decs ls res.
    stmt_vcg m stmt (post:exp list) (ens:exp list) decs ls = INR res
(*
                                                       ... = INR (loop_vcs,res) ∧
    EVERY require loop_vcs
    ⇒
    stmt_wp (set m) res stmt (post:exp list) (ens:exp list) decs ls
*)
    ⇒
    stmt_wp (set m) res stmt (post:exp list) (ens:exp list) decs ls
Proof
  ho_match_mp_tac stmt_vcg_ind
  \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [stmt_vcg_def, stmt_wp_Skip])
  >~ [‘Assert’] >-
   (gvs [stmt_vcg_def, stmt_wp_Assert])
  >~ [‘Return’] >-
   (gvs [stmt_vcg_def, stmt_wp_Return])
  >~ [‘Then’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_Then
    \\ last_x_assum $ irule_at (Pos last)
    \\ last_x_assum irule \\ simp [])
  >~ [‘If’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_If \\ simp [])
  >~ [‘Dec’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_Dec
    \\ gvs [IN_DEF, freevars_list_eq])
  >~ [‘Assign’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [UNZIP_MAP]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_Assign
    \\ imp_res_tac result_mmap_len \\ simp []
    \\ drule_then assume_tac result_mmap_dest_VarLhs \\ simp []
    \\ drule_then assume_tac result_mmap_dest_ExpRhs \\ simp []
    \\ gvs [LIST_TO_SET_SUBSET])
  >~ [‘MetCall’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ drule find_met_inr \\ rpt strip_tac \\ gvs []
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ drule_then assume_tac result_mmap_dest_VarLhs \\ simp []
    \\ irule $ SRULE [rich_listTheory.APPEND] stmt_wp_MetCall
    \\ simp []
    \\ gvs [LIST_TO_SET_SUBSET, LIST_TO_SET_DISJOINT, freevars_list_eq]
    \\ last_assum $ irule_at (Pos hd))
  \\ gvs [stmt_vcg_def]
QED

Definition wrap_Old_list_def:
  wrap_Old_list vs (Var v) =
    (if MEM v vs then Old (Var v) else Var v) ∧
  wrap_Old_list _ (Lit l) = Lit l ∧
  wrap_Old_list vs (If grd thn els) =
    If (wrap_Old_list vs grd) (wrap_Old_list vs thn) (wrap_Old_list vs els) ∧
  wrap_Old_list vs (UnOp uop e) =
    UnOp uop (wrap_Old_list vs e) ∧
  wrap_Old_list vs (BinOp bop e₀ e₁) =
    BinOp bop (wrap_Old_list vs e₀) (wrap_Old_list vs e₁) ∧
  wrap_Old_list vs (ArrLen arr) =
    ArrLen (wrap_Old_list vs arr) ∧
  wrap_Old_list vs (ArrSel arr idx) =
    ArrSel (wrap_Old_list vs arr) (wrap_Old_list vs idx) ∧
  wrap_Old_list vs (FunCall name args) =
    FunCall name (MAP (wrap_Old_list vs) args) ∧
  wrap_Old_list vs (Forall (vn,vt) term) =
    Forall (vn,vt) (wrap_Old_list (FILTER (λx. x ≠ vn) vs) term) ∧
  wrap_Old_list vs (Old e) =
    Old (wrap_Old_list vs e) ∧
  wrap_Old_list vs (Let binds body) =
    Let (MAP (λ(n,e). (n, wrap_Old_list vs e)) binds)
        ((wrap_Old_list (FILTER (λx. ¬MEM x (MAP FST binds)) vs)) body) ∧
  wrap_Old_list vs (ForallHeap mods term) =
    ForallHeap (MAP (wrap_Old_list vs) mods) (wrap_Old_list vs term)
End

Triviality mem_wrap_Old_list_eq:
  (∀e. MEM e args ⇒ wrap_Old_list vs e = wrap_Old (set vs) e) ⇒
  MAP (λa. wrap_Old_list vs a) args = MAP (λa. wrap_Old (set vs) a) args
Proof
  rpt strip_tac
  \\ simp [MAP_MAP_o, o_DEF]
  \\ irule MAP_CONG \\ gvs []
QED

Triviality wrap_Old_list_eq_aux:
  ∀vs e. wrap_Old_list vs e = wrap_Old (set vs) e
Proof
  ho_match_mp_tac wrap_Old_list_ind
  \\ rpt strip_tac
  >~ [‘Forall’] >-
   (simp [wrap_Old_list_def, wrap_Old_def]
    \\ simp [LIST_TO_SET_FILTER]
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ SET_TAC [])
  >~ [‘Let’] >-
   (simp [wrap_Old_list_def, wrap_Old_def]
    \\ simp [LIST_TO_SET_FILTER]
    \\ conj_tac
    >- (irule MAP_CONG \\ simp []
        \\ qx_gen_tac ‘x’
        \\ PairCases_on ‘x’ \\ simp []
        \\ strip_tac \\ last_assum drule \\ simp [])
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ SET_TAC [])
  \\ simp [wrap_Old_list_def, wrap_Old_def]
  \\ simp [mem_wrap_Old_list_eq]
  \\ simp [LIST_TO_SET_FILTER]
QED

Theorem wrap_Old_list_eq:
  ∀vs. wrap_Old_list vs = wrap_Old (set vs)
Proof
  simp [FUN_EQ_THM, wrap_Old_list_eq_aux]
QED

Definition met_vcg_def:
  met_vcg mets (Method name specs body) =
  do
    (* ensures should always refer to the locals as they were at the beginning
       of a method; in particular, it should ignore any updates/shadowing *)
    ens <<- (MAP (wrap_Old_list (MAP FST specs.ins)) specs.ens ++
             MAP (CanEval ∘ Var ∘ FST) specs.outs);
    vcs <- stmt_vcg mets body [False] ens (specs.rank, specs.decreases)
                    (specs.ins ++ specs.outs);
    p <<- (Foralls specs.ins $ imp (conj specs.reqs) (conj vcs));
    if freevars_list p = [] then
      return p
    else
      fail «met_vcg: condition has freevars»
  od
End

Definition mets_vcg_def:
  mets_vcg mets = result_mmap (met_vcg mets) mets
End

(* TODO move to result_monad? *)
Theorem mem_result_mmap_inr:
  ∀xs x f ys.
    MEM x xs ∧ result_mmap f xs = INR ys ⇒ ∃y. f x = INR y ∧ MEM y ys
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ last_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
QED

Theorem mets_vcg_correct:
  ∀mets vcs.
    mets_vcg mets = INR vcs ∧ (EVERY valid vcs) ⇒
    proved_methods (set mets)
Proof
  rpt strip_tac
  \\ gvs [mets_vcg_def, proved_methods_def]
  \\ rpt strip_tac
  \\ drule_all mem_result_mmap_inr
  \\ strip_tac
  \\ gvs [met_vcg_def, oneline bind_def, CaseEq "sum"]
  \\ drule stmt_vcg_correct \\ gvs []
  \\ simp [wrap_Old_list_eq]
  \\ disch_then $ irule_at (Pos hd)
  \\ gvs [EVERY_MEM]
  \\ simp [GSYM freevars_list_eq]
QED

(* TODO Perhaps we should use this in the semantics? *)
Definition get_method_def:
  get_method name members =
  case get_member_aux name members of
  | NONE => fail «get_method: Method not found»
  | SOME member =>
    (case member of
     | Function _ _ _ _ _ _ _ => fail «get_method: Found function instead»
     | Method _ _ _ _ _ _ _ _ _ => return member)
End

Definition met_calls_def:
  met_calls members (MetCall _ name _) =
  do
    member <- get_method name members;
    return [member]
  od ∧
  met_calls members (Then s₁ s₂) =
  do
    mcs₁ <- met_calls members s₁;
    mcs₂ <- met_calls members s₂;
    return (mcs₁ ++ mcs₂)
  od ∧
  met_calls members (If _ thn els) =
  do
    mcs₁ <- met_calls members thn;
    mcs₂ <- met_calls members els;
    return (mcs₁ ++ mcs₂)
  od ∧
  met_calls members (Dec _ stmt) = met_calls members stmt ∧
  met_calls members (While _ _ _ _ body) = met_calls members body ∧
  met_calls members Skip = return [] ∧
  met_calls members (Assert _) = return [] ∧
  met_calls members (Assign _) = return [] ∧
  met_calls members (Print _ _) = return [] ∧
  met_calls members Return = return []
End

Definition dependencies_def:
  dependencies members member =
  case member of
  | (Method _ _ _ _ _ _ _ _ body) =>
      do
        deps <- met_calls members body;
        return (member, deps)
      od
  | _ => fail «dependencies: Functions unsupported»
End

Definition top_sorted_deps_def:
  top_sorted_deps members =
  do
    deps <- result_mmap (dependencies members) members;
    return $ top_sort_any deps
  od
End

Definition to_met_def:
  to_met rank (Method name ins reqs ens reads decreases outs mods body) =
  return (Method name
                 <| ins := ins;
                    reqs := reqs;
                    ens := ens;
                    reads := reads;
                    decreases := decreases;
                    outs := outs;
                    mods := mods;
                    rank := rank |>
                 body) ∧
  to_met _ _ = fail «to_met: Not a method»
End

Definition to_mets_aux_def:
  to_mets_aux _ [] = return [] ∧
  to_mets_aux rank (methods::rest) =
  do
    mets <- result_mmap (to_met rank) methods;
    rest <- to_mets_aux (rank + 1) rest;
    return $ mets ++ rest
  od
End

Definition to_mets_def:
  to_mets methods = to_mets_aux 0 methods
End

Definition vcg_def:
  vcg (Program members) =
  do
    top_sorted_methods <- top_sorted_deps members;
    mets <- to_mets top_sorted_methods;
    result_mmap (met_vcg mets) mets
  od
End

(* In-logic testing *)
(* open dafny_compilerTheory; *)

(* val cwd = OS.FileSys.getDir (); *)
(* val fname = OS.Path.mkCanonical (cwd ^ "/../tests/examples/max_first_two.sexp"); *)

(* val inStream = TextIO.openIn fname; *)
(* val dafny = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)

(* val dafny_tm = stringSyntax.fromMLstring dafny; *)

(* val dafny_ast = EVAL “frontend ^dafny_tm” |> concl |> rhs |> rand; *)
(* val vcgs = EVAL “vcg ^dafny_ast” |> concl |> rhs |> rand; *)
