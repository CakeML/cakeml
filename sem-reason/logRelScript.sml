open preamble;
open finite_mapTheory;
open AstTheory TypeSystemTheory TypeSoundInvariantsTheory weakeningTheory;

val _ = new_theory "logRel";

(* A theory of logical relations.  Generally following Dreyer, Neis, Birkedal's
 * "The impact of higher-order state and control effects on local relational
 * reasoning" (JFP 2012), but greatly simplifying the treatment of local state.
 *
 * Many details differ because we are ML-like instead of SystemF-like.
 *)

val _ = Hol_datatype `
world = <| k : num; Sigma1 : tenvS; Sigma2 : tenvS; omega : unit |>`;

val _ = Hol_datatype `
rho = <| r : num |-> (world # v # v) ; p1 : t list ; p2 : t list |>`;

val world_n_def = Define `
world_n n w ⇔ w.k < n`;

val contAtom_n_def = Define
`contAtom_n n t1 t2 tenvM tenvC w k1 k2 ⇔ 
  world_n n w ∧
  (?t'. type_ctxts 0 tenvM tenvC w.Sigma1 k1 t1 t') ∧
  (?t'. type_ctxts 0 tenvM tenvC w.Sigma2 k2 t2 t')`;

val termVAtom_n_def = Define `
termVAtom_n n t1 t2 tenvM tenvC w v1 v2 ⇔
  world_n n w ∧
  type_v 0 tenvM tenvC w.Sigma1 v1 t1 ∧
  type_v 0 tenvM tenvC w.Sigma2 v2 t2`;

val termEAtom_n_def = Define `
termEAtom_n n t1 t2 tenvM tenvC (tenv1,tenv2) w e1 e2 ⇔
  world_n n w ∧
  type_e tenvM tenvC tenv1 e1 t1 ∧
  type_e tenvM tenvC tenv2 e2 t2`;

val envAtom_n_def = Define `
envAtom_n n tenv1 tenv2 tenvM tenvC w env1 env2 ⇔
  world_n n w ∧
  type_env tenvM tenvC w.Sigma1 env1 tenv1 ∧
  type_env tenvM tenvC w.Sigma1 env2 tenv2`;

val world_def = Define `
world w ⇔ ?n. world_n n w`;

val contAtom_def = Define
`contAtom t1 t2 tenvM tenvC w k1 k2 ⇔ 
  ∃n. contAtom_n n t1 t2 tenvM tenvC w k1 k2`;

val termVAtom_def = Define `
termVAtom t1 t2 tenvM tenvC w v1 v2 ⇔
  ?n. termVAtom_n n t1 t2 tenvM tenvC w v1 v2`;

val termEAtom_def = Define `
termEAtom t1 t2 tenvM tenvC tenv w e1 e2 ⇔
  ?n. termEAtom_n n t1 t2 tenvM tenvC tenv w e1 e2`;

val envAtom_def = Define `
envAtom tenv1 tenv2 tenvM tenvC w env1 env2 ⇔
  ?n. envAtom_n n tenv1 tenv2 tenvM tenvC w env1 env2`;

val later_def = Define `
later w w' ⇔
  w.k = w'.k + 1 ∧
  w.Sigma1 = w'.Sigma1 ∧
  w.Sigma2 = w'.Sigma2`;

val w_extends_def = Define `
w_extends w' w ⇔
  w'.k ≤ w.k ∧
  weakS w.Sigma1 w'.Sigma1 ∧
  weakS w.Sigma2 w'.Sigma2`; 

val _ = set_fixity "w_extends" (Infix (NONASSOC, 450));

val h_in_w_def = Define `
h_in_w tenvM tenvC h1 h2 w ⇔
  type_s tenvM tenvC w.Sigma1 h1 ∧
  type_s tenvM tenvC w.Sigma2 h2`;

val do_fn_app_def = Define `
(do_fn_app (Closure env n e) v ⇔
  SOME (bind n v env, e)) ∧
(do_fn_app (Recclosure env funs n) v ⇔
  case find_recfun n funs of
       SOME (n,e) => SOME (bind n v (build_rec_env funs env env), e)
     | NONE => NONE) ∧
(do_fn_app _ v ⇔ NONE)`;

(* ensure that v1 and v2 both have type t in world w and type environment p,
 * which can both differ between v1 and v2 *)
val check_VAtom_def = Define `
check_VAtom p t tenvM tenvC w v1 v2 ⇔
  termVAtom (deBruijn_subst 0 p.p1 t)
            (deBruijn_subst 0 p.p2 t)
            tenvM tenvC w v1 v2`;

val converges_def = Define `
converges s = ?s'. e_step_reln^* s s' ⇒ !s''. ~e_step_reln s' s''`;

val observe_v_def = Define `
observe_v tenvM tenvC w (k1,v1) (k2,v2) =
  !h1 h2 menv1 menv2 cenv1 cenv2. 
    h_in_w tenvM tenvC h1 h2 w ∧
    consistent_con_env cenv1 tenvC ∧
    consistent_con_env cenv2 tenvC ∧
    consistent_mod_env w.Sigma1 tenvC menv1 tenvM ∧
    consistent_mod_env w.Sigma2 tenvC menv2 tenvM ∧
    converges (menv1,cenv1,h1,ARB,Val v1,k1) ⇒
    converges (menv2,cenv2,h2,ARB,Val v2,k2)`;

val observe_e_def = Define `
observe_e tenvM tenvC w (k1,env1,e1) (k2,env2,e2) =
  !h1 h2 menv1 menv2 cenv1 cenv2. 
    h_in_w tenvM tenvC h1 h2 w ∧
    consistent_con_env cenv1 tenvC ∧
    consistent_con_env cenv2 tenvC ∧
    consistent_mod_env w.Sigma1 tenvC menv1 tenvM ∧
    consistent_mod_env w.Sigma2 tenvC menv2 tenvM ∧
    converges (menv1,cenv1,h1,env1,Exp e1,k1) ⇒
    converges (menv2,cenv2,h2,env2,Exp e2,k2)`;

val rel_v_def = tDefine "rel_v" `
(rel_v p (Tvar_db n) tenvM tenvC w v1 v2 ⇔
  FLOOKUP p.r n = SOME (w,v1,v2)) ∧

(rel_v p (Tapp [] TC_int) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [] TC_int) tenvM tenvC w v1 v2 ∧
  (v1 = v2)) ∧ 

(rel_v p (Tapp [] TC_bool) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [] TC_bool) tenvM tenvC w v1 v2 ∧
  (v1 = v2)) ∧ 

(rel_v p (Tapp [] TC_unit) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [] TC_unit) tenvM tenvC w v1 v2 ∧
  (v1 = v2)) ∧ 

(rel_v p (Tapp ts TC_tup) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp ts TC_tup) tenvM tenvC w v1 v2 ∧
  ?vs1 vs2.
    v1 = Conv NONE vs1 ∧
    v2 = Conv NONE vs2 ∧
    LIST_REL (λt (v1,v2). rel_v p t tenvM tenvC w v1 v2) ts (ZIP (vs1,vs2))) ∧

(rel_v p (Tapp [t1;t2] TC_fn) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [t1;t2] TC_fn) tenvM tenvC w v1 v2 ∧
  !w' v1' v2'.
    if w' w_extends w then
      if rel_v p t1 tenvM tenvC w' v1' v2' then
        ?e1 env1 e2 env2.
          do_fn_app v1 v1' = SOME (env1,e1) ∧
          do_fn_app v2 v2' = SOME (env2,e2) ∧
          rel_e p t2 tenvM tenvC w' (env1,e1) (env2,e2)
      else
        T
    else
      T) ∧

(*
(rel_v p (Tapp [t] TC_ref) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [t] TC_ref) tenvM tenvC w v1 v2 ∧
  ?l1 l2.
    v1 = Loc l1 ∧
    v2 = Loc l2 ∧
    ARB) ∧
*)

(rel_v p (Tapp [] TC_exn) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp [] TC_exn) tenvM tenvC w v1 v2 ∧
  ?vs1 vs2 cn ts' w'.
    if later w w' then
      v1 = Conv (SOME cn) vs1 ∧
      v2 = Conv (SOME cn) vs2 ∧
      lookup cn tenvC = SOME ([], ts', TypeExn) ∧
      LIST_REL (\t (v1,v2). rel_v p t tenvM tenvC w' v1 v2) ts' (ZIP (vs1,vs2))
    else
      F) ∧

(rel_v p (Tapp ts (TC_name n)) tenvM tenvC w v1 v2 ⇔
  check_VAtom p (Tapp ts (TC_name n)) tenvM tenvC w v1 v2 ∧
  ?vs1 vs2 cn tvs ts' w'.
    if later w w' then
      v1 = Conv (SOME cn) vs1 ∧
      v2 = Conv (SOME cn) vs2 ∧
      lookup cn tenvC = SOME (tvs, ts', TypeId n) ∧
      LIST_REL (\t (v1,v2). rel_v p t tenvM tenvC w' v1 v2) 
               (MAP (type_subst (ZIP (tvs, ts))) ts')
               (ZIP (vs1,vs2))
    else
      F) ∧

(rel_v p t tenvM tenvC w v1 v2 ⇔ F) ∧

(rel_k p t tenvM tenvC w k1 k2 ⇔
  contAtom t t tenvM tenvC w k1 k2 ∧
  !w' v1 v2. 
    if w' w_extends w then 
      rel_v p t tenvM tenvC w' v1 v2 ⇒ observe_v tenvM tenvC w' (k1,v1) (k2,v2)
    else
      T) ∧

(rel_e p t tenvM tenvC w (env1,e1) (env2,e2) ⇔
  ?tenv1 tenv2.
    envAtom tenv1 tenv2 tenvM tenvC w env1 env2 ∧
    termEAtom t t tenvM tenvC (tenv1,tenv2) w e1 e2 ∧
    !k1 k2.
      rel_k p t tenvM tenvC w k1 k2 ⇒ 
      observe_e tenvM tenvC w (k1,env1,e1) (k2,env2,e2))`

  (wf_rel_tac `inv_image ($< LEX $< LEX $<) 
                (\x.
                  case x of
                       INL (p,t,tenvM,tenvC,w,v1,v2) => 
                         (w.k, t_size t, 0:num)
                     | INR (INL (p,t,tenvM,tenvC,w,k1,k2)) => 
                         (w.k, t_size t, 1)
                     | INR (INR (p,t,tenvM,tenvC,w,(env1,e1),(env2,e2))) => 
                         (w.k, t_size t, 2))` >>
  rw [later_def, w_extends_def, MEM_MAP]
  >- decide_tac
  >- cheat (* from the TC_fn case *)
  >- decide_tac
  >- (Induct_on `ts` >>
      rw [t_size_def] >>
      res_tac >>
      decide_tac));



val _ = export_theory();
