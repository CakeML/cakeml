(*
  Various lemmas that are handy in the soundness and completeness
  proofs of the type inferencer.
*)
Theory inferProps
Ancestors
  namespaceProps typeSystem ast semanticPrimitives infer unify
  infer_t typeSysProps
Libs
  preamble

Theorem ienv_unchanged[simp]:
   (ienv with inf_v := ienv.inf_v) = ienv ∧
   (ienv with inf_c := ienv.inf_c) = ienv ∧
   (ienv with inf_t := ienv.inf_t) = ienv
Proof
 rw [inf_env_component_equality]
QED

Theorem extend_dec_ienv_empty:
   !ienv.
    extend_dec_ienv ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |> = ienv ∧
    extend_dec_ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |> ienv = ienv
Proof
  rw [extend_dec_ienv_def, inf_env_component_equality]
QED

(* ---------- Facts about deBruijn increment ---------- *)

Theorem infer_deBruijn_inc0:
 !(n:num) t. infer_deBruijn_inc 0 t = t
Proof
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []
QED

Theorem infer_deBruijn_inc0_id:
 infer_deBruijn_inc 0 = (\x.x)
Proof
metis_tac [infer_deBruijn_inc0]
QED

Theorem t_vars_inc:
 !tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t
Proof
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [t_vars_def, encode_infer_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw [encode_infer_t_def]
QED

Theorem inc_wfs:
 !tvs s. t_wfs s ⇒ t_wfs (infer_deBruijn_inc tvs o_f s)
Proof
rw [t_wfs_eqn] >>
`t_vR s = t_vR (infer_deBruijn_inc tvs o_f s)`
       by (rw [FLOOKUP_o_f, FUN_EQ_THM, t_vR_eqn] >>
           full_case_tac  >>
           rw [t_vars_inc]) >>
metis_tac []
QED

Theorem vwalk_inc:
 !s tvs n.
  t_wfs s
  ⇒
  t_vwalk (infer_deBruijn_inc tvs o_f s) n = infer_deBruijn_inc tvs (t_vwalk s n)
Proof
rw [] >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
rw [] >>
Q.SPEC_TAC (`n`, `n`) >>
qpat_x_assum `!p. (!v. q v ⇒ p v) ⇒ !v. p v` ho_match_mp_tac >>
rw [] >>
imp_res_tac t_vwalk_eqn >>
once_asm_rewrite_tac [] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
cases_on `FLOOKUP s n` >>
rw [FLOOKUP_o_f, infer_deBruijn_inc_def] >>
cases_on `x` >>
rw [infer_deBruijn_inc_def]
QED

Theorem walk_inc:
 !s tvs t.
  t_wfs s
  ⇒
  t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) = infer_deBruijn_inc tvs (t_walk s t)
Proof
rw [] >>
cases_on `t` >>
rw [t_walk_eqn, infer_deBruijn_inc_def, vwalk_inc]
QED

Theorem walkstar_inc:
 !tvs s t.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) =
   infer_deBruijn_inc tvs (t_walkstar s t))
Proof
rw [] >>
imp_res_tac t_walkstar_ind >>
Q.SPEC_TAC (`t`, `t`) >>
pop_assum ho_match_mp_tac >>
rw [] >>
rw [walk_inc] >>
cases_on `t_walk s t` >>
rw [infer_deBruijn_inc_def] >>
imp_res_tac inc_wfs >>
rw [t_walkstar_eqn,infer_deBruijn_inc_def, walk_inc] >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum (fn _ => all_tac) >>
induct_on `l` >>
rw [] >>
fs []
QED

Theorem walkstar_inc2:
 !tvs s n.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
   infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))
Proof
rw [GSYM walkstar_inc, infer_deBruijn_inc_def]
QED

(* ---------- Type substitution ---------- *)

Theorem subst_infer_subst_swap:
 (!t tvs s uvar.
  t_wfs s ⇒
  (t_walkstar s (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))) t)
   =
   infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs)))) t)) ∧
 (!ts tvs s uvar.
  t_wfs s ⇒
  (MAP (t_walkstar s) (MAP (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs))))) ts)
   =
   MAP (infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs))))) ts))
Proof
 ho_match_mp_tac t_induction >>
 rw [type_subst_def, infer_type_subst_alt, t_walkstar_eqn1]
 >- (every_case_tac >>
     rw [t_walkstar_eqn1] >>
     fs [ALOOKUP_FAILS] >>
     fs [MAP_ZIP, LENGTH_COUNT_LIST, ALOOKUP_ZIP_MAP_SND] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
     metis_tac [])
QED

val infer_t_induction = infer_tTheory.infer_t_induction;

Theorem infer_subst_FEMPTY:
 (!t. infer_subst FEMPTY t = t) ∧
 (!ts. MAP (infer_subst FEMPTY) ts = ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [SUBSET_DEF, infer_subst_def] >>
metis_tac []
QED

Theorem infer_subst_submap:
 (!t s1 s2 m.
    s1 SUBMAP s2 ∧
    {uv | uv ∈ t_vars t ∧ m ≤ uv} ⊆ FDOM s1 ∧
    (!uv. uv ∈ FDOM s2 DIFF FDOM s1 ⇒ m ≤ uv)
    ⇒
    (infer_subst s1 t = infer_subst s2 t)) ∧
 (!ts s1 s2 m.
    s1 SUBMAP s2 ∧
    {uv | ?s. uv ∈ s ∧ MEM s (MAP t_vars ts) ∧ m ≤ uv} ⊆ FDOM s1 ∧
    (!uv. uv ∈ FDOM s2 DIFF FDOM s1 ⇒ m ≤ uv)
    ⇒
    (MAP (infer_subst s1) ts = MAP (infer_subst s2) ts))
Proof
  ho_match_mp_tac infer_t_induction >>
  rw [SUBSET_DEF, infer_subst_def, t_vars_eqn]
  >-
    metis_tac []
  >- (
    full_case_tac >>
    full_case_tac >>
    rw [] >>
    fs [SUBMAP_DEF, FLOOKUP_DEF] >>
    metis_tac [])
  >-
    metis_tac []
  >>
    metis_tac []
QED

Theorem generalise_list_length:
    ∀a b c d e f g.
  generalise_list a b c d = (e,f,g) ⇒ LENGTH g = LENGTH d
Proof
  Induct_on`d`>>fs[generalise_def]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  res_tac>>fs[]>>rveq>>fs[]
QED

Theorem generalise_subst:
 (!t m n s tvs s' t'.
  (generalise m n s t = (tvs, s', t'))
  ⇒
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ t_vars t ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (!uv. uv ∈ t_vars t' ⇒ uv < m) ∧
  (infer_subst s' t = infer_subst s t')) ∧
 (!ts m n s tvs s' ts'.
  (generalise_list m n s ts = (tvs, s', ts'))
  ⇒
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ BIGUNION (set (MAP t_vars ts)) ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (!uv. uv ∈  BIGUNION (set (MAP t_vars ts')) ⇒ uv < m) ∧
  (MAP (infer_subst s') ts = MAP (infer_subst s) ts'))
Proof
  Induct >>
  SIMP_TAC (srw_ss()) [t_vars_eqn, generalise_def, infer_subst_def]
  >- (
    REPEAT GEN_TAC  >>
    STRIP_TAC >>
    fs[]>>pairarg_tac>>fs[]>>
    first_x_assum old_drule>> simp[]>>
    rveq>>fs[]>>
    rw [EXTENSION, infer_subst_def] >>
    fs [t_vars_eqn] >>
    metis_tac [])
  >- (
    rw [] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    rw [FLOOKUP_DEF, EXTENSION] >>
    TRY (EQ_TAC) >>
    rw [] >>
    fs [FLOOKUP_DEF, infer_subst_def, t_vars_eqn] >>
    decide_tac)
  >>
    REPEAT GEN_TAC >>
    STRIP_TAC >>
    `?tvs s' t'. generalise m n s t = (tvs, s', t')`
              by (cases_on `generalise m n s t` >>
                  rw [] >>
                  cases_on `r` >>
                  fs []) >>
    fs [LET_THM] >>
    `?tvs s' ts'. generalise_list m (tvs'+n) s'' ts = (tvs, s', ts')`
              by (cases_on `generalise_list m (tvs'+n) s'' ts` >>
                  rw [] >>
                  cases_on `r` >>
                  fs []) >>
    fs [LET_THM] >>
    qpat_x_assum `!m'. P m'`
          (mp_tac o Q.SPECL [`m`, `tvs'+n`, `s''`, `tvs''`, `s'''`, `ts''`]) >>
    qpat_x_assum `!m'. P m'`
          (mp_tac o Q.SPECL [`m`, `n`, `s`, `tvs'`, `s''`, `t'`]) >>
    rw [INTER_UNION]
    >-
      metis_tac [SUBMAP_TRANS]
    >- (rw [EXTENSION] >> metis_tac [])
    >- (
      `uv ∈ FDOM s''` by fs [] >>
      res_tac >>
      rw [INTER_UNION] >>
      fs [SUBMAP_DEF])
    >- (
      `uv ∈ FDOM s''` by fs [] >>
      res_tac >>
      rw [INTER_UNION] >>
      fs [SUBMAP_DEF] >>
      res_tac >>
      decide_tac)
    >- (
      `uv ∈ FDOM s'` by (fs [] >> metis_tac []) >>
      cases_on `uv ∈ t_vars t` >>
      rw [] >>
      res_tac >>
      rw [INTER_UNION] >>
      fs [SUBMAP_DEF] >>
      res_tac >>
      decide_tac)
    >- (
      `uv ∈ FDOM s'` by (fs [] >> metis_tac []) >>
      cases_on `uv ∈ t_vars t` >>
      rw [] >>
      `uv ∈ FDOM s''` by (fs [] >> metis_tac []) >>
      res_tac >>
      rw [INTER_UNION] >>
      fs [SUBMAP_DEF] >>
      res_tac >>
      decide_tac)
     >- metis_tac []
     >- metis_tac []
     >- (
       `{uv | uv ∈ t_vars t ∧ m ≤ uv} ⊆ FDOM s'' ∧
       (!uv. uv ∈ FDOM s' DIFF FDOM s'' ⇒ m ≤ uv)` by
         rw [SUBSET_DEF] >>
       metis_tac [infer_subst_submap])
     >>
     `{uv | ∃s. uv ∈ s ∧ MEM s (MAP t_vars ts'') ∧ m ≤ uv} ⊆ FDOM s ∧ (!uv. uv ∈ FDOM s'' DIFF FDOM s ⇒ m ≤ uv)` by
       (rw [SUBSET_DEF] >>
       `¬(x < m)` by decide_tac  >>
       metis_tac []) >>
     metis_tac [infer_subst_submap]
QED

Theorem generalise_subst_empty:
 !n ts tvs s ts'.
  (generalise_list 0 n FEMPTY ts = (tvs, s, ts'))
  ⇒
  (FDOM s = { uv | uv ∈ BIGUNION (set (MAP t_vars ts)) }) ∧
  (!uv. uv ∈ FDOM s ⇒ ∃tv. (FAPPLY s uv = tv) ∧ tv < tvs + n) ∧
  (BIGUNION (set (MAP t_vars ts')) = {}) ∧
  (ts' = MAP (infer_subst s) ts)
Proof
  rw [] >>
  imp_res_tac generalise_subst >>
  fs [] >>
  rw []
  >- (
    rw [BIGUNION, EXTENSION] >>
    metis_tac [])
  >- (
    fs [EXTENSION] >>
    metis_tac [])
  >- (
    cases_on `ts'` >>
    rw [] >>
    rw [EXTENSION] >>
    eq_tac >>
    rw [] >>
    fs [t_vars_eqn] >>
    metis_tac [])
  >>
  metis_tac [infer_subst_FEMPTY]
QED

(* ---------- Dealing with the monad ---------- *)

(* TODO: update *)
Theorem infer_st_rewrs:
 (!st. (st with next_uvar := st.next_uvar) = st) ∧
 (!st. (st with subst := st.subst) = st) ∧
 (!st s. (st with subst := s).subst = s) ∧
 (!st s. (st with subst := s).next_uvar = st.next_uvar) ∧
 (!st uv. (st with next_uvar := uv).next_uvar = uv) ∧
 (!st uv. (st with next_uvar := uv).subst = st.subst)
Proof
  rw [] >>
  cases_on `st` >>
  rw [infer_st_component_equality]
QED

Theorem st_ex_return_success[local]:
  !v st v' st'.
  (st_ex_return v st = (Success v', st')) =
  ((v = v') ∧ (st = st'))
Proof
  rw [st_ex_return_def]
QED

Theorem st_ex_bind_success[local]:
  !f g st st' v.
 (st_ex_bind f g st = (Success v, st')) =
 ?v' st''. (f st = (Success v', st'')) /\ (g v' st'' = (Success v, st'))
Proof
  rw [st_ex_bind_def] >>
cases_on `f st` >>
rw [] >>
cases_on `q` >>
rw []
QED

Theorem fresh_uvar_success[local]:
  !st t st'.
  (fresh_uvar st = (Success t, st')) =
  ((t = Infer_Tuvar st.next_uvar) ∧
   (st' = st with next_uvar := st.next_uvar + 1))
Proof
  rw [fresh_uvar_def] >>
metis_tac []
QED

Theorem n_fresh_uvar_success:
 !n st ts st'.
  (n_fresh_uvar n st = (Success ts, st')) =
  ((ts = MAP (\n. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST n)) ∧
   (st' = st with next_uvar := st.next_uvar + n))
Proof
ho_match_mp_tac n_fresh_uvar_ind >>
rw [] >>
rw [st_ex_return_success, Once n_fresh_uvar_def, COUNT_LIST_SNOC,
    st_ex_bind_success, fresh_uvar_success, infer_st_rewrs] >-
metis_tac [] >>
fs [] >>
srw_tac [ARITH_ss] [] >>
rw [count_list_sub1, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
eq_tac >>
srw_tac [ARITH_ss] [arithmeticTheory.ADD1]
QED

Theorem apply_subst_success[local]:
  !t1 st1 t2 st2.
  (apply_subst t1 st1 = (Success t2, st2))
  =
  ((st2 = st1) ∧
   (t2 = t_walkstar st1.subst t1))
Proof
  rw [st_ex_return_def, st_ex_bind_def, LET_THM, apply_subst_def, read_def] >>
eq_tac >>
rw []
QED

Theorem add_constraint_success:
 !l t1 t2 st st' x.
  (add_constraint l t1 t2 st = (Success x, st'))
  =
  ((x = ()) ∧ (?s. (t_unify st.subst t1 t2 = SOME s) ∧ (st' = st with subst := s)))
Proof
rw [add_constraint_def] >>
full_case_tac >>
metis_tac []
QED

Theorem add_constraints_success[local]:
  !l ts1 ts2 st st' x.
  (add_constraints l ts1 ts2 st = (Success x, st'))
  =
  ((LENGTH ts1 = LENGTH ts2) ∧
   ((x = ()) ∧
   (st.next_uvar = st'.next_uvar) ∧
   (st.next_id = st'.next_id) ∧
   pure_add_constraints st.subst (ZIP (ts1,ts2)) st'.subst))
Proof
  ho_match_mp_tac add_constraints_ind >>
rw [add_constraints_def, pure_add_constraints_def, st_ex_return_success,
    failwith_def, st_ex_bind_success, add_constraint_success] >>
TRY (cases_on `x`) >>
rw [pure_add_constraints_def] >-
metis_tac [infer_st_component_equality] >>
eq_tac >>
rw [] >>
cases_on `t_unify st.subst t1 t2` >>
fs []
QED

Theorem add_constraints_nil2_success[local]:
  (add_constraints l ts1 [] st = (Success x, st'))
  = (ts1 = [] /\ st = st')
Proof
  Cases_on `ts1` \\ simp [add_constraints_def]
  \\ simp [failwith_def, st_ex_bind_success, st_ex_return_success]
QED

Theorem add_constraints_cons2_success[local]:
  (add_constraints l ts1 (t2 :: ts2) st = (Success x, st'))
  = (?t1 tl1 st''. ts1 = t1 :: tl1 /\
    add_constraint l t1 t2 st = (Success (), st'') /\
    add_constraints l tl1 ts2 st'' = (Success x, st'))
Proof
  Cases_on `ts1` \\ simp [add_constraints_def]
  \\ simp [failwith_def, st_ex_bind_success, st_ex_return_success]
QED

Theorem failwith_success[local]:
  !l m st v st'. (failwith l m st = (Success v, st')) = F
Proof
  rw [failwith_def]
QED

Theorem lookup_st_ex_success[local]:
  !loc x err l st v st'.
  (lookup_st_ex loc err x l st = (Success v, st'))
  =
  ((nsLookup l x = SOME v) ∧ (st = st'))
Proof
  rw [lookup_st_ex_def, failwith_def, st_ex_return_success]
 >> every_case_tac
QED

val op_data = {nchotomy = op_nchotomy, case_def = op_case_def};
val op_case_eq = prove_case_eq_thm op_data;
val op_case_rand = prove_case_rand_thm op_data;
val list_data = {nchotomy = list_nchotomy, case_def = list_case_def}
val list_case_eq = prove_case_eq_thm list_data;
val list_case_rand = prove_case_rand_thm list_data;

val bool_data = {nchotomy = TypeBase.nchotomy_of bool,
        case_def = TypeBase.case_def_of bool}
val bool_case_rand = prove_case_rand_thm bool_data;

fun mk_case_rator case_rand =
  case_rand
  |> GEN (case_rand |> concl |> lhs |> rator)
  |> ISPEC (let val z = genvar(gen_tyvar())
                val r = genvar(type_of z --> gen_tyvar())
            in mk_abs(r,mk_comb(r,z)) end)
  |> BETA_RULE

val list_case_rator = mk_case_rator list_case_rand
val op_case_rator = mk_case_rator op_case_rand
val bool_case_rator = mk_case_rator bool_case_rand

Theorem UNCURRY_rator:
  UNCURRY f x y = UNCURRY (\a b. f a b y) x
Proof
  Cases_on `x` \\ simp []
QED

Theorem constrain_op_op_case[local]:
  constrain_op l op ts st = (case op of
      Opapp => let x = () in constrain_op l op ts st
    | _ => constrain_op l op ts st)
Proof
  CASE_TAC \\ simp []
QED

val constrain_op_success =
  ``(constrain_op l op ts st = (Success v, st'))``
  |> (REWRITE_CONV [Once constrain_op_op_case, op_case_eq]
    THENC SIMP_CONV (srw_ss () ++ CONJ_ss) [constrain_op_case_def,
        op_simple_constraints_def, LET_THM, bool_case_eq,
        st_ex_bind_success,st_ex_return_success,
        add_constraint_success,failwith_success,
        add_constraints_cons2_success,
        add_constraints_nil2_success,
        list_case_rator, list_case_eq, bool_case_rator, bool_case_eq,
        PULL_EXISTS]
  )

Theorem constrain_op_success =
  constrain_op_success

Theorem get_next_uvar_success[local]:
  !st v st'.
  (get_next_uvar st = (Success v, st'))
  =
  ((v = st.next_uvar) ∧ (st = st'))
Proof
  rw [get_next_uvar_def] >>
metis_tac []
QED

val apply_subst_list_success =
  SIMP_CONV (srw_ss()) [apply_subst_list_def, LET_THM]
  ``(apply_subst_list ts st = (Success v, st'))``

Theorem guard_success[local]:
  ∀P l m st v st'.
  (guard P l m st = (Success v, st'))
  =
  (P ∧ (v = ()) ∧ (st = st'))
Proof
  rw [guard_def, st_ex_return_def, failwith_def] >>
metis_tac []
QED

Theorem check_dups_success:
   !l f ls s r s'.
    check_dups l f ls s = (Success r, s')
    ⇔
    s' = s ∧ ALL_DISTINCT ls
Proof
  Induct_on `ls` >>
  rw [check_dups_def, st_ex_return_def, failwith_def] >>
  metis_tac []
QED

Theorem type_name_check_subst_success:
   (!t l f tenvT tvs r (s:'a) s'.
    type_name_check_subst l f tenvT tvs t s = (Success r, s')
    ⇔
    s = s' ∧ r = type_name_subst tenvT t ∧
    check_freevars_ast tvs t ∧ check_type_names tenvT t) ∧
   (!ts l f tenvT tvs r (s:'a) s'.
    type_name_check_subst_list l f tenvT tvs ts s = (Success r, s')
    ⇔
    s = s' ∧ r = MAP (type_name_subst tenvT) ts ∧
    EVERY (check_freevars_ast tvs) ts ∧ EVERY (check_type_names tenvT) ts)
Proof
 Induct >>
 rw [type_name_check_subst_def, st_ex_bind_def, guard_def, st_ex_return_def,
     check_freevars_ast_def, check_type_names_def, failwith_def,
     type_name_subst_def] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 TRY pairarg_tac >>
 fs [] >>
 every_case_tac >>
 fs [lookup_st_ex_success, lookup_st_ex_def] >>
 metis_tac [exc_distinct, PAIR_EQ, NOT_EVERY]
QED

Theorem check_ctor_types_success:
   !l tenvT tvs ts s s'.
   check_ctor_types l tenvT tvs ts s = (Success (),s') ⇔
   s = s' ∧
   EVERY (λ(cn,ts).  EVERY (check_freevars_ast tvs) ts ∧
   EVERY (check_type_names tenvT) ts) ts
Proof
  Induct_on `ts` >>
  rw [check_ctor_types_def, st_ex_return_def] >>
  PairCases_on `h` >>
  rw [check_ctor_types_def, st_ex_bind_def] >>
  every_case_tac >>
  fs [type_name_check_subst_success] >>
  CCONTR_TAC >>
  fs [combinTheory.o_DEF] >>
  metis_tac [exc_distinct, PAIR_EQ, type_name_check_subst_success]
QED

Theorem check_dup_ctors_thm:
   check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
Proof
  rw [check_dup_ctors_def] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  eq_tac >>
  rw [] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs []
QED

Theorem check_ctors_success:
  !l tenvT tds s s'.
   ALL_DISTINCT (MAP (FST o SND) tds) ⇒
   (check_ctors l tenvT tds s = (Success (),s') ⇔
    s' = s ∧ check_ctor_tenv tenvT tds)
Proof
  Induct_on `tds` >>
  rw [] >>
  TRY (PairCases_on `h`) >>
  fs [check_ctor_tenv_def, check_type_definition_def, st_ex_bind_def,
      check_ctors_def, st_ex_return_def, check_dup_ctors_thm]
  >- metis_tac [] >>
  every_case_tac >>
  fs [check_dups_success, st_ex_return_def, check_type_definition_def,
      check_ctor_types_success] >>
  fs [check_dups_def, st_ex_return_def, st_ex_bind_def, LAMBDA_PROD,
      combinTheory.o_DEF] >>
  CCONTR_TAC >>
  fs [combinTheory.o_DEF, ETA_THM] >>
  rw [] >>
  TRY (
    Induct_on `h2` >>
    fs [check_dups_def, st_ex_return_def] >>
    rw [] >>
    NO_TAC)
  >- metis_tac [exc_distinct, PAIR_EQ, check_dups_success]
  >- (
    Induct_on `h2` >>
    fs [] >>
    rw [check_ctor_types_def, st_ex_return_def] >>
    PairCases_on `h` >>
    fs [check_ctor_types_def, st_ex_return_def, st_ex_bind_def] >>
    every_case_tac >>
    fs [type_name_check_subst_success] >>
    rw [] >>
    metis_tac [NOT_EVERY, exc_distinct, PAIR_EQ, type_name_check_subst_success])
  >- metis_tac [exc_distinct, PAIR_EQ, check_dups_success]
  >- metis_tac [exc_distinct, PAIR_EQ, check_dups_success]
  >- metis_tac [exc_distinct, PAIR_EQ, check_dups_success]
QED

Theorem check_type_definition_success:
   !l tenvT tds s r s'.
    check_type_definition l tenvT tds s = (Success r, s')
    ⇔
    s' = s ∧ check_ctor_tenv tenvT tds
Proof
 rw [check_type_definition_def, st_ex_bind_def] >>
 every_case_tac >>
 fs [check_dups_success]
 >- metis_tac [check_ctors_success] >>
 `~ALL_DISTINCT (MAP (FST ∘ SND) tds)`
 by metis_tac [exc_distinct, PAIR_EQ, check_dups_success] >>
 pop_assum mp_tac >>
 pop_assum kall_tac >>
 Induct_on `tds` >>
 rw [] >>
 PairCases_on `h` >>
 rw [check_ctor_tenv_def] >>
 fs [LAMBDA_PROD, combinTheory.o_DEF]
QED

Theorem option_case_eq[local]:
  !opt f g v st st'.
  ((case opt of NONE => f | SOME x => g x) st = (Success v, st')) =
  (((opt = NONE) ∧ (f st = (Success v, st'))) ∨ (?x. (opt = SOME x) ∧ (g x st = (Success v, st'))))
Proof
  rw [] >>
cases_on `opt` >>
fs []
QED

val success_eqns =
  LIST_CONJ [st_ex_return_success, st_ex_bind_success, fresh_uvar_success,
             apply_subst_success, add_constraint_success, lookup_st_ex_success,
             n_fresh_uvar_success, failwith_success, add_constraints_success,
             oneTheory.one, check_type_definition_success,
             get_next_uvar_success, apply_subst_list_success, guard_success,
             read_def, option_case_eq, check_dups_success,
             type_name_check_subst_success,
             check_ctor_types_success,
             check_ctors_success];

Theorem success_eqns =
  success_eqns

Theorem remove_pair_lem:
 (!f v. (\(x,y). f x y) v = f (FST v) (SND v)) ∧
 (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND (SND v)))
Proof
rw [] >>
PairCases_on `v` >>
rw []
QED

(* ---------- Simple structural properties ---------- *)

Theorem infer_funs_length:
 !l ienv funs ts st1 st2.
  (infer_funs l ienv funs st1 = (Success ts, st2)) ⇒
  (LENGTH funs = LENGTH ts)
Proof
induct_on `funs` >>
rw [infer_e_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
metis_tac []
QED

Theorem type_name_check_subst_state:
  (!t l err tenvT fvs (st:'a) r st'. type_name_check_subst l err tenvT fvs t st = (r,st') ⇒ st = st') ∧
  (!ts l err tenvT fvs (st:'a) r st'. type_name_check_subst_list l err tenvT fvs ts st = (r,st') ⇒ st = st')
Proof
  Induct >>
  rw [type_name_check_subst_def, st_ex_bind_def, guard_def, st_ex_return_def,
      failwith_def, lookup_st_ex_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  TRY pairarg_tac >>
  fs [] >>
  every_case_tac >>
  fs [] >>
  metis_tac []
QED

Theorem infer_p_bindings:
 (!l cenv p st t env st' x.
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    (pat_bindings p x = MAP FST env ++ x)) ∧
 (!l cenv ps st ts env st' x.
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
    (pats_bindings ps x = MAP FST env ++ x))
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [pat_bindings_def, infer_p_def, success_eqns, remove_pair_lem]
  >- (PairCases_on `v'` >>
      rw [] >>
      metis_tac [])
  >- (PairCases_on `v''` >>
      rw [] >>
      metis_tac [])
  >- (PairCases_on `v'` >>
      rw [] >>
      metis_tac [])
  >- (
    PairCases_on `v'` >>
    first_x_assum drule>>
    simp[])
  >- metis_tac []
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      rw [] >>
      metis_tac [APPEND_ASSOC])
QED

(* ---------- Dealing with the constraint set ---------- *)

Theorem pure_add_constraints_append2[local]:
  !s1 ts s2 t1 t2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)
Proof
  induct_on `ts` >>
rw [pure_add_constraints_def] >>
rw [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs, t_unify_apply2]
QED

Theorem pure_add_constraints_apply:
 !s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts
Proof
induct_on `ts` >>
rw [pure_add_constraints_def] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_apply, pure_add_constraints_append2, t_unify_wfs]
QED

Theorem pure_add_constraints_append:
 !s1 ts1 s3 ts2.
  pure_add_constraints s1 (ts1 ++ ts2) s3
  =
  (?s2. pure_add_constraints s1 ts1 s2 ∧ pure_add_constraints s2 ts2 s3)
Proof
ho_match_mp_tac pure_add_constraints_ind >>
rw [pure_add_constraints_def] >>
metis_tac []
QED

Theorem infer_p_constraints:
 (!l cenv p st t env st'.
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!l cenv ps st ts env st'.
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
    (?ts'. pure_add_constraints st.subst ts' st'.subst))
Proof
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, type_name_check_subst_state]
QED

Theorem infer_e_constraints:
 (!l ienv e st st' t.
    (infer_e l ienv e st = (Success t, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!l ienv es st st' ts.
    (infer_es l ienv es st = (Success ts, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!l ienv pes t1 t2 st st'.
    (infer_pes l ienv pes t1 t2 st = (Success (), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!l ienv funs st st' ts'.
    (infer_funs l ienv funs st = (Success ts', st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst))
Proof
  ho_match_mp_tac infer_e_ind >>
  rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem,
      GSYM FORALL_PROD] >>
  rw [] >>~-
  ([‘∃y. pure_add_constraints x y x (* g *)’],
   irule_at Any (iffRL (cj 1 pure_add_constraints_def)) >> simp[]) >>
  rpt (first_x_assum $ drule_then strip_assume_tac) >> simp[] >>
  gvs[success_eqns]
  >~ [‘t_unify s2.subst t1 (FST v) = SOME s’]
  >- (Cases_on ‘v’ >> gvs[] >>
      prove_tac [pure_add_constraints_append, pure_add_constraints_def,
                 infer_p_constraints, type_name_check_subst_state])
  >~ [‘supported_arith a ty’]
  >- (Cases_on ‘supported_arith a ty’
      \\ gvs [failwith_def,AllCaseEqs(),st_ex_bind_def,st_ex_return_def]
      \\ gvs [add_constraints_success]
      \\ prove_tac [pure_add_constraints_append, pure_add_constraints_def,
                    infer_p_constraints, type_name_check_subst_state])
  \\ prove_tac [pure_add_constraints_append, pure_add_constraints_def,
                infer_p_constraints, type_name_check_subst_state]
QED

Theorem pure_add_constraints_wfs:
 !s1 ts s2.
  pure_add_constraints s1 ts s2 ∧
  t_wfs s1
  ⇒
  t_wfs s2
Proof
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]
QED

(* ---------- The next unification variable is monotone non-decreasing ---------- *)

Theorem infer_p_next_uvar_mono:
 (!l cenv p st t env st'.
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!l cenv ps st ts env st'.
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)
Proof
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
`st''' = st''` by metis_tac [type_name_check_subst_state] >>
metis_tac [DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``,
           arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem infer_e_next_uvar_mono:
 (!l ienv e st st' t.
    (infer_e l ienv e st = (Success t, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!l ienv es st st' ts.
    (infer_es l ienv es st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!l ienv pes t1 t2 st st'.
    (infer_pes l ienv pes t1 t2 st = (Success (), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!l ienv funs st st' ts.
    (infer_funs l ienv funs st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)
Proof
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
every_case_tac >> TRY (Cases_on `uop:fp_uop`) >>
fs [success_eqns]>>
metis_tac [infer_p_next_uvar_mono, arithmeticTheory.LESS_EQ_TRANS,
           pair_CASES,type_name_check_subst_state,
           DECIDE ``!(x:num) y. x ≤ x + y``,
           DECIDE ``!(x:num) y. x + 1 ≤ y ⇒ x ≤ y``,
           DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``]
QED

(* ---------- The inferencer builds well-formed substitutions ---------- *)

Theorem infer_p_wfs:
 (!l cenv p st t env st'.
    t_wfs st.subst ∧
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    t_wfs st'.subst) ∧
 (!l cenv ps st ts env st'.
    t_wfs st.subst ∧
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
   t_wfs st'.subst)
Proof
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs []
>- prove_tac [pure_add_constraints_wfs]
>- metis_tac [t_unify_wfs, type_name_check_subst_state]
QED

Theorem infer_e_wfs:
 (!l ienv e st st' t.
    infer_e l ienv e st = (Success t, st') ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!l ienv es st st' ts.
    infer_es l ienv es st = (Success ts, st') ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!l ienv pes t1 t2 st st'.
    infer_pes l ienv pes t1 t2 st = (Success (), st') ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!l ienv funs st st' ts'.
    infer_funs l ienv funs st = (Success ts', st') ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst)
Proof
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
fs [] >>
res_tac >>
imp_res_tac t_unify_wfs >>
fs [] >>
imp_res_tac pure_add_constraints_wfs >>
fs [] >>
TRY (cases_on `v'`) >>
imp_res_tac infer_p_wfs >>
fs [] >>
every_case_tac >> TRY (cases_on `uop:fp_uop`) >>
fs [success_eqns] >>
rw [] >>
fs [infer_st_rewrs] >>
res_tac >>
fs [] >>
imp_res_tac t_unify_wfs >>
metis_tac [type_name_check_subst_state]
QED

(* ---------- The invariants of the inferencer ---------- *)

Theorem check_t_more:
 (!t tvs. check_t tvs {} t ⇒ !uvs. check_t tvs uvs t) ∧
 (!ts tvs. EVERY (check_t tvs {}) ts ⇒ !uvs. EVERY (check_t tvs uvs) ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []
QED

Theorem check_t_more2:
 (!t tvs uvs. check_t tvs uvs t ⇒ !tvs'. check_t (tvs' + tvs) uvs t) ∧
 (!ts tvs uvs. EVERY (check_t tvs uvs) ts ⇒ !tvs'. EVERY (check_t (tvs' + tvs) uvs) ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []
QED

Theorem check_t_more3:
 (!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. check_t tvs (count (uvs + uvs')) t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. EVERY (check_t tvs (count (uvs + uvs'))) ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
metis_tac [] >>
decide_tac
QED

Theorem check_t_more4:
 (!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. uvs ≤ uvs' ⇒ check_t tvs (count uvs') t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. uvs ≤ uvs' ⇒ EVERY (check_t tvs (count uvs')) ts)
Proof
ho_match_mp_tac infer_t_induction >>
srw_tac [ARITH_ss] [check_t_def] >>
metis_tac []
QED

Theorem check_t_more5:
 (!t uvs tvs. check_t tvs uvs t ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_t tvs uvs' t) ∧
 (!ts uvs tvs. EVERY (check_t tvs uvs) ts ⇒ !uvs'. uvs ⊆ uvs' ⇒ EVERY (check_t tvs uvs') ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, SUBSET_DEF] >>
metis_tac []
QED

Theorem check_t_t_vars:
 !tvs uvs t.
  check_t tvs uvs t ⇒ t_vars t ⊆ uvs
Proof
ho_match_mp_tac check_t_ind >>
rw [t_vars_eqn, check_t_def, EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
metis_tac []
QED

Theorem check_s_more[local]:
  !s tvs uvs. check_s tvs (count uvs) s ⇒ check_s tvs (count (uvs + 1)) s
Proof
  rw [check_s_def] >>
metis_tac [check_t_more3]
QED

Theorem check_s_more2:
 !s uvs. check_s tvs (count uvs) s ⇒ !uvs'. uvs ≤ uvs' ⇒ check_s tvs (count uvs') s
Proof
rw [check_s_def] >>
metis_tac [check_t_more4]
QED

Theorem check_s_more3:
 !s uvs. check_s tvs uvs s ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_s tvs uvs' s
Proof
rw [check_s_def] >>
metis_tac [check_t_more5]
QED

Theorem check_s_more5:
 !s uvs tvs uvs'. check_s tvs uvs s ∧ uvs ⊆ uvs' ⇒ check_s tvs uvs' s
Proof
 rw [check_s_def] >>
 metis_tac [check_t_more5]
QED

Theorem check_t_deBruijn_inc2:
 !inc t s. check_t tvs s t ⇒ check_t (inc + tvs) s (infer_deBruijn_inc inc t)
Proof
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [check_t_def, infer_deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM]
QED

Theorem check_t_deBruijn_inc:
 !inc t. check_t 0 UNIV t ⇒ (infer_deBruijn_inc inc t = t)
Proof
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [check_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []
QED

Theorem infer_deBruijn_subst_twice:
   (∀t.
    check_t (LENGTH subst2) uvs t ⇒
    (infer_deBruijn_subst subst1 (infer_deBruijn_subst subst2 t) =
     infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1) subst2) t)) ∧
   (∀ts.
    EVERY (check_t (LENGTH subst2) uvs) ts ⇒
    MAP ((infer_deBruijn_subst subst1) o (infer_deBruijn_subst subst2)) ts =
    MAP (infer_deBruijn_subst(MAP(infer_deBruijn_subst subst1) subst2)) ts)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_alt]>>
  simp[EL_MAP]>>
  fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f]
QED

Theorem check_t_subst:
 !tvs (tvs':num set) t s.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))
Proof
ho_match_mp_tac check_t_ind >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw []
QED

Theorem t_vwalk_check:
 !s. t_wfs s ⇒
  !n tvs uvs t.
    n ∈ uvs ∧
    check_s tvs uvs s
    ⇒
    check_t tvs uvs (t_vwalk s n)
Proof
NTAC 2 STRIP_TAC >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
pop_assum ho_match_mp_tac >>
rw [] >>
rw [Once t_vwalk_eqn] >>
cases_on `FLOOKUP s n` >>
rw [check_t_def] >>
cases_on `x` >>
rw [check_t_def] >>
fs [check_s_def, FLOOKUP_DEF] >>
metis_tac [check_t_def, IN_UNION]
QED

Theorem t_walkstar_check'[local]:
  !s. t_wfs s ⇒
  !t tvs uvs.
    check_s tvs (uvs ∪ FDOM s) s ∧
    check_t tvs (uvs ∪ FDOM s) t
    ⇒
    check_t tvs uvs (t_walkstar s t)
Proof
  NTAC 2 STRIP_TAC >>
  imp_res_tac t_walkstar_ind >>
  pop_assum ho_match_mp_tac >>
  rw [] >>
  rw [t_walkstar_eqn] >>
  cases_on `t` >>
  fs [check_t_def] >>
  rw [t_walk_eqn] >>
  rw [check_t_def, EVERY_MAP]
  >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [t_walk_eqn])
  >- (
    fs [t_walk_eqn] >>
    `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)`
            by metis_tac [t_vwalk_check,  IN_UNION] >>
    cases_on `t_vwalk s n` >>
    fs [check_t_def, EVERY_MAP] >>
    fs [EVERY_MEM] >>
    metis_tac [t_vwalk_to_var])
  >>
    fs [t_walk_eqn] >>
    `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)` by
      metis_tac [t_vwalk_check,  IN_UNION] >>
    cases_on `t_vwalk s n` >>
    fs [check_t_def, EVERY_MAP] >>
    fs [EVERY_MEM] >>
    metis_tac [t_vwalk_to_var]
QED

Theorem t_walkstar_check:
 !s t tvs uvs.
    t_wfs s ∧
    check_s tvs (uvs ∪ FDOM s) s ∧
    check_t tvs (uvs ∪ FDOM s) t
    ⇒
    check_t tvs uvs (t_walkstar s t)
Proof
metis_tac [t_walkstar_check']
QED

Theorem t_walkstar_uncheck_lem[local]:
  !s. t_wfs s ⇒
    ∀t max_tvs uvs.
    check_t max_tvs uvs (t_walkstar s t) ⇒
    check_t max_tvs (uvs ∪ FDOM s) t
Proof
  ntac 2 strip_tac
 >> old_drule t_walkstar_ind
 >> fs [GSYM PULL_FORALL]
 >> disch_then ho_match_mp_tac
 >> rw []
 >> Cases_on `t`
 >> rfs [check_t_def, t_walkstar_eqn, t_walk_eqn, EVERY_MAP, EVERY_MEM]
 >> pop_assum mp_tac
 >> old_drule t_vwalk_eqn
 >> strip_tac
 >> ONCE_ASM_REWRITE_TAC []
 >> pop_assum kall_tac
 >> every_case_tac
 >> simp [check_t_def]
 >> fs [check_s_def, FLOOKUP_DEF]
QED

Theorem t_walkstar_uncheck:
   !s t max_tvs uvs.
    check_t max_tvs uvs (t_walkstar s t) ∧
    t_wfs s ⇒
    check_t max_tvs (uvs ∪ FDOM s) t
Proof
 metis_tac [t_walkstar_uncheck_lem]
QED

Theorem t_unify_check_s_help[local]:
  (!s t1 t2. t_wfs s ⇒
    !tvs uvs s'. check_s tvs uvs s ∧
           check_t tvs uvs t1 ∧
           check_t tvs uvs t2 ∧
           (t_unify s t1 t2 = SOME s')
           ⇒
           check_s tvs uvs s') ∧
 (!s ts1 ts2. t_wfs s ⇒
    !tvs uvs s'. check_s tvs uvs s ∧
           EVERY (check_t tvs uvs) ts1 ∧
           EVERY (check_t tvs uvs) ts2 ∧
           (ts_unify s ts1 ts2 = SOME s')
           ⇒
           check_s tvs uvs s')
Proof
  ho_match_mp_tac t_unify_strongind >>
  rw []
  >- (
    qpat_x_assum `t_unify s t1 t2 = SOME s'` mp_tac >>
    rw [t_unify_eqn] >>
    (* Only the last case is interesting *)
    reverse(
      cases_on `t1` >>
      cases_on `t2`) >>
    fs [t_walk_eqn, t_ext_s_check_eqn, check_t_def]
    >- (
      old_drule t_vwalk_check >>
      disch_then imp_res_tac>>
      fs[infer_tTheory.infer_t_case_eq]>>
      rveq>>rfs[check_t_def]>>
      TRY (fs [check_s_def] >>
           rw [check_t_def, FAPPLY_FUPDATE_THM] >>
           rw [check_t_def] >>
           NO_TAC) >>
      metis_tac [])
   >>
     old_drule t_vwalk_check>>
     rpt(disch_then old_drule)>>
     fs[infer_tTheory.infer_t_case_eq,check_s_def]>>
     rw[check_t_def]>>
     rw [check_t_def, FAPPLY_FUPDATE_THM]>>
     metis_tac[])>>
   pop_assum mp_tac >>
   cases_on `ts1` >>
   cases_on `ts2` >>
   fs [ts_unify_def] >>
   rw [] >- metis_tac [] >>
   cases_on `t_unify s h h'` >>
   fs []
QED

Theorem check_t_walkstar:
 (!t tvs s.
    t_wfs s ∧
    check_t tvs (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    check_t tvs {} (t_walkstar s t)) ∧
 (!ts tvs s.
    t_wfs s ∧
    EVERY (check_t tvs (FDOM s)) ts ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    EVERY (check_t tvs {} o t_walkstar s) ts)
Proof
  ho_match_mp_tac infer_t_induction >>
  rw [check_t_def, t_walkstar_eqn1, EVERY_MAP] >>
  metis_tac []
QED

Theorem t_walkstar_no_vars[local]:
  !tvs uvs t s.
  t_wfs s ∧
  uvs = {} ∧
  check_t tvs uvs t
  ⇒
  t_walkstar s t = t
Proof
  ho_match_mp_tac check_t_ind >>
  srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
  fs [t_walkstar_eqn1] >>
  induct_on `ts` >>
  rw [] >>
  metis_tac []
QED

Theorem t_walkstar_no_vars:
 !tvs t s.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  t_walkstar s t = t
Proof
  metis_tac [t_walkstar_no_vars]
QED

Theorem t_unify_check_s:
 !s1 tvs uvs t1 t2 s2.
  t_unify s1 t1 t2 = SOME s2 ∧
  t_wfs s1 ∧
  check_s tvs uvs s1 ∧
  check_t tvs uvs t1 ∧
  check_t tvs uvs t2
  ⇒
  check_s tvs uvs s2
Proof
  metis_tac [t_unify_check_s_help]
QED

Theorem pure_add_constraints_check_s:
 !s1 tvs uvs ts s2.
  pure_add_constraints s1 ts s2 ∧
  t_wfs s1 ∧
  EVERY (\(t1,t2). check_t tvs (count uvs) t1 ∧ check_t tvs (count uvs) t2) ts ∧
  check_s tvs (count uvs) s1
  ⇒
  check_s tvs (count uvs) s2
Proof
  induct_on `ts` >-
  (rw [check_s_def, pure_add_constraints_def] >-
   metis_tac []) >>
  rw [pure_add_constraints_def] >>
  PairCases_on `h` >>
  fs [pure_add_constraints_def] >>
  metis_tac [t_unify_wfs, t_unify_check_s]
QED

Theorem infer_p_check_t:
 (!l cenv p st t env st'.
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    check_t 0 (count st'.next_uvar) t) ∧
 (!l cenv ps st ts env st'.
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    EVERY (check_t 0 (count st'.next_uvar)) ts)
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [infer_p_def, success_eqns, remove_pair_lem] >>
  rw [check_t_def]
  >- (PairCases_on `v'` >>
      fs [remove_pair_lem, EVERY_MEM] >>
      rw [] >>
      metis_tac [check_t_more3])
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- (PairCases_on `v''` >>
      fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
      rw [check_t_def] >>
      `?n. st'.next_uvar = st'''.next_uvar + n`
                  by (imp_res_tac infer_p_next_uvar_mono >>
                      qexists_tac `st'.next_uvar - st'''.next_uvar` >>
                      srw_tac [ARITH_ss] []) >>
      metis_tac [check_t_more3])
  >- (PairCases_on `v''` >>
      fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
      rw [check_t_def] >>
      decide_tac)
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- (* Pas case *)
    (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- (* Pas case *)
    (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- (* Pas case *)
    (PairCases_on `v'` >>
      fs [] >>
      metis_tac [])
  >- metis_tac [type_name_check_subst_state]
  >- metis_tac [type_name_check_subst_state]
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      fs [] >>
      metis_tac [infer_p_wfs])
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      fs [remove_pair_lem, EVERY_MEM] >>
      rw [] >>
      `?n. st'.next_uvar = st''.next_uvar + n`
                  by (imp_res_tac infer_p_next_uvar_mono >>
                      qexists_tac `st'.next_uvar - st''.next_uvar` >>
                      srw_tac [ARITH_ss] []) >>
      metis_tac [check_t_more3])
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      fs [] >>
      `?n. st'.next_uvar = st''.next_uvar + n`
                  by (imp_res_tac infer_p_next_uvar_mono >>
                      qexists_tac `st'.next_uvar - st''.next_uvar` >>
                      srw_tac [ARITH_ss] []) >>
      metis_tac [check_t_more3])
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      fs [] >>
      `?n. st'.next_uvar = st''.next_uvar + n`
                  by (imp_res_tac infer_p_next_uvar_mono >>
                      qexists_tac `st'.next_uvar - st''.next_uvar` >>
                      srw_tac [ARITH_ss] []) >>
      metis_tac [infer_p_wfs, check_t_more3])
QED

Theorem check_infer_type_subst[local]:
  (!t tvs uvs.
  check_freevars 0 tvs t
  ⇒
  check_t 0 (count (LENGTH tvs + uvs)) (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs)))) t)) ∧
 (!ts tvs uvs.
  EVERY (check_freevars 0 tvs) ts
  ⇒
  EVERY (\t. check_t 0 (count (LENGTH tvs + uvs)) (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs)))) t)) ts)
Proof
  ho_match_mp_tac t_induction >>
  rw [check_freevars_def, check_t_def, infer_type_subst_alt]
  >- (
    pop_assum mp_tac >>
    Q.SPEC_TAC (`uvs`, `uvs`) >>
    induct_on `tvs` >>
    rw [COUNT_LIST_def, check_t_def] >>
    qpat_x_assum `!uvs. P uvs` (mp_tac o Q.SPEC `SUC uvs`) >>
    rw [MAP_MAP_o, combinTheory.o_DEF] >>
    qmatch_asmsub_abbrev_tac`MAP f1 _` >>
    qmatch_goalsub_abbrev_tac`MAP f2 _` >>
    `f1 = f2` by (unabbrev_all_tac \\ simp[FUN_EQ_THM]) >>
    fs[ADD1])
  >> metis_tac [EVERY_MAP]
QED

(* moved this one around a bit *)
Theorem infer_type_subst_empty_check:
  (∀t.
  check_freevars 0 [] t ⇒
  check_t 0 {} (infer_type_subst [] t)) ∧
∀ts.
EVERY (check_freevars 0 []) ts ⇒
EVERY (check_t 0 {}) (MAP (infer_type_subst []) ts)
Proof
  Induct>>fs[check_freevars_def,infer_type_subst_alt,check_t_def]>>
  metis_tac[]
QED

Theorem type_name_check_subst_thm:
  (!t l err tenvT fvs (st:'a) r st'.
    type_name_check_subst l err tenvT fvs t st = (Success r,st') ⇒
    check_freevars_ast fvs t ∧ check_type_names tenvT t ∧
    r = type_name_subst tenvT t) ∧
  (!ts l err tenvT fvs (st:'a) rs st'.
    type_name_check_subst_list l err tenvT fvs ts st = (Success rs,st') ⇒
    EVERY (check_freevars_ast fvs) ts ∧ EVERY (check_type_names tenvT) ts ∧
    rs = MAP (type_name_subst tenvT) ts)
Proof
  Induct >>
  rw [check_type_names_def, type_name_check_subst_def, check_freevars_def,
      type_name_subst_def, success_eqns] >>
  rw [check_freevars_ast_def] >>
  TRY pairarg_tac >>
  fs [success_eqns] >>
  rw [] >>
  metis_tac []
QED

Theorem type_name_check_subst_comp_thm:
  (!t l err tenvT fvs (st:'a) r.
    check_freevars_ast fvs t ∧ check_type_names tenvT t
    ⇒
    type_name_check_subst l err tenvT fvs t st =
      (Success (type_name_subst tenvT t), st)) ∧
  (!ts l err tenvT fvs (st:'a) rs st'.
    EVERY (check_freevars_ast fvs) ts ∧ EVERY (check_type_names tenvT) ts
    ⇒
    type_name_check_subst_list l err tenvT fvs ts st =
      (Success (MAP (type_name_subst tenvT) ts),st))
Proof
  Induct >>
  rw [check_type_names_def, type_name_check_subst_def, check_freevars_def,
      type_name_subst_def, success_eqns] >>
  fs [check_freevars_ast_def] >>
  TRY pairarg_tac >>
  fs [success_eqns]
QED

Theorem infer_p_check_s:
 (!l ienv p st t env st' tvs.
  infer_p l ienv p st = (Success (t,env), st') ∧
  t_wfs st.subst ∧
  tenv_ctor_ok ienv.inf_c ∧
  tenv_abbrev_ok ienv.inf_t ∧
  check_s tvs (count st.next_uvar) st.subst
  ⇒
  check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!l ienv ps st ts env st' tvs.
  infer_ps l ienv ps st = (Success (ts,env), st') ∧
  t_wfs st.subst ∧
  tenv_ctor_ok ienv.inf_c ∧
  tenv_abbrev_ok ienv.inf_t ∧
  check_s tvs (count st.next_uvar) st.subst
  ⇒
  check_s tvs (count st'.next_uvar) st'.subst)
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [infer_p_def, success_eqns, remove_pair_lem] >>
  rw []
  >- metis_tac [check_s_more]
  >- metis_tac [check_s_more]
  >- (PairCases_on `v'` >>
      metis_tac [check_s_more2, infer_p_next_uvar_mono])
  >- (rename1 `infer_ps _ _ _ _ = (Success v1, st1)` >>
      PairCases_on `v1` >>
      fs [] >>
      first_x_assum old_drule >>
      rpt (disch_then old_drule) >>
      old_drule (CONJUNCT2 infer_p_wfs) >>
      rpt (disch_then old_drule) >>
      rw []>>
      `st1.next_uvar ≤ st1.next_uvar + LENGTH (FST v')` by decide_tac >>
      `check_s tvs (count st'.next_uvar) st1.subst` by metis_tac [check_s_more2,ADD_COMM] >>
      match_mp_tac pure_add_constraints_check_s >>
      qexists_tac `st1.subst` >>
      qexists_tac `(ZIP (v10, MAP (infer_type_subst (ZIP (FST v', MAP (λn.  Infer_Tuvar (st1.next_uvar + n)) (COUNT_LIST (LENGTH (FST v')))))) (FST (SND v'))))` >>
      rw [] >>
      rw [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
      metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_p_next_uvar_mono,
                 arithmeticTheory.LESS_EQ_TRANS, infer_p_check_t, ADD_COMM] >>
      PairCases_on `v'` >>
      fs [] >>
      imp_res_tac tenv_ctor_ok_lookup >>
      imp_res_tac check_infer_type_subst >>
      rw [] >>
      fs [EVERY_MEM] >>
      metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM])
  >- (PairCases_on `v'` >>
      metis_tac [check_s_more2, infer_p_next_uvar_mono])
  >- ( (* Pas case *) PairCases_on `v'` >>
      metis_tac [check_s_more2, infer_p_next_uvar_mono])
  >- (
    irule t_unify_check_s >>
    qexists_tac `st''.subst` >>
    qexists_tac `t'` >>
    qexists_tac `(infer_type_subst []  (type_name_subst ienv.inf_t t))` >>
    rw [] >>
    fs []
    >- metis_tac [infer_p_wfs]
    >- metis_tac [t_unify_check_s]
    >- metis_tac [check_t_more2, arithmeticTheory.ADD_0, infer_p_check_t, ADD_COMM]
    >- metis_tac [infer_type_subst_empty_check, check_freevars_type_name_subst,
                  check_t_more2, arithmeticTheory.ADD_0, infer_p_check_t, ADD_COMM,
                  check_t_more, type_name_check_subst_thm])
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      metis_tac [infer_p_wfs, check_s_more2, infer_p_next_uvar_mono])
QED

Theorem check_env_more:
 !uvs e.
  nsAll (λx (tvs,t). check_t tvs (count uvs) t) e
  ⇒
  !uvs'. uvs ≤ uvs' ⇒ nsAll (λx (tvs,t). check_t tvs (count uvs') t) e
Proof
 rw []
 >> irule nsAll_mono
 >> qexists_tac `(λx (tvs,t). check_t tvs (count uvs) t)`
 >> rw []
 >> pairarg_tac
 >> fs []
 >> metis_tac [check_t_more4]
QED

Theorem check_env_letrec_lem:
 ∀uvs funs uvs'.
  ((funs = []) ∨ (uvs' + LENGTH funs ≤ uvs))
  ⇒
  nsAll (λx (tvs,t). check_t tvs (count uvs) t)
    (alist_to_ns (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (n+uvs')) (COUNT_LIST (LENGTH funs)))))
Proof
 rw [COUNT_LIST_def]
 >> rw [COUNT_LIST_def]
 >> irule nsAll_alist_to_ns
 >> Induct_on `funs`
 >> rw [COUNT_LIST_def]
 >> rpt (pairarg_tac >> fs [])
 >> rw [check_t_def]
 >> fs [MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM]
 >> rw []
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [MAP2_MAP, LENGTH_COUNT_LIST, MEM_MAP, MEM_ZIP]
 >> rw []
 >> fs []
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [EL_MAP, LENGTH_COUNT_LIST, check_t_def, EL_COUNT_LIST]
QED

Theorem check_t_infer_db_subst[local]:
  (!t uvs tvs.
   check_t 0 (count (uvs + tvs)) (infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs)) t)
   =
   check_t tvs (count (uvs + tvs)) t) ∧
 (!ts uvs tvs.
   EVERY (check_t 0 (count (uvs + tvs)) o infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs))) ts
   =
   EVERY (check_t tvs (count (uvs + tvs))) ts)
Proof
  ho_match_mp_tac infer_t_induction >>
rw [check_t_def, infer_deBruijn_subst_alt, LENGTH_COUNT_LIST,
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >>
metis_tac []
QED

Theorem check_t_infer_db_subst2:
 (!t tvs1 tvs2.
   check_t tvs1  (count tvs2) (infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2)) t)
   =
   check_t (tvs1 + tvs2) (count tvs2) t) ∧
 (!ts tvs1 tvs2.
   EVERY (check_t tvs1 (count tvs2) o infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2))) ts
   =
   EVERY (check_t (tvs1 + tvs2) (count tvs2)) ts)
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, infer_deBruijn_subst_alt, LENGTH_COUNT_LIST,
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >-
metis_tac []
QED

Theorem infer_e_check_t:
  (∀l ienv e st st' t.
     infer_e l ienv e st = (Success t, st') ∧
     ienv_val_ok (count st.next_uvar) ienv.inf_v
     ⇒
    check_t 0 (count st'.next_uvar) t) ∧
  (∀l ienv es st st' ts.
     infer_es l ienv es st = (Success ts, st') ∧
     ienv_val_ok (count st.next_uvar) ienv.inf_v
     ⇒
     EVERY (check_t 0 (count st'.next_uvar)) ts) ∧
  (∀l ienv pes t1 t2 st st'.
     infer_pes l ienv pes t1 t2 st = (Success (), st') ∧
    ienv_val_ok (count st.next_uvar) ienv.inf_v
     ⇒
     T) ∧
  (∀l ienv funs st st' ts'.
     infer_funs l ienv funs st = (Success ts', st') ∧
     ienv_val_ok (count st.next_uvar) ienv.inf_v
     ⇒
     EVERY (check_t 0 (count st'.next_uvar)) ts')
Proof
 ho_match_mp_tac infer_e_ind >>
 srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, LET_THM] >>
 fsrw_tac[] [check_t_def] >>
 imp_res_tac infer_e_next_uvar_mono >>
 fsrw_tac[] [EVERY_MAP, check_t_def, check_t_infer_db_subst]
 >- metis_tac [check_t_more4]
 >- (fs [ienv_val_ok_def] >>
     imp_res_tac nsLookup_nsAll >>
     pairarg_tac >>
     fs [] >>
     pairarg_tac >>
     fs [] >>
     srw_tac[] [] >>
     metis_tac [check_t_more3, ADD_COMM])
 >- metis_tac [check_t_more4]
 >- (rw [EVERY_MEM, MEM_COUNT_LIST] >>
     decide_tac)
 >- (srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def, ienv_val_ok_def] >>
     first_x_assum irule >>
     irule nsAll_nsBind >>
     simp [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``])
 >- (every_case_tac >>
     fs [success_eqns] >>
     rw [] >>
     fs [infer_st_rewrs, EVERY_MAP, check_t_def, check_t_infer_db_subst] >>
     res_tac >>
     fs [count_def,ienv_val_ok_def])
 >- (res_tac >>
     fs [check_t_def] >>
     pop_assum match_mp_tac  >>
     rw [opt_bind_def] >>
     every_case_tac >>
     fs [ienv_val_ok_def] >>
     irule nsAll_nsOptBind
     >> simp [option_nchotomy]
     >> metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``])
 >- ( first_x_assum drule \\ rw[] )
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> simp []
   >> fs [ienv_val_ok_def]
   >> metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4])
 >- decide_tac
 >- (res_tac >>
     fs [check_t_def] >>
     pop_assum match_mp_tac  >>
     rw [opt_bind_def] >>
     every_case_tac >>
     fs [ienv_val_ok_def] >>
     irule nsAll_nsOptBind
     >> simp [option_nchotomy]
     >> metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> simp []
   >> fs [ienv_val_ok_def]
   >> rw []
   >> first_x_assum irule
   >> irule nsAll_nsAppend
   >> simp []
   >> conj_tac >- (
     irule check_env_letrec_lem
     >> simp [])
   >> irule check_env_more
   >> `st.next_uvar ≤ st''''.next_uvar` by decide_tac
   >> metis_tac [check_env_more, check_t_more4])
 >- (imp_res_tac type_name_check_subst_thm >>
     imp_res_tac type_name_check_subst_state >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4,
                type_name_check_subst_state])
 >- (res_tac >>
     fs [ienv_val_ok_def] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4])
 >- (reverse (srw_tac [ARITH_ss] []) >>
     res_tac >>
     fs [check_t_def, ienv_val_ok_def]
     >- metis_tac [check_env_more, check_t_more4, DECIDE ``x ≤ x + 1:num``]
     >> `check_t 0 (count st'''.next_uvar) t` suffices_by metis_tac [check_t_more4]
     >> first_x_assum irule
     >> irule nsAll_nsBind
     >> simp [check_t_def]
     >> metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``])
QED

val check_t_more_0 =
  check_t_more2 |> CONJUNCT1 |> Q.SPECL[`t`,`0`] |> SIMP_RULE(srw_ss())[]

val check_t_more_1 =
  check_t_more3 |> CONJUNCT1 |> SPEC_ALL |> SIMP_RULE(srw_ss())[PULL_FORALL] |> Q.SPEC`1`

Theorem constrain_op_wfs:
   !l tvs op ts t st st'.
    constrain_op l op ts st = (Success t, st') ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst
Proof
  rw [constrain_op_success, success_eqns] >>
  fs [] >>
  TRY (rename [‘supported_arith a p’] >>
       rpt (pairarg_tac >> gvs [AllCaseEqs(),failwith_def]) >>
       gvs [st_ex_bind_def,AllCaseEqs(),st_ex_return_def] >>
       imp_res_tac pure_add_constraints_wfs) >>
  every_case_tac >>
  TRY (Cases_on `f`) >>
  fs [op_to_string_def, success_eqns] >>
  rw [] >>
  fs [infer_st_rewrs, add_constraints_def, success_eqns] >>
  rw [] >>
  metis_tac [t_unify_wfs]
QED

Theorem constrain_op_check_t:
   !l tvs op ts t st st'.
    constrain_op l op ts st = (Success t, st') ∧
    EVERY (check_t 0 (count st.next_uvar)) ts
    ⇒
    check_t 0 (count st'.next_uvar) t
Proof
  rw [constrain_op_success, success_eqns] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs(),st_ex_bind_def,st_ex_return_def]) >>
  every_case_tac >>
  TRY (Cases_on `f`) >>
  fs [op_to_string_def, success_eqns] >>
  rw [] >>
  fs [infer_st_rewrs, check_t_def]
QED

Theorem constrain_op_check_s:
   !l tvs op ts t st st'.
    constrain_op l op ts st = (Success t, st') ∧
    t_wfs st.subst ∧
    EVERY (check_t 0 (count st.next_uvar)) ts ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst
Proof
   rw [] >>
   `!uvs tvs tc. check_t tvs uvs (Infer_Tapp [] tc)` by rw [check_t_def] >>
   fs [constrain_op_success] >> rw [] >>
   rpt (pairarg_tac \\ gvs [AllCaseEqs(),st_ex_bind_def,st_ex_return_def,failwith_def]) >>
   fs [op_to_string_def, infer_st_rewrs]
   >~ [‘supported_arith a p’]
   >- (Cases_on‘p’ >> gvs[supported_arith_def] >>
       TRY (Cases_on‘a:arith’) >>
       gvs [supported_arith_def,LENGTH_EQ_NUM_compute,REPLICATE_compute,
            add_constraints_def, st_ex_bind_success, add_constraint_def,
            CaseEq"prod", CaseEq"option", st_ex_return_success] >>
       imp_res_tac t_unify_wfs >>
       match_mp_tac t_unify_check_s >> asm_exists_tac >> rw[] >>
       TRY(match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[]) >>
       TRY(match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
       \\ TRY(match_mp_tac check_t_more_0 \\ rw[]))
   >~ [‘supported_conversion p p0’]
   >- (Cases_on`p` \\ Cases_on`p0` >> gvs [supported_conversion_def] >>
       match_mp_tac t_unify_check_s >> asm_exists_tac >>
       imp_res_tac t_unify_wfs >> rw[] >>
       match_mp_tac check_t_more_0 \\ rw[])
   >~ [‘supported_test t0 p0’]
   >- (Cases_on`t0` >> gvs [supported_test_def] >>
       imp_res_tac t_unify_wfs >>
       match_mp_tac t_unify_check_s >> asm_exists_tac >> rw[] >>
       TRY(match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[]) >>
       match_mp_tac check_t_more_0 \\ rw[])
   \\ TRY (Cases_on `uop`)
   \\ TRY pairarg_tac >> fs [success_eqns]
   \\ imp_res_tac t_unify_wfs \\ rfs[fresh_uvar_success]
   \\ TRY (match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
   \\ TRY (match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
   \\ TRY (match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
   \\ TRY (match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
   \\ TRY (match_mp_tac t_unify_check_s \\ asm_exists_tac \\ rw[])
   \\ TRY (match_mp_tac check_s_more \\ rw[])
   \\ TRY (CHANGED_TAC(rw[check_t_def]))
   \\ TRY (match_mp_tac check_t_more_1 \\ rw[])
   \\ match_mp_tac check_t_more_0 \\ simp[] \\ NO_TAC
QED

Definition ienv_ok_def:
  ienv_ok uvars ienv ⇔
    ienv_val_ok uvars ienv.inf_v ∧
    tenv_ctor_ok ienv.inf_c ∧
    tenv_abbrev_ok ienv.inf_t
End

Theorem ienv_ok_more:
   !uv uv' ienv. ienv_ok (count uv) ienv ∧ uv ≤ uv' ⇒ ienv_ok (count uv') ienv
Proof
 rw [ienv_ok_def, ienv_val_ok_def]
 >> metis_tac [check_env_more]
QED

Theorem infer_e_check_s:
 (!l ienv e st st' t tvs.
    infer_e l ienv e st = (Success t, st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!l ienv es st st' ts tvs.
    infer_es l ienv es st = (Success ts, st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!l ienv pes t1 t2 st st' tvs.
    infer_pes l ienv pes t1 t2 st = (Success (), st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_t 0 (count st.next_uvar) t1 ∧
    check_t 0 (count st.next_uvar) t2 ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!l ienv funs st st' ts' tvs.
    infer_funs l ienv funs st = (Success ts', st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst)
Proof
 ho_match_mp_tac infer_e_ind
 >> rw [infer_e_def, success_eqns]
 >> rw []
 >- (
   old_drule (CONJUNCT1 infer_e_wfs)
   >> rw []
   >> irule check_s_more
   >> irule t_unify_check_s
   >> asm_exists_tac >> simp[]
   >> asm_exists_tac >> simp[]
   >> rw [check_t_def]
   >> metis_tac [ienv_ok_def, infer_e_check_t, arithmeticTheory.ADD_0, check_t_more2])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> simp []
   >> rw []
   >> first_x_assum irule
   >> simp [check_t_def]
   >> conj_tac >- metis_tac [infer_e_wfs]
   >> conj_tac >- metis_tac [ienv_ok_more, infer_e_next_uvar_mono]
   >- metis_tac [check_t_more4, infer_e_next_uvar_mono, infer_e_check_t, ienv_ok_def])
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rw []
   >> metis_tac [check_s_more2, DECIDE ``x ≤ (y:num) + x``])
 >- metis_tac [check_s_more2, DECIDE ``x ≤ x + y:num``]
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rw []
   >> first_x_assum old_drule
   >> simp []
   >> disch_then old_drule
   >> rw []
   >> old_drule pure_add_constraints_check_s
   >> simp []
   >> disch_then irule
   >> simp []
   >> conj_tac >- metis_tac [infer_e_wfs]
   >> conj_tac >- (
     old_drule (List.nth (CONJUNCTS infer_e_check_t, 1))
     >> rfs [ienv_ok_def]
     >> fs [EVERY_MEM]
     >> rw []
     >> rfs [MEM_ZIP, LENGTH_COUNT_LIST, EL_MAP]
     >> rw []
     >> fs [MEM_EL, PULL_EXISTS]
     >> rfs []
     >> qpat_x_assum `_ + _ = (_:num)` (assume_tac o GSYM)
     >- (
       first_x_assum old_drule
       >> rw []
       >> fs []
       >> old_drule (CONJUNCT1 check_t_more2)
       >> fs []
       >> metis_tac [check_t_more4, DECIDE ``x ≤ y+x:num``])
     >- (
       old_drule tenv_ctor_ok_lookup
       >> disch_then old_drule
       >> rw [EVERY_MEM, MEM_EL, PULL_EXISTS]
       >> first_x_assum old_drule
       >> rw []
       >> old_drule (CONJUNCT1 check_infer_type_subst)
       >> disch_then (qspec_then `st''.next_uvar` mp_tac)
       >> rw []
       >> old_drule (CONJUNCT1 check_t_more2)
       >> rw []))
   >- (
     `st''.next_uvar ≤ st'.next_uvar` by simp []
     >> metis_tac [check_s_more2]))
 >- (
   first_x_assum old_drule
   >> simp []
   >> disch_then irule
   >> conj_tac >- (
     fs [ienv_ok_def, ienv_val_ok_def]
     >> irule nsAll_nsBind
     >> simp [check_t_def]
     >> irule check_env_more
     >> HINT_EXISTS_TAC
     >> simp [])
   >> metis_tac [check_s_more])
 >- (
   old_drule (List.nth (CONJUNCTS infer_e_wfs, 1))
   >> rw []
   >> old_drule constrain_op_check_s
   >> disch_then irule
   >> simp []
   >> metis_tac [infer_e_check_t, ienv_ok_def])
 >- (
   gvs []
   >> first_x_assum old_drule
   >> rw []
   >> first_x_assum old_drule
   >> rw []
   >> old_drule t_unify_check_s
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> old_drule t_unify_check_s
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> qpat_x_assum `infer_e _ _ _ _ = _` mp_tac
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> rw [check_t_def]
   >> first_x_assum irule
   >> conj_tac >- metis_tac [t_unify_wfs]
   >> conj_tac >- (
     first_x_assum irule
     >> conj_tac >- (
       first_x_assum irule
       >> rw []
       >> metis_tac [ienv_ok_more, ienv_ok_def])
     >> metis_tac [check_t_more4, check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])
   >> metis_tac [ienv_ok_more, ienv_ok_def, check_t_more4, check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])
 >- (
   first_x_assum old_drule
   >> rw []
   >> first_x_assum old_drule
   >> rw []
   >> first_x_assum old_drule
   >> rw []
   >> old_drule t_unify_check_s
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> old_drule t_unify_check_s
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> qpat_x_assum `infer_e _ _ _ _ = _` mp_tac
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> qpat_x_assum `infer_e _ _ _ _ = _` mp_tac
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> rw [check_t_def]
   >> first_x_assum irule
   >> conj_tac >- metis_tac [t_unify_wfs]
   >> conj_tac >- (
     first_x_assum irule
     >> simp []
     >> conj_tac >- metis_tac [t_unify_wfs]
     >> conj_tac >- metis_tac [ienv_ok_more, ienv_ok_def]
     >- (
       first_x_assum irule
       >> rw []
       >- metis_tac [t_unify_wfs]
       >- metis_tac [ienv_ok_more, ienv_ok_def]
       >- (
         first_x_assum irule
         >> simp []
         >> metis_tac [check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])))
   >> metis_tac [ienv_ok_more, ienv_ok_def, check_t_more4, check_t_more2,
                 DECIDE ``0n ≤ x ∧ y + 0n = y``])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> rw [check_t_def]
   >> first_x_assum irule
   >> rw []
   >- metis_tac [infer_e_wfs]
   >- metis_tac [infer_e_next_uvar_mono, ienv_ok_more, DECIDE ``x ≤ x+1n``]
   >- metis_tac [check_s_more]
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> metis_tac [check_t_more3])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> rw [check_t_def]
   >> first_x_assum irule
   >> rw []
   >- metis_tac [infer_e_wfs]
   >> old_drule ienv_ok_more
   >> disch_then (qspec_then `st''.next_uvar` mp_tac)
   >> rw []
   >> fs [ienv_ok_def, ienv_val_ok_def]
   >> irule nsAll_nsOptBind
   >> rw []
   >> metis_tac [infer_e_check_t, ienv_val_ok_def, infer_e_next_uvar_mono,
                 option_nchotomy, infer_e_wfs])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e _ (ienv with inf_v := nsAppend bindings ienv.inf_v) _ _ = _`
   >> `ienv_ok (count (LENGTH funs + st.next_uvar)) (ienv with inf_v := nsAppend bindings ienv.inf_v)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsAppend
       >> rw []
       >- (
         irule check_env_letrec_lem
         >> disj2_tac
         >> decide_tac)
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more4, DECIDE ``y ≤ x+y:num``])
   >> rw []
   >> first_x_assum irule
   >> rw []
   >- (
     old_drule (List.nth (CONJUNCTS infer_e_wfs, 3))
     >> simp []
     >> metis_tac [pure_add_constraints_wfs])
   >- (
     irule ienv_ok_more
     >> HINT_EXISTS_TAC
     >> rw []
     >> old_drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
     >> rw [])
   >> old_drule pure_add_constraints_check_s
   >> disch_then irule
   >> conj_tac >- (
     old_drule (List.nth (CONJUNCTS infer_e_wfs, 3))
     >> rw [])
   >> conj_tac >- (
     fs [EVERY_MEM, LENGTH_COUNT_LIST, LENGTH_MAP, MEM_ZIP]
     >> rw []
     >> rw [EL_MAP, LENGTH_COUNT_LIST, check_t_def]
     >> old_drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
     >> rw [EL_COUNT_LIST]
     >> old_drule (List.nth (CONJUNCTS infer_e_check_t, 3))
     >> rfs [ienv_ok_def]
     >> rw [EVERY_MEM, MEM_EL, PULL_EXISTS]
     >> metis_tac [check_t_more2, DECIDE ``x+0n = x``, MEM_EL])
   >> first_x_assum irule
   >> rw []
   >> metis_tac [check_s_more2, DECIDE ``x ≤ y+x:num``])
 >- (
   imp_res_tac type_name_check_subst_state >>
   imp_res_tac type_name_check_subst_thm >>
   fs [] >>
   old_drule (CONJUNCT1 infer_e_wfs)
   >> first_x_assum old_drule
   >> rw []
   >> old_drule t_unify_check_s
   >> simp []
   >> disch_then irule
   >> simp []
   >> conj_tac >- (
     old_drule (CONJUNCT1 infer_e_check_t)
     >> fs [ienv_ok_def]
     >> metis_tac [check_t_more2, DECIDE ``y + 0n = y``])
   >> fs [ienv_ok_def]
   >> imp_res_tac check_freevars_type_name_subst
   >> pop_assum (qspec_then`0n` assume_tac)
   >> old_drule (CONJUNCT1 infer_type_subst_empty_check)
   >> rw []
   >> metis_tac [COUNT_ZERO, check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y ∧ 0n ≤ y``])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> rw []
   >> first_x_assum irule
   >> metis_tac [infer_e_wfs, ienv_ok_more, infer_e_next_uvar_mono])
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rename1 `infer_p _ _ _ _ = (Success (t1',bindings1),st1)`
   >> old_drule (REWRITE_RULE [Once CONJ_SYM] (CONJUNCT1 infer_p_wfs))
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_check_t)
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_p_check_s)
   >> `tenv_ctor_ok ienv.inf_c ∧ tenv_abbrev_ok ienv.inf_t` by fs [ienv_ok_def]
   >> simp []
   >> disch_then old_drule
   >> rw []
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> rename1 `t_unify _ t1 t1' = SOME s1`
   >> old_drule (REWRITE_RULE [Once CONJ_SYM] t_unify_wfs)
   >> old_drule t_unify_check_s
   >> rpt (disch_then old_drule)
   >> `check_t tvs (count st1.next_uvar) t1 ∧ check_t tvs (count st1.next_uvar) t1'`
     by metis_tac [check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y``]
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e _ (ienv with inf_v := nsAppend bindings2 ienv.inf_v) _ _ = (Success t2', st2)`
   >> `ienv_val_ok (count st1.next_uvar) (nsAppend bindings2 ienv.inf_v)`
     by (
       fs [ienv_ok_def, ienv_val_ok_def, Abbr `bindings2`]
       >> irule nsAll_nsAppend
       >> conj_tac >- (
         irule nsAll_alist_to_ns
         >> fs [EVERY_MAP, EVERY_MEM]
         >> rw []
         >> rpt (pairarg_tac >> fs [])
         >> rw []
         >> first_x_assum old_drule
         >> rw [])
       >- (
         irule nsAll_mono
         >> HINT_EXISTS_TAC
         >> rw []
         >> rpt (pairarg_tac >> fs [])
         >> metis_tac [check_t_more4]))
   >> old_drule (CONJUNCT1 infer_e_check_t)
   >> simp []
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> simp [ienv_ok_def]
   >> rw []
   >> rename1 `t_unify _ t2 t2' = SOME s2`
   >> old_drule (REWRITE_RULE [Once CONJ_SYM] t_unify_wfs)
   >> old_drule t_unify_check_s
   >> simp []
   >> rpt (disch_then old_drule)
   >> `check_t tvs (count st2.next_uvar) t2 ∧ check_t tvs (count st2.next_uvar) t2'`
     by metis_tac [check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y``]
   >> rw []
   >> first_x_assum old_drule
   >> simp []
   >> disch_then irule
   >> simp []
   >> conj_tac >- metis_tac [ienv_ok_more]
   >> conj_tac >- (
     fs [Abbr `bindings2`]
     >> first_x_assum old_drule
     >> simp [ienv_ok_def])
   >> metis_tac [check_t_more4])
 >- (
   first_x_assum old_drule
   >> first_x_assum old_drule
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e _ (ienv with inf_v := bindings) _ _ = _`
   >> `ienv_ok (count (st.next_uvar+1)) (ienv with inf_v := bindings)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsBind
       >> simp [check_t_def]
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more3])
   >> first_x_assum irule
   >> conj_tac >- (
     old_drule (CONJUNCT1 infer_e_wfs)
     >> rw [])
   >> conj_tac >- (
     old_drule (CONJUNCT1 infer_e_next_uvar_mono)
     >> rw []
     >> metis_tac [ienv_ok_more, DECIDE ``x ≤ x+1n``])
   >> first_x_assum irule
   >> simp [check_s_more])
QED

Theorem generalise_complete_lemma[local]:
  !tvs ts.
  (∀uv. uv ∈ FDOM (FEMPTY |++ ts) ⇒ ∃tv. (FEMPTY |++ ts) ' uv = tv ∧ tv < tvs)
  ⇒
  (∀uv. uv ∈ FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ⇒ ∃tv. (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ' uv = Infer_Tvar_db tv ∧ tv < tvs)
Proof
  rw [FDOM_FUPDATE_LIST, MEM_MAP] >>
  PairCases_on `y'` >>
  fs [] >>
  `y'0 ∈ FDOM (FEMPTY |++ ts)`
          by (rw [FDOM_FUPDATE_LIST, MEM_MAP] >> metis_tac [FST]) >>
  metis_tac [FST, fupdate_list_map]
QED

Theorem generalise_complete_lemma2[local]:
  !s ts.
  t_wfs s ∧
  ALL_DISTINCT (MAP FST ts) ∧
  EVERY (\t. t = Infer_Tapp [] TC_unit ∨ ?tvs. t = Infer_Tvar_db tvs) (MAP SND ts) ∧
  DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))
  ⇒
  pure_add_constraints s (MAP (\(uv,t). (Infer_Tuvar uv, t)) ts) (s |++ ts)
Proof
  induct_on `ts` >>
  rw [pure_add_constraints_def, FUPDATE_LIST_THM] >>
  PairCases_on `h` >>
  rw [pure_add_constraints_def] >>
  `t_unify s (Infer_Tuvar h0) h1 = SOME (s |+ (h0,h1))` by
    (rw [t_unify_eqn] >>
    rw [Once t_walk_eqn] >>
    rw [Once t_vwalk_eqn, FLOOKUP_DEF]
    >- (
      fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
      metis_tac [])
    >>
      fs [] >>
      rw [t_walk_eqn, t_ext_s_check_eqn, oc_tvar_db, oc_unit]) >>
  `t_wfs (s |+ (h0,h1))` by metis_tac [t_unify_wfs] >>
  qexists_tac `s |+ (h0,h1)` >>
  rw [] >>
  `DISJOINT (FDOM (s |+ (h0,h1))) (FDOM (FEMPTY |++ ts))` by
    (fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
    metis_tac []) >>
  metis_tac []
QED

Definition infer_subst_var_def:
(infer_subst_var s (Infer_Tuvar n) =
  case FLOOKUP s n of
    | NONE => Infer_Tuvar n
    | SOME tv => Infer_Tvar_db tv) ∧
(infer_subst_var s t = t)
End

Theorem generalise_complete_lemma4[local]:
  !s. t_wfs s ⇒
  !t s'. t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') ∧
         ALL_DISTINCT (MAP FST s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s')) ⇒
         infer_subst_var (FEMPTY |++ s') (t_vwalk s t) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') t
Proof
  strip_tac >>
 strip_tac >>
 imp_res_tac (DISCH_ALL t_vwalk_ind) >>
 pop_assum ho_match_mp_tac >>
 rw [] >>
 imp_res_tac t_vwalk_eqn >>
 ONCE_ASM_REWRITE_TAC [] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 fs [flookup_fupdate_list, infer_subst_var_def] >>
 every_case_tac >>
 fs [infer_subst_var_def, flookup_fupdate_list] >>
 every_case_tac >>
 fs [ALOOKUP_FAILS, PROVE [flookup_thm] ``FLOOKUP f x = NONE ⇔ x ∉ FDOM f``] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11]
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
QED

Theorem generalise_complete_lemma5[local]:
  !s. t_wfs s ⇒
  !t s'. t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') ⇒
         ALL_DISTINCT (MAP FST s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s')) ⇒
         infer_subst (FEMPTY |++ s') (t_walkstar s t) = t_walkstar (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') t
Proof
  strip_tac >>
 strip_tac >>
 imp_res_tac t_walkstar_ind >>
 pop_assum ho_match_mp_tac >>
 rw [] >>
 cases_on `t` >>
 rw [t_walkstar_eqn, t_walk_eqn, infer_subst_def] >>
 fs [t_walk_eqn]
 >- (induct_on `l` >>
     rw []) >>
 `infer_subst_var (FEMPTY |++ s') (t_vwalk s n) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n`
          by metis_tac [generalise_complete_lemma4] >>
 cases_on `t_vwalk s n` >>
 rw [] >>
 cases_on `t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n` >>
 rw [] >>
 fs [infer_subst_def, infer_subst_var_def] >>
 rw [MAP_MAP_o, MAP_EQ_f] >>
 cases_on `FLOOKUP (FEMPTY |++ s') n'` >>
 fs []
QED

Theorem fst_lem[local]:
  FST = (\(x,y).x)
Proof
  rw [FUN_EQ_THM] >>
PairCases_on `x` >>
rw []
QED

Theorem t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`

(* Rename (type_system) type identifiers with a function *)
Definition ts_tid_rename_def:
  (ts_tid_rename f (Tapp ts tn) = Tapp (MAP (ts_tid_rename f) ts) (f tn)) ∧
  (ts_tid_rename f t = t)
Termination
  WF_REL_TAC `measure (λ(_,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac
End

val ts_tid_rename_ind = theorem"ts_tid_rename_ind";

Theorem ts_tid_rename_I[simp]:
   ts_tid_rename I = I
Proof
  simp[FUN_EQ_THM]
  \\ ho_match_mp_tac t_ind
  \\ rw[ts_tid_rename_def, MAP_EQ_ID, EVERY_MEM]
QED

(* All type ids in a type belonging to a set *)
Definition set_tids_def:
  (set_tids (Tapp ts tn) = tn INSERT (BIGUNION (set (MAP set_tids ts)))) ∧
  (set_tids _ = {})
Termination
  WF_REL_TAC `measure t_size` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac
End

val set_tids_ind = theorem"set_tids_ind";

Theorem set_tids_ts_tid_rename:
   ∀f t. set_tids (ts_tid_rename f t) = IMAGE f (set_tids t)
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, set_tids_def]
  \\ rw[Once EXTENSION, MEM_MAP, PULL_EXISTS]
  \\ metis_tac[IN_IMAGE]
QED

Definition set_tids_subset_def:
  set_tids_subset tids t <=> set_tids t ⊆ tids
End

Theorem set_tids_subset_type_subst:
    ∀s t tids.
  FEVERY (set_tids_subset tids o SND) s ∧
  set_tids_subset tids t ⇒
  set_tids_subset tids (type_subst s t)
Proof
  ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,set_tids_def]
  >- (
    TOP_CASE_TAC>>
    fs[set_tids_def]>>
    old_drule (GEN_ALL FEVERY_FLOOKUP)>>fs[]>>
    metis_tac[])
  >- (
    fs[set_tids_subset_def,set_tids_def]>>
    fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>rw[]>>
    last_x_assum old_drule>>
    disch_then old_drule>>
    disch_then match_mp_tac>>
    metis_tac[])
QED

Definition unconvert_t_def:
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc) ∧
(unconvert_t (Tvar v) = Infer_Tuvar ARB)
Termination
  wf_rel_tac `measure t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []
End

val unconvert_t_ind = theorem"unconvert_t_ind"

(* Properties about inferencer type identifiers *)
Definition inf_set_tids_def:
  (inf_set_tids (Infer_Tapp ts tn) = tn INSERT (BIGUNION (set (MAP inf_set_tids ts)))) ∧
  (inf_set_tids _ = {})
Termination
  WF_REL_TAC `measure infer_t_size` >>
  rw [] >>
  induct_on `ts` >>
  rw [infer_tTheory.infer_t_size_def] >>
  res_tac >>
  decide_tac
End

Definition inf_set_tids_subset_def:
  inf_set_tids_subset tids t <=> inf_set_tids t ⊆ tids
End

Theorem typeSystem_t_ind =
  deBruijn_subst_ind |> Q.SPEC ‘λ_ _ x. P x’ |> SRULE [];

Theorem inf_set_tids_infer_type_subst_SUBSET:
  ∀subst (t:typeSystem$t).
    inf_set_tids (infer_type_subst subst t) ⊆
    set_tids t ∪ BIGUNION (IMAGE inf_set_tids (set (MAP SND subst)))
Proof
  gen_tac \\ ho_match_mp_tac typeSystem_t_ind
  \\ rw[infer_type_subst_alt, set_tids_def, inf_set_tids_def,
        SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  \\ TRY FULL_CASE_TAC \\ fs[inf_set_tids_def]
  \\ imp_res_tac ALOOKUP_MEM
  \\ metis_tac[SND]
QED

Theorem inf_set_tids_infer_deBruijn_subst_SUBSET:
  ∀subst t.
    inf_set_tids (infer_deBruijn_subst subst t) ⊆
    inf_set_tids t ∪ BIGUNION (IMAGE inf_set_tids (set subst))
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  \\ rw[infer_deBruijn_subst_alt, inf_set_tids_def,
        SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  \\ metis_tac[MEM_EL]
QED

Theorem inf_set_tids_unconvert:
   ∀t. inf_set_tids (unconvert_t t) = set_tids t
Proof
  recInduct set_tids_ind
  \\ rw[unconvert_t_def, inf_set_tids_def, set_tids_def]
  \\ rw[Once EXTENSION,MEM_MAP,PULL_EXISTS,EQ_IMP_THM]
  \\ metis_tac[EXTENSION]
QED

(* all the tids used in a tenv *)
Definition inf_set_tids_ienv_def:
  inf_set_tids_ienv tids (ienv:inf_env) ⇔
  nsAll (λi (ls,t). inf_set_tids_subset tids (unconvert_t t)) ienv.inf_t ∧
  nsAll (λi (ls,ts,tid). EVERY (λt. inf_set_tids_subset tids (unconvert_t t)) ts ∧ tid ∈ tids) ienv.inf_c ∧
  nsAll (λi (n,t). inf_set_tids_subset tids t) ienv.inf_v
End

Definition inf_set_tids_subst_def:
  inf_set_tids_subst tids subst ⇔
  !t. t ∈ FRANGE subst ⇒ inf_set_tids_subset tids t
End

Definition prim_tids_def:
  prim_tids contain tids ⇔
    EVERY (\x. x ∈ tids ⇔ contain) (Tlist_num::Tbool_num::prim_type_nums)
End

Theorem set_tids_subset_type_name_subst:
    ∀tenvt t tids.
  prim_tids T tids ∧
  nsAll (λi (ls,t). set_tids_subset tids t) tenvt ==>
  set_tids_subset tids (type_name_subst tenvt t)
Proof
  ho_match_mp_tac type_name_subst_ind>>
  rw[set_tids_def,type_name_subst_def,set_tids_subset_def]
  >- fs[prim_tids_def,prim_type_nums_def]
  >- (
     fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>
     metis_tac[])
  >- fs[prim_tids_def,prim_type_nums_def]
  >>
    TOP_CASE_TAC>>fs[set_tids_def,EVERY_MAP,EVERY_MEM]
    >- (
      CONJ_TAC>- fs[prim_tids_def,prim_type_nums_def]>>
      fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>
      metis_tac[])
    >>
      TOP_CASE_TAC>>fs[GSYM set_tids_subset_def]>>
      match_mp_tac set_tids_subset_type_subst>>
      CONJ_TAC
      >- (
        match_mp_tac FEVERY_alist_to_fmap>>fs[EVERY_MEM,MEM_ZIP]>>
        rw[]>>
        imp_res_tac MEM_ZIP2>>
        fs[EL_MAP]>>
        metis_tac[MEM_EL])
      >>
        old_drule nsLookup_nsAll >> disch_then old_drule>>
        simp[]
QED

Theorem generalise_complete:
 !n s l tvs s' ts next_uvar.
  generalise_list 0 n FEMPTY (MAP (t_walkstar s) l) = (tvs,s',ts) ∧
  t_wfs s ∧
  check_s 0 (count next_uvar) s ∧
  EVERY (\t. check_t 0 (count next_uvar) t) l
  ⇒
  ?ec1 last_sub.
    (ts = MAP (t_walkstar last_sub) l) ∧
    t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub ∧
    (TC_unit ∈ tids ∧ inf_set_tids_subst tids s ⇒ inf_set_tids_subst tids last_sub)
    (* ∧ EVERY (check_t tvs (count ???)) (MAP FST ec1 ++ MAP SND ec1)*)
Proof
  rw [] >>
  imp_res_tac generalise_subst_empty >>
  rw [sub_completion_def] >>
  Q.ABBREV_TAC `unconstrained = count next_uvar DIFF (FDOM s ∪ FDOM s')` >>
  `?ts. ALL_DISTINCT (MAP FST ts) ∧ s' = FEMPTY |++ ts` by metis_tac [fmap_to_list] >>
  rw [] >>
  `FINITE unconstrained` by metis_tac [FINITE_COUNT, FINITE_DIFF, FINITE_UNION, finite_t_rangevars] >>
  `?ts2. ALL_DISTINCT (MAP FST ts2) ∧ FEMPTY |++ ts2 = (FUN_FMAP (\x. Infer_Tapp [] TC_unit) unconstrained)` by metis_tac [fmap_to_list] >>
  `DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts2))`
               by (rw [EXTENSION, DISJOINT_DEF] >>
                   Q.UNABBREV_TAC `unconstrained` >>
                   rw [] >>
                   CCONTR_TAC >>
                   fs [] >>
                   fs []) >>
  `DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))`
               by (rw [] >>
                   fs [MEM_MAP] >>
                   rw [EXTENSION, DISJOINT_DEF] >>
                   fs [] >>
                   metis_tac [t_walkstar_vars_notin]) >>
  `t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)`
        by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)`
               by (rw [t_vR_eqn, FUN_EQ_THM] >>
                   every_case_tac >>
                   fs [flookup_fupdate_list] >>
                   every_case_tac >>
                   fs [] >>
                   imp_res_tac ALOOKUP_MEM >>
                   fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, t_vars_eqn] >>
                   fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MEM_MAP] >>
                   metis_tac [pair_CASES, FST]) >>
           fs [t_vars_eqn, t_wfs_eqn]) >>
  `t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
        by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
               by (rw [t_vR_eqn, FUN_EQ_THM] >>
                   cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) x'` >>
                   rw [flookup_update_list_some, flookup_update_list_none] >-
                   fs [flookup_update_list_none] >>
                   pop_assum mp_tac >>
                   rw [flookup_update_list_some] >|
                   [imp_res_tac ALOOKUP_MEM >>
                        pop_assum mp_tac >>
                        rw [MAP_REVERSE] >>
                        `x' ∈ FDOM (FEMPTY |++ ts2)`
                                  by metis_tac [MEM_MAP, FDOM_FUPDATE_LIST, IN_UNION, FST, pair_CASES] >>
                        `x' ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                        `FLOOKUP s x' = NONE` by metis_tac [FLOOKUP_DEF] >>
                        rw [] >>
                        `FLOOKUP (FEMPTY |++ ts2) x' = SOME x''` by rw [flookup_update_list_some] >>
                        pop_assum mp_tac >>
                        rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                        rw [FLOOKUP_FUN_FMAP, t_vars_eqn],
                   imp_res_tac ALOOKUP_MEM >>
                        pop_assum mp_tac >>
                        rw [MEM_MAP, MAP_REVERSE] >>
                        PairCases_on `y` >>
                        rw [] >>
                        `MEM y0 (MAP FST ts)` by (rw [MEM_MAP] >> metis_tac [FST]) >>
                        `y0 ∈ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                        `y0 ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                        `FLOOKUP s y0 = NONE` by metis_tac [FLOOKUP_DEF] >>
                        rw [] >>
                        fs [] >>
                        `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) y0 = SOME x''` by rw [flookup_update_list_some] >>
                        imp_res_tac ALOOKUP_MEM >>
                        fs [MEM_MAP] >>
                        rw [] >>
                        PairCases_on `y'` >>
                        rw [] >>
                        rw [t_vars_eqn, encode_infer_t_def],
                    rw []]) >>
           fs [t_vars_eqn, t_wfs_eqn]) >>
  `count next_uvar ⊆ FDOM (s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2)`
        by (rw [FDOM_FUPDATE_LIST, SUBSET_DEF] >>
            CCONTR_TAC >>
            fs [] >>
            `x ∉ FDOM (FEMPTY |++ ts2)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
            pop_assum mp_tac >>
            rw [FLOOKUP_FUN_FMAP] >>
            `x ∉ set (MAP FST ts)` by metis_tac [map_fst] >>
            `x ∉ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
            Q.UNABBREV_TAC `unconstrained` >>
            rw []) >>
  `DISJOINT (FDOM (FEMPTY |++ ts)) (FDOM (FEMPTY |++ ts2))`
               by (Q.UNABBREV_TAC `unconstrained` >>
                   rw [DISJOINT_DEF, EXTENSION] >>
                   metis_tac []) >>
  qexists_tac `(MAP (\(uv,tv). (Infer_Tuvar uv, Infer_Tvar_db tv)) ts) ++
               (MAP (\(uv,t). (Infer_Tuvar uv, t)) ts2)` >>
  qexists_tac `s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2` >>
  conj_tac >-
  (rw [MAP_EQ_f, MAP_MAP_o] >>
       `DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts))`
                 by (fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, map_fst] >>
                     metis_tac []) >>
       `infer_subst (FEMPTY |++ ts) (t_walkstar s e) = t_walkstar (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) e`
                 by metis_tac [generalise_complete_lemma5] >>
       rw [] >>
       fs [] >>
       rw [] >>
       fs [] >>
       `(t_vars o infer_subst (FEMPTY |++ ts) o t_walkstar s) e = {}`
               by metis_tac [no_vars_lem, MAP_MAP_o] >>
       fs [combinTheory.o_DEF] >>
       pop_assum mp_tac >>
       rw [] >>
       `DISJOINT (FDOM (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) (FDOM (FEMPTY |++ ts2))`
                  by (rw [FDOM_FUPDATE_LIST, map_fst] >>
                      fs [FDOM_FUPDATE_LIST]) >>
       metis_tac [no_vars_extend_subst])
  \\ conj_tac >- rw[]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac >- (
   rw[] \\
   `MAP (λ(uv,tv). (Infer_Tuvar uv,Infer_Tvar_db tv)) ts ++ MAP (λ(uv,t). (Infer_Tuvar uv,t)) ts2
    =
    MAP (λ(uv,t). (Infer_Tuvar uv, t)) (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts ++ ts2)`
              by rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       ASM_REWRITE_TAC [GSYM FUPDATE_LIST_APPEND] >>
       match_mp_tac generalise_complete_lemma2 >>
       rw [MAP_MAP_o, EVERY_MAP, LAMBDA_PROD, ALL_DISTINCT_APPEND, combinTheory.o_DEF] >|
       [metis_tac [fst_lem],
        `e ∈ FDOM (FEMPTY |++ ts)`
                     by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, fst_lem] >>
            `e ∉ unconstrained`
                     by (Q.UNABBREV_TAC `unconstrained` >>
                         fs []) >>
            `e ∉ FDOM (FEMPTY |++ ts2)`
                      by metis_tac [FDOM_FMAP] >>
            fs [FDOM_FUPDATE_LIST],
        rw [EVERY_MEM] >>
            PairCases_on `e` >>
            rw [],
        rw [EVERY_MEM] >>
            PairCases_on `e` >>
            rw [] >>
            `FLOOKUP (FEMPTY |++ ts2) e0 = SOME e1`
                      by (rw [flookup_fupdate_list] >>
                          full_case_tac >>
                          fs [ALOOKUP_FAILS] >>
                          metis_tac [optionTheory.SOME_11,ALOOKUP_ALL_DISTINCT_MEM, MEM_REVERSE, ALL_DISTINCT_REVERSE, REVERSE_REVERSE, MAP_REVERSE]) >>
            pop_assum mp_tac >>
            rw [FLOOKUP_FUN_FMAP],
        fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
            rw [map_fst] >>
            metis_tac []])
  \\ conj_tac >- (
   rw[] \\
   ONCE_REWRITE_TAC [GSYM COUNT_ZERO] >>
       match_mp_tac t_walkstar_check >>
       rw [check_t_def, check_s_def] >>
       `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) uv' = SOME ((s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) ' uv')`
                      by rw [FLOOKUP_DEF] >>
       pop_assum mp_tac >>
       rw [flookup_update_list_some] >>
       Q.ABBREV_TAC `last_sub = s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2` >|
       [`FLOOKUP (FEMPTY |++ ts2) uv' = SOME (last_sub ' uv')` by metis_tac [flookup_update_list_some] >>
            pop_assum mp_tac >>
            rw [FLOOKUP_FUN_FMAP] >>
            metis_tac [check_t_def, EVERY_DEF],
        `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) uv' = SOME (last_sub ' uv')`
                      by metis_tac [flookup_update_list_some] >>
            `(!uv. uv ∈ FDOM (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ⇒ ∃tv. (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ' uv = Infer_Tvar_db tv ∧ tv < tvs + n)`
                     by metis_tac [generalise_complete_lemma] >>
            fs [FLOOKUP_DEF] >>
            metis_tac [check_t_def],
        fs [check_s_def, FLOOKUP_DEF] >>
            metis_tac [check_t_more2, check_t_more5, arithmeticTheory.ADD_0]])
   \\ (*conj_tac >-*) (
     rw[] \\
     simp[inf_set_tids_subst_def, IN_FRANGE_FLOOKUP, PULL_EXISTS, flookup_fupdate_list]
     \\ qpat_x_assum`FEMPTY |++ _ = _`mp_tac
     \\ simp[FUPDATE_LIST_alist_to_fmap]
     \\ disch_then(mp_tac o Q.AP_TERM`FLOOKUP`) \\ simp[]
     \\ simp[FLOOKUP_FUN_FMAP]
     \\ strip_tac \\ rpt gen_tac
     \\ IF_CASES_TAC \\ simp[]
     >- (
       rw[inf_set_tids_subset_def]
       \\ rw[inf_set_tids_def] )
     \\ reverse CASE_TAC
     >- (
       rw[]
       \\ imp_res_tac ALOOKUP_MEM
       \\ fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD]
       \\ EVAL_TAC )
     \\ rw[]
     \\ qhdtm_x_assum`inf_set_tids_subst`mp_tac
     \\ simp[inf_set_tids_subst_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
     \\ metis_tac[])
QED

Theorem init_infer_state_wfs[local]:
  t_wfs (init_infer_state st).subst ∧
   check_s 0 ∅ (init_infer_state st).subst
Proof
  rw [check_s_def, init_infer_state_def, t_wfs_def]
QED

Theorem init_infer_state_next_uvar[simp]:
   (init_infer_state st).next_uvar = 0
Proof
 rw [init_infer_state_def]
QED

Theorem init_infer_state_subst[simp]:
   (init_infer_state st).subst = FEMPTY
Proof
  EVAL_TAC
QED

Theorem t_wfs_FEMPTY[simp]:
   t_wfs FEMPTY
Proof
  rw[t_wfs_eqn]
  \\ EVAL_TAC
  \\ rw[relationTheory.WF_DEF, substTheory.vR_def]
QED

Theorem t_wfs_init_infer_state[simp]:
   t_wfs (init_infer_state s).subst
Proof
rw[]
QED

val let_tac =
   old_drule (CONJUNCT1 infer_e_check_t)
   >> old_drule (CONJUNCT1 infer_e_check_s)
   >> simp []
   >> disch_then old_drule
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> old_drule (CONJUNCT1 infer_p_check_t)
   >> fs [ienv_ok_def]
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_check_s)
   >> simp []
   >> disch_then old_drule
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_wfs)
   >> disch_then old_drule
   >> rw []
   >> old_drule t_unify_check_s
   >> rpt (disch_then old_drule)
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_p_next_uvar_mono)
   >> rw []
   >> rename1 `infer_p _ _ _ st2 = (Success (t2, env2), st3)`
   >> `check_t 0 (count st3.next_uvar) t1` by metis_tac [check_t_more4]
   >> fs []
   >> old_drule t_unify_wfs
   >> disch_then old_drule
   >> rw []
   >> old_drule generalise_complete
   >> rpt (disch_then old_drule)
   >> fs [every_shim]
   >> rw [ienv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> simp [EVERY_MEM, MEM_ZIP]
   >> rw []
   >> rw [EL_MAP]
   >> irule (CONJUNCT1 check_t_walkstar)
   >> simp []
   >> fs [sub_completion_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
   >> metis_tac [check_t_more2, check_t_more5, MEM_EL, DECIDE ``x + 0n = x``];

Theorem eta2_thm[local]:
  (\x. f a b x) = f a b
Proof
  metis_tac []
QED

Theorem check_env_letrec_lem2[local]:
  ∀funs.
    nsAll (λx (tvs,t). check_t tvs (count (LENGTH funs)) t)
      (alist_to_ns (MAP2 (λ(f,x,e) uvar. (f,0,uvar))
                      funs
                      (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
Proof
  rw []
 >> Q.SPECL_THEN [`LENGTH funs`, `funs`, `0n`] mp_tac check_env_letrec_lem
 >> simp []
QED

Theorem ienv_ok_extend_dec_ienv:
   !e1 e2 n. ienv_ok n e1 ∧ ienv_ok n e2 ⇒ ienv_ok n (extend_dec_ienv e1 e2)
Proof
 rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
     typeSoundInvariantsTheory.tenv_abbrev_ok_def, extend_dec_ienv_def]
 >> metis_tac [nsAll_nsAppend]
QED

Theorem infer_d_check:
 (!d ienv st1 st2 ienv'.
  infer_d ienv d st1 = (Success ienv', st2) ∧
  ienv_ok {} ienv
  ⇒
  ienv_ok {} ienv') ∧
 (!ds ienv st1 st2 ienv'.
  infer_ds ienv ds st1 = (Success ienv', st2) ∧
  ienv_ok {} ienv
  ⇒
  ienv_ok {} ienv')
Proof
 Induct>>rw[]>>
 fs [infer_d_def, success_eqns]>>
 rpt (pairarg_tac >> fs [success_eqns])>>
 fs [init_state_def]>> rw[]>>
 strip_assume_tac init_infer_state_wfs
 >- ( fs[] \\ let_tac )
 >- ( fs[] \\ let_tac )
 >- (
   qmatch_assum_abbrev_tac
     `infer_funs _ (ienv with inf_v := nsAppend bindings ienv.inf_v) _ _ = _`
   >> rename1 `init_infer_state s0`
   >> rename1 `infer_funs _ _ funs _ = (Success funs_ts, st1)`
   >> rename1 `pure_add_constraints _ _ st2.subst`
   >> `ienv_ok (count (LENGTH funs)) (ienv with inf_v := nsAppend bindings ienv.inf_v)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsAppend
       >> simp []
       >> conj_tac >- metis_tac [check_env_letrec_lem2]
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more4, COUNT_ZERO, DECIDE ``0n≤ x``])
   >> `check_s 0 (count (LENGTH funs)) (init_infer_state s0).subst`
     by rw [init_infer_state_def, check_s_def]
   >> old_drule (List.nth (CONJUNCTS infer_e_check_t, 3))
   >> old_drule (List.nth (CONJUNCTS infer_e_wfs, 3))
   >> fs [ienv_ok_def]
   >> old_drule (List.nth (CONJUNCTS infer_e_check_s, 3))
   >> simp [ienv_ok_def]
   >> disch_then old_drule
   >> rw []
   >> old_drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
   >> simp [ienv_ok_def]
   >> old_drule pure_add_constraints_wfs
   >> rw []
   >> `EVERY (\t. check_t 0 (count st2.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))`
      by rw [EVERY_MAP, every_count_list, check_t_def]
   >> old_drule pure_add_constraints_check_s
   >> fs [every_zip_split, eta2_thm, ETA_THM]
   >> simp [GSYM CONJ_ASSOC]
   >> rpt (disch_then old_drule)
   >> rw []
   >> old_drule generalise_complete
   >> simp [eta2_thm]
   >> rpt (disch_then old_drule)
   >> rw [ienv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> rw [EVERY_MEM, MEM_ZIP]
   >> pairarg_tac
   >> rw []
   >> pairarg_tac
   >> rw []
   >> fs [MAP2_MAP, LENGTH_COUNT_LIST, MEM_MAP, MEM_ZIP, MAP_MAP_o, combinTheory.o_DEF]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> rw [EL_MAP, LENGTH_COUNT_LIST]
   >> irule (CONJUNCT1 check_t_walkstar)
   >> simp []
   >> fs [sub_completion_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
   >> rw [check_t_def, EL_COUNT_LIST]
   >> fs [SUBSET_DEF])
 >- (
   simp [ienv_ok_def]
   >> conj_tac
   >- rw [ienv_val_ok_def]
   \\ fs[n_fresh_id_def] \\ rveq \\ fs[]
   >> conj_asm2_tac
   >- (
     irule check_ctor_tenv_ok
     >> fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def, ienv_ok_def]
     >> irule nsAll_nsAppend
     >> simp [])
   >> fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def]
   >> irule nsAll_alist_to_ns
   >> rw [EVERY_MAP, EVERY_MEM, MAP2_ZIP, ZIP_GENLIST, MAP_GENLIST, MEM_GENLIST]
   >> rpt (pairarg_tac >> fs [])
   >> fs []
   >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (
   imp_res_tac type_name_check_subst_thm >>
   fs [] >>
   rw [] >>
   rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_abbrev_ok_def]
   >> irule check_freevars_type_name_subst
   >> fs [ienv_ok_def])
 >- (
   imp_res_tac type_name_check_subst_thm >>
   fs [] >>
   fs [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
       EVERY_MAP, EVERY_MEM, MEM_MAP]
   >> rw []
   >> irule check_freevars_type_name_subst
   >> fs [EVERY_MEM])
 >- (
  fs[ienv_ok_def,lift_ienv_def,ienv_val_ok_def,
     typeSoundInvariantsTheory.tenv_ctor_ok_def,
     typeSoundInvariantsTheory.tenv_abbrev_ok_def]
  \\ metis_tac[])
 >- (
  rpt (first_x_assum old_drule)
  \\ rw []
  \\ metis_tac [ienv_ok_extend_dec_ienv]
 )
 >- fs[ienv_ok_def,ienv_val_ok_def]
 >>
   match_mp_tac ienv_ok_extend_dec_ienv>>
   rpt (first_x_assum old_drule)>> rw[]>>
   metis_tac[ienv_ok_extend_dec_ienv]
QED

Theorem infer_p_next_id_const:
 (!l cenv p st t env st'.
    (infer_p l cenv p st = (Success (t,env), st'))
    ⇒
    st.next_id = st'.next_id) ∧
 (!l cenv ps st ts env st'.
    (infer_ps l cenv ps st = (Success (ts,env), st'))
    ⇒
    st.next_id = st'.next_id)
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
  fs[]>>
  imp_res_tac type_name_check_subst_state >>
  fs [] >>
  res_tac >>
  fs []
QED

Theorem infer_e_next_id_const:
 (!l ienv e st st' t.
    (infer_e l ienv e st = (Success t, st'))
    ⇒
    st.next_id = st'.next_id) ∧
 (!l ienv es st st' ts.
    (infer_es l ienv es st = (Success ts, st'))
    ⇒
    st.next_id = st'.next_id) ∧
 (!l ienv pes t1 t2 st st'.
    (infer_pes l ienv pes t1 t2 st = (Success (), st'))
    ⇒
    st.next_id = st'.next_id) ∧
 (!l ienv funs st st' ts.
    (infer_funs l ienv funs st = (Success ts, st'))
    ⇒
    st.next_id = st'.next_id)
Proof
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
imp_res_tac type_name_check_subst_state >>
fs [] >>
res_tac >>
fs [] >>
every_case_tac >> TRY (Cases_on `uop`) >>
fs [success_eqns] >>
metis_tac [infer_p_next_id_const,pair_CASES]
QED

Theorem infer_d_next_id_mono:
 (!d ienv st t st'.
  infer_d ienv d st = (Success t, st') ⇒
  st.next_id ≤ st'.next_id) ∧
 (!ds ienv st ts st'.
  (infer_ds ienv ds st = (Success ts, st') ⇒
  st.next_id ≤ st'.next_id))
Proof
  Induct>>rw[]>>
  fs [infer_d_def, success_eqns]>>
  rpt (pairarg_tac >> fs [success_eqns])>>
  fs[init_state_def,init_infer_state_def]>>
  rw[]>>
  imp_res_tac type_name_check_subst_state >>
  fs [] >>
  imp_res_tac infer_e_next_id_const>>
  imp_res_tac infer_p_next_id_const>>fs[]
  >- (fs[n_fresh_id_def]>>rw[])>>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem count_list_one[local]:
  COUNT_LIST 1 = [0]
Proof
  metis_tac [COUNT_LIST_def, MAP, DECIDE ``1 = SUC 0``]
QED

Theorem check_freevars_more_append[local]:
  (!t x fvs1 fvs2.
  check_freevars x fvs1 t ⇒
  check_freevars x (fvs2++fvs1) t ∧
  check_freevars x (fvs1++fvs2) t) ∧
 (!ts x fvs1 fvs2.
  EVERY (check_freevars x fvs1) ts ⇒
  EVERY (check_freevars x (fvs2++fvs1)) ts ∧
  EVERY (check_freevars x (fvs1++fvs2)) ts)
Proof
  Induct >>
rw [check_freevars_def] >>
metis_tac []
QED

Theorem check_freevars_more:
   ∀a b c. check_freevars a b c ⇒ ∀b'. set b ⊆ set b' ⇒ check_freevars a b' c
Proof
  ho_match_mp_tac check_freevars_ind >>
  rw[check_freevars_def] >-
    fs[SUBSET_DEF] >>
  fs[EVERY_MEM]
QED

Theorem check_t_infer_type_subst_dbs:
   ∀m w t n u ls.
    check_freevars m w t ∧
    m + LENGTH ls ≤ n ∧
    (ls = [] ⇒ 0 < m)
    ⇒
    check_t n u (infer_type_subst (ZIP(ls,MAP Infer_Tvar_db (COUNT_LIST (LENGTH ls)))) t)
Proof
  ho_match_mp_tac check_freevars_ind >>
  conj_tac >- (
    simp[check_freevars_def] >>
    simp[infer_type_subst_alt] >>
    simp[ZIP_MAP,LENGTH_COUNT_LIST] >>
    simp[ALOOKUP_MAP,LAMBDA_PROD] >>
    simp[COUNT_LIST_GENLIST] >>
    simp[ZIP_GENLIST] >>
    rw[] >>
    BasicProvers.CASE_TAC >- (
      simp[check_t_def] >>
      Cases_on`LENGTH ls = 0`>-(fs[LENGTH_NIL] >> DECIDE_TAC) >>
      DECIDE_TAC ) >>
    fs[optionTheory.OPTION_MAP_EQ_SOME] >>
    simp[check_t_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_GENLIST] >>
    DECIDE_TAC ) >>
  conj_tac >- (
    rw[check_freevars_def,infer_type_subst_alt,check_t_def] >>
    simp[EVERY_MAP] >> fs[EVERY_MEM] ) >>
  rw[check_freevars_def,check_t_def,infer_type_subst_alt] >>
  DECIDE_TAC
QED

Theorem nub_eq_nil:
   ∀ls. nub ls = [] ⇔ ls = []
Proof
  Induct >> simp[nub_def] >> rw[] >>
  Cases_on`ls`>>fs[]
QED

Theorem ienv_ok_lift:
   !mn ienv n. ienv_ok n ienv ⇒ ienv_ok n (lift_ienv mn ienv)
Proof
 rw [lift_ienv_def, ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
     typeSoundInvariantsTheory.tenv_abbrev_ok_def]
QED

Theorem sub_completion_wfs:
 !n uvars s1 ts s2.
  t_wfs s1 ∧
  sub_completion n uvars s1 ts s2
  ⇒
  t_wfs s2
Proof
  rw [sub_completion_def] >>
  pop_assum (fn _ => all_tac) >>
  pop_assum (fn _ => all_tac) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  Q.SPEC_TAC (`s1`, `s1`) >>
  induct_on `ts` >>
  rw [pure_add_constraints_def] >-
  metis_tac [] >>
  PairCases_on `h` >>
  fs [pure_add_constraints_def] >>
  metis_tac [t_unify_wfs]
QED

Theorem infer_deBruijn_subst_id:
 (!t. infer_deBruijn_subst [] t = t) ∧
  (!ts. MAP (infer_deBruijn_subst []) ts = ts)
Proof
  Induct>>rw[]>>fs[infer_deBruijn_subst_alt,MAP_EQ_ID]
QED

Theorem deBruijn_subst_nothing:
   (∀t.
  deBruijn_subst 0 [] t = t )∧
  ∀ts.
  MAP (deBruijn_subst 0 []) ts = ts
Proof
  ho_match_mp_tac t_induction>>
  fs[deBruijn_subst_def]>>rw[]>>
  fs[LIST_EQ_REWRITE]>>rw[]>>
  fs[MEM_EL,EL_MAP]
QED

Theorem infer_deBruijn_subst_id2:
   (∀t.
  check_t tvs {} t ⇒
  infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs) t = t) ∧
  (∀ts.
  EVERY (check_t tvs {}) ts ⇒
  MAP (infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs)) ts = ts)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]>>fs[check_t_def]
  >-
    fs[infer_deBruijn_subst_alt]
  >>
    fs[infer_deBruijn_subst_alt,EVERY_MEM]>>
    metis_tac[]
QED

Theorem check_t_infer_deBruijn_subst:
  !subst t tvs uvs.
    check_t (tvs + LENGTH subst) uvs t ∧
    EVERY (check_t tvs uvs) subst
    ⇒
    check_t tvs uvs (infer_deBruijn_subst subst t)
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  >> rw [infer_deBruijn_subst_alt, check_t_def, EVERY_MEM, MEM_EL]
  >- metis_tac []
  >> simp [EL_MAP]
  >> metis_tac []
QED

Theorem infer_deBruijn_subst_uncheck:
   !s t max_tvs uvs.
    check_t max_tvs uvs (infer_deBruijn_subst s t)
    ⇒
    check_t (max_tvs + LENGTH s) uvs t
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  >> rw [check_t_def, infer_deBruijn_subst_alt]
  >> fs [EVERY_MAP, EVERY_EL]
  >> rw []
  >> first_x_assum old_drule
  >> fs [MEM_EL, PULL_EXISTS]
QED

Theorem db_subst_inc_id:
   !inst t.
    infer_deBruijn_subst inst (infer_deBruijn_inc (LENGTH inst) t) = t
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  >> rw [infer_deBruijn_inc_def, infer_deBruijn_subst_alt,
         MAP_MAP_o, combinTheory.o_DEF]
  >> Induct_on `l` >> rw []
QED

Theorem t_walkstar_db_subst:
   !inst t s.
    t_wfs s ⇒
    t_walkstar s (infer_deBruijn_subst inst t)
    =
    infer_deBruijn_subst (MAP (t_walkstar s) inst)
               (t_walkstar (infer_deBruijn_inc (LENGTH inst) o_f s) t)
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  >> rw [infer_deBruijn_subst_alt]
  >> old_drule inc_wfs
  >> disch_then (qspec_then `LENGTH inst` mp_tac)
  >> rw [t_walkstar_eqn1, infer_deBruijn_subst_alt, EL_MAP,
         MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  >> simp [walkstar_inc2]
  >> metis_tac [db_subst_inc_id, LENGTH_MAP]
QED

Theorem generalise_subst_exist:
    (t_wfs s ∧
  (∀uv. uv ∈ FDOM s ⇒ check_t tvs {} (t_walkstar s (Infer_Tuvar uv))))
  ⇒
  (∀t subst n smap a b t'.
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧
  t_vars t ⊆ FDOM s ∧
  check_t 0 (FDOM s) t ∧
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧
  generalise 0 n smap t = (a,b,t') ⇒
  ∃subst'.
    LENGTH subst' = a ∧
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x))) ∧
  (∀ts subst n smap a b ts'.
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧
  EVERY (λt. t_vars t ⊆ FDOM s) ts ∧
  EVERY (check_t 0 (FDOM s)) ts ∧
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧
  generalise_list 0 n smap ts = (a,b,ts') ⇒
  ∃subst'.
    LENGTH subst' = a ∧
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x)))
Proof
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  srw_tac[][]>>
  fsrw_tac[][check_t_def]
  >-
    (fsrw_tac[][generalise_def]>>
    qpat_x_assum`A=(a,b,t')` mp_tac>>BasicProvers.LET_ELIM_TAC>>
    fsrw_tac[][]>>
    first_assum match_mp_tac>>
    ntac 2 HINT_EXISTS_TAC >>
    fsrw_tac[][EVERY_MEM,t_vars_eqn,SUBSET_DEF,MEM_MAP]>>
    metis_tac[])
  >-
    (imp_res_tac generalise_subst>>
    fsrw_tac[][generalise_def]>>
    full_case_tac>>fsrw_tac[][]
    >-
      (qexists_tac`[t_walkstar s (Infer_Tuvar n)]`>>
      qpat_x_assum`A=b` sym_sub_tac>>
      srw_tac[][]
      >-
        (simp[FAPPLY_FUPDATE_THM]>>
        `x ≠ n` by
          (CCONTR_TAC>>
          fs[flookup_thm])>>
        fs[]>>
        `smap ' x < LENGTH subst` by fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>
        simp[EL_APPEND1])
      >>
      fs[t_vars_eqn,EL_LENGTH_APPEND])
    >>
    qexists_tac`[]`>>fs[EXTENSION]>>
    metis_tac[])
  >-
    (fs[generalise_def]>>
    qexists_tac`[]`>>fs[])
  >>
    fsrw_tac[][generalise_def]>>
    qpat_x_assum`A=(a,b,t')` mp_tac>>BasicProvers.LET_ELIM_TAC>>
    imp_res_tac generalise_subst>>
    first_x_assum(qspecl_then[`subst`,`smap`,`num_gen`,`s'`,`t'`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then[`subst++subst'`,`s'`,`num_gen'`,`s''`,`ts''`] mp_tac)>>
    impl_tac>-
      (fsrw_tac [ARITH_ss] []>>
      reverse CONJ_TAC>-
        metis_tac[]>>
      fs[IN_FRANGE,SUBSET_DEF,PULL_EXISTS]>>
      gen_tac>>Cases_on`k ∈ FDOM smap`>>fs[]>>
      fs[SUBMAP_DEF]>>
      res_tac>>
      DECIDE_TAC)>>
    rw[]>>
    qexists_tac`subst'++subst''`>>fs[]>>
    metis_tac[]
QED

Theorem infer_deBruijn_subst_infer_subst_walkstar:
    ∀b subst n m.
  FRANGE b ⊆ count (LENGTH subst) ∧
  t_wfs s
  ⇒
  ((∀t.
  (∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧
  check_t 0 m t ∧
  t_vars t ⊆ FDOM b
  ⇒
  infer_deBruijn_subst subst (infer_subst b t) =
  t_walkstar s t) ∧
  (∀ts.
  EVERY (λt.(∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x))) ts ∧
  EVERY (check_t 0 m) ts ∧
  EVERY (λt.t_vars t ⊆ FDOM b) ts
  ⇒
  MAP ((infer_deBruijn_subst subst) o (infer_subst b)) ts =
  MAP (t_walkstar s) ts))
Proof
  ntac 5 strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
  fs[infer_subst_def,t_walkstar_eqn1,check_t_def,infer_deBruijn_subst_alt]
  >-
    (fs[LIST_EQ_REWRITE,EL_MAP,t_vars_eqn,PULL_EXISTS,SUBSET_DEF,MEM_MAP]>>
    rw[]>>
    first_assum (match_mp_tac o MP_CANON)>>
    fs[EVERY_MEM]>>
    metis_tac[])
  >>
  (fs[t_vars_eqn] >> imp_res_tac flookup_thm>>
  fs[PULL_FORALL]>>
  fs[infer_deBruijn_subst_alt]>>
  reverse IF_CASES_TAC
  >- (fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>metis_tac[])
  >> REFL_TAC)
QED

Definition remap_tenv_def:
  remap_tenv f tenv =
  <|
    t := nsMap (λ(ls,t). (ls, ts_tid_rename f t)) tenv.t;
    c := nsMap (λ(ls,ts,tid). (ls, MAP (ts_tid_rename f) ts, f tid)) tenv.c;
    v := nsMap (λ(n,t). (n,ts_tid_rename f t)) tenv.v
   |>
End

Theorem remap_tenv_I[simp]:
   remap_tenv I = I
Proof
  rw[FUN_EQ_THM, remap_tenv_def, type_env_component_equality]
  \\ qmatch_goalsub_abbrev_tac`nsMap I'`
  \\ `I' = I` by simp[Abbr`I'`, UNCURRY, FUN_EQ_THM]
  \\ rw[]
QED

Theorem t_vwalk_set_tids:
   ∀s.  t_wfs s ⇒
   ∀v. inf_set_tids_subst tids s
   ⇒
   inf_set_tids (t_vwalk s v) ⊆ tids
Proof
  ntac 2 strip_tac
  \\ recInduct(t_vwalk_ind)
  \\ rw[] \\ fs[]
  \\ rw[Once t_vwalk_eqn]
  \\ CASE_TAC \\ fs[inf_set_tids_def]
  \\ CASE_TAC \\ fs[inf_set_tids_def]
  \\ fs[inf_set_tids_subst_def, FRANGE_FLOOKUP, PULL_EXISTS, inf_set_tids_subset_def]
  \\ res_tac \\ fs[inf_set_tids_def]
QED

Theorem t_walk_set_tids:
   ∀s t t'.
   t_wfs s ∧
   inf_set_tids_subst tids s ∧
   inf_set_tids_subset tids t ∧
   t_walk s t = t' ⇒
   inf_set_tids_subset tids t'
Proof
  Cases_on`t`
  \\ rw[t_walk_eqn]
  \\ fs[inf_set_tids_subset_def]
  \\ metis_tac[t_vwalk_set_tids]
QED

Theorem t_walkstar_set_tids:
   ∀s t t'.
   t_wfs s ∧
   inf_set_tids_subst tids s ∧
   inf_set_tids_subset tids t ∧
   t_walkstar s t = t' ⇒
   inf_set_tids_subset tids t'
Proof
  gen_tac
  \\ simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  \\ strip_tac
  \\ simp[AND_IMP_INTRO, PULL_FORALL]
  \\ recInduct (UNDISCH (SPEC_ALL t_walkstar_ind))
  \\ rw[]
  \\ rw[Once t_walkstar_eqn]
  \\ CASE_TAC \\ fs[inf_set_tids_subset_def, inf_set_tids_def]
  \\ old_drule t_walk_set_tids
  \\ fs[inf_set_tids_subset_def]
  \\ disch_then old_drule
  \\ fs[inf_set_tids_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  \\ metis_tac[]
QED

Theorem t_unify_set_tids:
     (∀s t1 t2. t_wfs s ==>
   ∀s'.
   inf_set_tids_subst tids s ∧
   inf_set_tids_subset tids t1 ∧
   inf_set_tids_subset tids t2 ∧
   t_unify s t1 t2 = SOME s' ⇒
   inf_set_tids_subst tids s') ∧
   (∀s ts1 ts2. t_wfs s ==>
   ∀s'.
   inf_set_tids_subst tids s ∧
   EVERY (inf_set_tids_subset tids) ts1 ∧
   EVERY (inf_set_tids_subset tids) ts2 ∧
   ts_unify s ts1 ts2 = SOME s' ⇒
   inf_set_tids_subst tids s')
Proof
  ho_match_mp_tac t_unify_strongind>>
  rw[t_unify_eqn]>>
  every_case_tac>>fs[t_ext_s_check_eqn]>>rw[]>>
  TRY (
    Cases_on`ts1` \\ Cases_on`ts2` \\ fs[ts_unify_def, CaseEq"option"] \\ NO_TAC )
  \\ imp_res_tac t_walk_set_tids >>
  rfs[inf_set_tids_subst_def, FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_UPDATE]
  \\ rw[] \\ res_tac
  \\ fs[inf_set_tids_subset_def, inf_set_tids_def, SUBSET_DEF, PULL_EXISTS, MEM_MAP, EVERY_MEM]
  \\ metis_tac[]
QED

Theorem pure_add_constraints_set_tids:
   ∀s1 ls s2.
   t_wfs s1 ∧
   EVERY (inf_set_tids_subset tids) (MAP FST ls) ∧
   EVERY (inf_set_tids_subset tids) (MAP SND ls) ∧
   inf_set_tids_subst tids s1 ∧
   pure_add_constraints s1 ls s2 ⇒
   inf_set_tids_subst tids s2
Proof
  recInduct pure_add_constraints_ind
  \\ rw[pure_add_constraints_def] \\ rw[]
  \\ metis_tac[t_unify_set_tids, t_unify_wfs]
QED

Definition hide_def:
  hide x = x
End

Theorem infer_p_inf_set_tids:
  (!l cenv p st t env st'.
  (infer_p l cenv p st = (Success (t,env), st'))
  ⇒
  prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
  ∧ t_wfs st.subst
  ⇒
  inf_set_tids_subset tids t ∧
  EVERY (inf_set_tids_subset tids o SND) env ∧
  inf_set_tids_subst tids st'.subst) ∧
  (!l cenv ps st ts env st'.
  (infer_ps l cenv ps st = (Success (ts,env), st'))
  ⇒
  prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
  ∧ t_wfs st.subst
  ⇒
  EVERY (inf_set_tids_subset tids) ts ∧
  EVERY (inf_set_tids_subset tids o SND) env ∧
  inf_set_tids_subst tids st'.subst)
Proof
  Q.ISPEC_THEN`_ ∧ _ ∧ inf_set_tids_subst _ _ `(fn th => once_rewrite_tac[th])(GSYM hide_def) >>
  ho_match_mp_tac infer_p_ind >>
  rw [pat_bindings_def, infer_p_def, success_eqns, remove_pair_lem] >>
  simp[inf_set_tids_subset_def,inf_set_tids_def]>>
  TRY(fs[hide_def,prim_tids_def,prim_type_nums_def]>>NO_TAC)
  >- (
    rename1`infer_ps _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def]>>
    fs[prim_tids_def,prim_type_nums_def]>>
    metis_tac[])
  >- (
    rename1`infer_ps _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def,MEM_COUNT_LIST]>>
    rw[]
    >- (
      fs[inf_set_tids_ienv_def,namespaceTheory.nsAll_def]>>
      first_x_assum old_drule>> pairarg_tac>> fs[])
    >-
      fs[inf_set_tids_def]
    >-
      metis_tac[]
    >>
      match_mp_tac pure_add_constraints_set_tids>>
      goal_assum(first_assum o mp_then (Pat`pure_add_constraints`) match_mp_tac)>>
      rw[]
      >-
        metis_tac[infer_p_wfs]
      >- (
        fs[MAP_ZIP,EVERY_MEM,inf_set_tids_subset_def,SUBSET_DEF]>>
        metis_tac[])
      >- (
        fs[MAP_ZIP,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_ZIP,EL_MAP,inf_set_tids_subset_def]>>
        rw[]>>
        match_mp_tac SUBSET_TRANS>>
        specl_args_of_then``infer_type_subst`` inf_set_tids_infer_type_subst_SUBSET assume_tac>>
        asm_exists_tac>>rw[]
        >- (
          fs[inf_set_tids_ienv_def]>>
          imp_res_tac nsLookup_nsAll>>
          rpt(pairarg_tac>>fs[])>>
          fs[EVERY_MEM,inf_set_tids_unconvert,inf_set_tids_subset_def]>>
          metis_tac[EL_MEM])
        >>
        simp[MAP_ZIP,LENGTH_COUNT_LIST,SUBSET_DEF,PULL_EXISTS]>>
        simp[MEM_MAP,PULL_EXISTS,MEM_COUNT_LIST,inf_set_tids_def]))
  >- (
    rename1`infer_p _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def]>>
    fs[prim_tids_def,prim_type_nums_def]>>
    metis_tac[])
  >- ( (* Pas case *)
    rename1`infer_p _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def]>>
    fs[prim_tids_def,prim_type_nums_def]>>
    metis_tac[])
  >- (
    imp_res_tac type_name_check_subst_state >>
    imp_res_tac type_name_check_subst_thm >>
    fs [] >>
    first_x_assum old_drule>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def]>>
    fs[prim_tids_def,prim_type_nums_def]>>
    rw[]
    >-
      metis_tac[]
    >>
     imp_res_tac infer_p_wfs >>
     old_drule (t_unify_set_tids |> CONJUNCT1)>>
     disch_then match_mp_tac>> simp[]>>
    goal_assum(first_assum o mp_then(Pat`t_unify`)mp_tac) >>
    simp[inf_set_tids_subset_def]>>
    CONJ_TAC >- simp[SUBSET_DEF]>>
    match_mp_tac SUBSET_TRANS>>
    specl_args_of_then``infer_type_subst`` inf_set_tids_infer_type_subst_SUBSET assume_tac>>
    asm_exists_tac>>simp[GSYM set_tids_subset_def]>>
    match_mp_tac set_tids_subset_type_name_subst>>
    fs[inf_set_tids_ienv_def,prim_tids_def,prim_type_nums_def,inf_set_tids_unconvert,inf_set_tids_subset_def,set_tids_subset_def])
  >- (
    rename1`infer_p _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    simp[]>>
    strip_tac>>
    rename1`infer_ps _ _ _ _ = (Success vv,_)`>>
    Cases_on`vv`>> first_x_assum old_drule>>
    impl_tac>- (
      imp_res_tac infer_p_wfs>>
      fs[hide_def])>>
    fs[hide_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EVERY_MEM,inf_set_tids_subset_def]>>
    rw[]>>
    metis_tac[])
QED

Theorem constrain_op_set_tids:
   constrain_op l op ts st = (Success t, st') ∧
   EVERY (inf_set_tids_subset tids) ts ∧
   inf_set_tids_subst tids st.subst ∧
   t_wfs st.subst ∧ prim_tids T tids
   ⇒
   inf_set_tids_subset tids t ∧ inf_set_tids_subst tids st'.subst
Proof
  simp[constrain_op_success,success_eqns]
  \\ strip_tac \\ rveq >>
  TRY pairarg_tac
  \\ TRY (Cases_on `uop`)
  \\ fs[success_eqns, inf_set_tids_subset_def, inf_set_tids_def, LET_THM]
  \\ rpt(conj_tac >-(TRY(rename1`word_tc wz`\\Cases_on`wz`\\simp[word_tc_def])\\fs[prim_tids_def,prim_type_nums_def]))
  \\ TRY(TRY(rename1`word_tc wz`\\Cases_on`wz`\\simp[word_tc_def])\\fs[prim_tids_def,prim_type_nums_def]\\NO_TAC)
  \\ imp_res_tac t_unify_wfs
  \\ rpt(t_unify_set_tids |> CONJUNCT1 |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
         |> first_x_assum o mp_then(Pat`t_unify`)(qspec_then ‘tids’ mp_tac))
  \\ fs[inf_set_tids_subset_def, inf_set_tids_def]
  \\ rpt (
    (impl_tac >-(TRY(rename1`word_tc wz`\\Cases_on`wz`\\simp[word_tc_def])
                  \\fs[prim_tids_def,prim_type_nums_def]))
    \\ strip_tac \\ fs[])
  \\ rveq \\ fs[inf_set_tids_def,prim_tids_def, prim_type_nums_def]
  \\ gvs[CaseEq"option",failwith_success,CaseEq"bool",
         st_ex_bind_success,st_ex_return_success,inf_set_tids_def,
         add_constraints_success]
  \\ TRY(rename1`supported_arith a p` \\ Cases_on`a`
         \\ Cases_on ‘p’ using semanticPrimitivesPropsTheory.prim_type_cases \\ gvs[supported_arith_def]
         \\ irule pure_add_constraints_set_tids
         \\ first_x_assum $ irule_at (Pat`pure_add_constraints`)
         \\ gvs[LENGTH_EQ_NUM_compute,REPLICATE_compute]
         \\ gvs[inf_set_tids_subset_def, inf_set_tids_def])
  \\ TRY(rename1`supported_conversion c x`
         \\ Cases_on ‘c’ using semanticPrimitivesPropsTheory.prim_type_cases
         \\ Cases_on ‘x’ using semanticPrimitivesPropsTheory.prim_type_cases \\ gvs[supported_conversion_def])
  \\ rename1`supported_test x p`
  \\ Cases_on`x` \\ Cases_on ‘p’ using semanticPrimitivesPropsTheory.prim_type_cases \\ gvs[supported_test_def]
QED

Theorem infer_e_inf_set_tids:
  (!l cenv p st t st'.
    (infer_e l cenv p st = (Success t, st'))
    ⇒
    prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
    ∧ t_wfs st.subst
    ⇒
    inf_set_tids_subset tids t ∧
    inf_set_tids_subst tids st'.subst) ∧
  (!l cenv ps st ts st'.
    (infer_es l cenv ps st = (Success ts, st'))
    ⇒
    prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
    ∧ t_wfs st.subst
    ⇒
    EVERY (inf_set_tids_subset tids) ts ∧
    inf_set_tids_subst tids st'.subst) ∧
  (!l cenv ps t1 t2 st st'.
    (infer_pes l cenv ps t1 t2 st = (Success (), st'))
    ⇒
    prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
    ∧ inf_set_tids_subset tids t1
    ∧ inf_set_tids_subset tids t2
    ∧ t_wfs st.subst
    ⇒
    inf_set_tids_subst tids st'.subst) ∧
  (!l cenv funs st ts st'.
    (infer_funs l cenv funs st = (Success ts, st'))
    ⇒
    prim_tids T tids ∧ inf_set_tids_ienv tids cenv ∧ inf_set_tids_subst tids st.subst
    ∧ t_wfs st.subst
    ⇒
    EVERY (inf_set_tids_subset tids) ts ∧
    inf_set_tids_subst tids st'.subst)
Proof
  Q.ISPEC_THEN`EVERY _ _ ∧ _ `(fn th => once_rewrite_tac[th])(GSYM hide_def)
  \\ Q.ISPEC_THEN`inf_set_tids_subset _ _ ∧ _ `(fn th => once_rewrite_tac[th])(GSYM hide_def)
  \\ ho_match_mp_tac infer_e_ind >>
  rw [pat_bindings_def, infer_e_def, success_eqns, remove_pair_lem] >>
  fs[inf_set_tids_subset_def,inf_set_tids_def]>>
  TRY(fs[prim_tids_def,prim_type_nums_def,hide_def]>> NO_TAC)>>
  rpt(first_x_assum old_drule) >> rw[] >>
  fs[hide_def] >>
  imp_res_tac infer_e_wfs
  \\ rpt(qpat_x_assum`∀x. _`kall_tac)
  \\ imp_res_tac t_unify_wfs
  \\ rpt(qpat_x_assum`∀x. _`kall_tac)
  \\ fs[GSYM CONJ_ASSOC]
  \\ rfs[] \\ fs[]
  \\ TRY(
    irule (CONJUNCT1 t_unify_set_tids)
    \\ rw[inf_set_tids_subset_def]
    \\ goal_assum(first_assum o mp_then(Pat`t_unify`)mp_tac)
    \\ simp[]
    \\ simp[inf_set_tids_def]
    \\ TRY(fs[prim_tids_def,prim_type_nums_def] \\ NO_TAC))
  \\ rpt(conj_tac >- (fs[prim_tids_def,prim_type_nums_def]))
  \\ TRY(fs[prim_tids_def,prim_type_nums_def] \\ NO_TAC)
  \\ TRY (
    match_mp_tac SUBSET_TRANS
    \\ specl_args_of_then``infer_deBruijn_subst`` inf_set_tids_infer_deBruijn_subst_SUBSET assume_tac
    \\ asm_exists_tac \\ simp[]
    \\ fs[inf_set_tids_ienv_def]
    \\ imp_res_tac nsLookup_nsAll
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[inf_set_tids_subset_def]
    \\ fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP,MEM_COUNT_LIST,inf_set_tids_def]
    \\ NO_TAC)
  \\ TRY (
    rfs[inf_set_tids_ienv_def]
    \\ first_x_assum match_mp_tac
    \\ match_mp_tac nsAll_nsBind
    \\ fs[inf_set_tids_subset_def,inf_set_tids_def]
    \\ NO_TAC)
  \\ TRY (
    fs[EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,
       AND_IMP_INTRO,CONJ_COMM,inf_set_tids_subset_def]
    \\ NO_TAC)
  >- (
    first_assum (
      mp_then (Pat`pure_add_constraints`) (qspec_then ‘tids’ mp_tac)
              pure_add_constraints_set_tids
    )
    \\ simp[MAP_ZIP,LENGTH_COUNT_LIST,MAP_MAP_o,o_DEF,inf_set_tids_def]
    \\ rfs[inf_set_tids_ienv_def]
    \\ imp_res_tac nsLookup_nsAll
    \\ rpt(pairarg_tac \\ fs[])
    \\ simp[SUBSET_DEF,MEM_MAP,PULL_EXISTS]
    \\ disch_then match_mp_tac
    \\ simp[EVERY_MAP]
    \\ fs[EVERY_MEM]
    \\ rw[]
    \\ fs[inf_set_tids_subset_def]
    \\ match_mp_tac SUBSET_TRANS
    \\ specl_args_of_then``infer_type_subst`` inf_set_tids_infer_type_subst_SUBSET assume_tac
    \\ asm_exists_tac \\ simp[]
    \\ fs[MAP_ZIP,LENGTH_COUNT_LIST]
    \\ fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP,MEM_COUNT_LIST,
          inf_set_tids_def,inf_set_tids_unconvert]
    \\ metis_tac[])
  >- (
    old_drule constrain_op_set_tids
    \\ simp[inf_set_tids_subset_def] )
  >- (
    irule (CONJUNCT1 t_unify_set_tids)
    \\ rw[inf_set_tids_subset_def]
    \\ goal_assum(first_assum o mp_then(Pat`t_unify`)mp_tac)
    \\ simp[]
    \\ simp[inf_set_tids_def]
    \\ fs [inf_set_tids_subset_def]
    \\ conj_tac >- (fs[prim_tids_def,prim_type_nums_def] \\ NO_TAC)
    \\ irule (CONJUNCT1 t_unify_set_tids)
    \\ rw[inf_set_tids_subset_def]
    \\ goal_assum(first_assum o mp_then(Pat`t_unify`)mp_tac)
    \\ simp[]
    \\ simp[inf_set_tids_def]
    \\ fs[prim_tids_def,prim_type_nums_def] \\ NO_TAC )
  >- (
    rpt(t_unify_set_tids |> CONJUNCT1 |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
        |> first_x_assum o mp_then(Pat`t_unify`)(qspec_then ‘tids’ mp_tac))
    \\ simp[inf_set_tids_subset_def,inf_set_tids_def]
    \\ impl_tac >- fs[prim_tids_def,prim_type_nums_def]
    \\ strip_tac \\ fs[] )
  >- ( fs[inf_set_tids_def] )
  >- (
    first_x_assum match_mp_tac
    \\ fs[inf_set_tids_ienv_def]
    \\ match_mp_tac nsAll_nsOptBind
    \\ fs[]
    \\ Cases_on`x` \\ fs[]
    \\ fs[inf_set_tids_subset_def] )
  >- (
    first_x_assum match_mp_tac
    \\ imp_res_tac pure_add_constraints_wfs \\ fs[]
    \\ conj_asm1_tac
    >- (
      fs[inf_set_tids_ienv_def]
      \\ match_mp_tac nsAll_nsAppend
      \\ fs[]
      \\ match_mp_tac nsAll_alist_to_ns
      \\ fs[EVERY_MAP,MAP2_MAP,MAP_MAP_o,LENGTH_COUNT_LIST,
            inf_set_tids_subset_def,UNCURRY]
      \\ fs[EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,EL_MAP,PULL_EXISTS,inf_set_tids_def] )
    \\ fs[]
    \\ irule pure_add_constraints_set_tids
    \\ goal_assum(first_assum o mp_then (Pat`pure_add_constraints`) mp_tac)
    \\ simp[MAP_ZIP,LENGTH_COUNT_LIST]
    \\ simp[EVERY_MAP,inf_set_tids_subset_def,inf_set_tids_def] )
  >- (
    imp_res_tac type_name_check_subst_state >>
    imp_res_tac type_name_check_subst_thm >>
    fs [] >>
    match_mp_tac SUBSET_TRANS
    \\ specl_args_of_then``infer_type_subst`` inf_set_tids_infer_type_subst_SUBSET assume_tac
    \\ asm_exists_tac
    \\ rw[]
    \\ fs[inf_set_tids_ienv_def]
    \\ simp[GSYM set_tids_subset_def]
    \\ match_mp_tac set_tids_subset_type_name_subst
    \\ fs[inf_set_tids_unconvert,inf_set_tids_subset_def,set_tids_subset_def] )
  >- (
    first_x_assum match_mp_tac >>
    rpt(t_unify_set_tids |> CONJUNCT1 |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
        |> first_x_assum o mp_then(Pat`t_unify`)(qspec_then ‘tids’ mp_tac))
    \\ simp[inf_set_tids_subset_def,inf_set_tids_def]
    \\ rename1`infer_p _ _ _ _ = (Success pp,_)`
    \\ Cases_on`pp`
    \\ imp_res_tac infer_p_wfs
    \\ fs[]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ first_x_assum irule
    \\ conj_tac
    >- (
      fs[inf_set_tids_ienv_def]
      \\ match_mp_tac nsAll_nsAppend
      \\ fs[]
      \\ match_mp_tac nsAll_alist_to_ns
      \\ fs[inf_set_tids_subset_def,EVERY_MAP,UNCURRY]
      \\ imp_res_tac infer_p_inf_set_tids
      \\ rfs[o_DEF,inf_set_tids_subset_def,inf_set_tids_ienv_def] )
    \\ first_x_assum irule
    \\ imp_res_tac infer_p_inf_set_tids
    \\ rfs[inf_set_tids_subset_def] )
  >- (
    conj_tac >- (
      fsrw_tac[DNF_ss][]
      \\ first_x_assum match_mp_tac
      \\ fs[inf_set_tids_ienv_def]
      \\ match_mp_tac nsAll_nsBind
      \\  fs[inf_set_tids_subset_def, inf_set_tids_def] )
    \\ first_x_assum irule
    \\ fsrw_tac[DNF_ss][]
    \\ first_x_assum match_mp_tac
    \\ fs[inf_set_tids_ienv_def]
    \\ match_mp_tac nsAll_nsBind
    \\ fs[inf_set_tids_subset_def, inf_set_tids_def] )
QED

Theorem generalise_inf_set_tids:
   (∀d a b c e f g. generalise a b c d = (e,f,g) ⇒
                    inf_set_tids g = inf_set_tids d) ∧
   (∀d a b c e f g. generalise_list a b c d = (e,f,g) ⇒
                    EVERY2 (inv_image $= inf_set_tids) d g)
Proof
  Induct
  \\ rw[generalise_def, inf_set_tids_def]
  \\ rw[inf_set_tids_def]
  \\ every_case_tac \\ rw[] \\ fs[inf_set_tids_def]
  \\ pairarg_tac \\ fs[] \\ rw[inf_set_tids_def]
  \\ TRY(pairarg_tac \\ fs[]) \\ rw[]
  \\ res_tac \\ fs[]
  \\ AP_TERM_TAC
  \\ fs[LIST_REL_EL_EQN, EXTENSION,MEM_MAP,PULL_EXISTS,MEM_EL]
  \\ metis_tac[]
QED

Theorem start_type_id_prim_tids_count:
   start_type_id ≤ n ⇒ prim_tids T (count n)
Proof
  rw[prim_tids_def,prim_type_nums_def,start_type_id_def]
  \\ EVAL_TAC \\ fs[]
QED

Theorem inf_set_tids_subst_FEMPTY[simp]:
   inf_set_tids_subst tids FEMPTY
Proof
  EVAL_TAC \\ rw[]
QED

Theorem build_ctor_tenv_FOLDR:
   ∀tenvT tds ids.
     LENGTH tds = LENGTH ids ⇒
     build_ctor_tenv tenvT tds ids =
       FOLDR (combin$C nsAppend) (alist_to_ns [])
       (MAP (alist_to_ns o REVERSE)
          (MAP2 (λ(tvs,tn,ctors) id. (MAP (λ(cn,ts). (cn,tvs,MAP (type_name_subst tenvT) ts,id)) ctors))
              tds ids))
Proof
  recInduct build_ctor_tenv_ind
  \\ rw[build_ctor_tenv_def]
QED

Theorem build_ctor_tenv_FOLDL:
   ∀tenvT tds ids.
     LENGTH tds = LENGTH ids ⇒
     build_ctor_tenv tenvT tds ids =
       FOLDL nsAppend (alist_to_ns [])
       (REVERSE
       (MAP (alist_to_ns o REVERSE)
          (MAP2 (λ(tvs,tn,ctors) id. (MAP (λ(cn,ts). (cn,tvs,MAP (type_name_subst tenvT) ts,id)) ctors))
              tds ids)))
Proof
  simp[FOLDL_FOLDR_REVERSE]
  \\ recInduct build_ctor_tenv_ind
  \\ rw[build_ctor_tenv_def]
QED

Theorem nsMap_FOLDL_nsAppend:
   ∀ls ns. nsMap f (FOLDL nsAppend ns ls) =
   FOLDL nsAppend (nsMap f ns) (MAP (nsMap f) ls)
Proof
  Induct \\ rw[] \\ rw[nsMap_nsAppend]
QED

Theorem nsAll_FOLDL_nsAppend:
   ∀ls ns.
   nsAll P ns ∧ EVERY (nsAll P) ls
   ⇒ nsAll P (FOLDL nsAppend ns ls)
Proof
  Induct \\ rw[]
  \\ first_x_assum match_mp_tac \\ fs[]
  \\ match_mp_tac nsAll_nsAppend \\ fs[]
QED

Theorem infer_d_inf_set_tids:
   (∀d ienv st ienv' st'.
     infer_d ienv d st = (Success ienv', st') ∧
     start_type_id ≤ st.next_id ∧
     inf_set_tids_ienv (count st.next_id) ienv
     ⇒
     inf_set_tids_ienv (count st'.next_id) ienv') ∧
  (∀ds ienv st ienv' st'.
     infer_ds ienv ds st = (Success ienv', st') ∧
     start_type_id ≤ st.next_id ∧
     inf_set_tids_ienv (count st.next_id) ienv
     ⇒
     inf_set_tids_ienv (count st'.next_id) ienv')
Proof
  Induct
  \\ rw[infer_d_def, success_eqns]
  \\ rpt(pairarg_tac \\ fs[success_eqns]) \\ rw[]
  \\ rpt(first_x_assum old_drule \\ rw[])
  \\ imp_res_tac generalise_list_length
  \\ imp_res_tac start_type_id_prim_tids_count
  \\ fs[inf_set_tids_ienv_def, ZIP_MAP, MAP_MAP_o, o_DEF]
  \\ fs[inf_set_tids_subset_def, inf_set_tids_unconvert, LENGTH_COUNT_LIST]
  \\ fs[GSYM set_tids_subset_def]
  \\ TRY (
    match_mp_tac nsAll_alist_to_ns
    \\ simp[EVERY_MAP,every_zip_snd]
    \\ imp_res_tac generalise_inf_set_tids
    \\ fs[GSYM LIST_REL_MAP_inv_image]
    \\ simp[GSYM (Q.ISPEC`inf_set_tids`(CONV_RULE SWAP_FORALL_CONV EVERY_MAP))]
    \\ pop_assum(assume_tac o SYM)
    \\ simp[]
    \\ simp[EVERY_MAP]
    \\ old_drule(GEN_ALL(CONJUNCT1 infer_p_inf_set_tids))
    \\ disch_then old_drule
    \\ simp[inf_set_tids_ienv_def,inf_set_tids_subset_def,inf_set_tids_unconvert,GSYM set_tids_subset_def]
    \\ old_drule(GEN_ALL(CONJUNCT1 infer_e_inf_set_tids))
    \\ disch_then old_drule
    \\ simp[inf_set_tids_ienv_def,inf_set_tids_subset_def,inf_set_tids_unconvert,GSYM set_tids_subset_def]
    \\ fs[init_state_def] \\ rveq \\ fs[]
    \\ strip_tac
    \\ old_drule(GEN_ALL(CONJUNCT1 infer_e_wfs))
    \\ fs[] \\ rw[]
    \\ old_drule(GEN_ALL(CONJUNCT1 infer_p_wfs))
    \\ disch_then old_drule \\ strip_tac
    \\ old_drule(GEN_ALL(CONJUNCT1 t_unify_set_tids))
    \\ disch_then old_drule
    \\ fs[inf_set_tids_subset_def]
    \\ disch_then(first_assum o mp_then (Pat`t_unify`)mp_tac)
    \\ fs[] \\ strip_tac
    \\ old_drule(GEN_ALL(t_unify_wfs))
    \\ disch_then old_drule \\ strip_tac
    \\ old_drule (GEN_ALL t_walkstar_set_tids)
    \\ disch_then old_drule
    \\ fs[inf_set_tids_subset_def]
    \\ fs[EVERY_MEM] \\ rw[]
    \\ res_tac
    \\ fs[inf_set_tids_subset_def]
    \\ res_tac
    \\ imp_res_tac infer_e_next_id_const
    \\ imp_res_tac infer_p_next_id_const
    \\ fs[init_infer_state_def] )
  >- (
    match_mp_tac nsAll_alist_to_ns
    \\ simp[MAP2_MAP, UNCURRY, EVERY_MAP]
    \\ simp[every_zip_snd]
    \\ imp_res_tac generalise_inf_set_tids
    \\ fs[GSYM LIST_REL_MAP_inv_image]
    \\ simp[GSYM (Q.ISPEC`inf_set_tids`(CONV_RULE SWAP_FORALL_CONV EVERY_MAP))]
    \\ pop_assum(assume_tac o SYM)
    \\ simp[]
    \\ simp[EVERY_MAP]
    \\ simp[EVERY_MEM,MEM_COUNT_LIST]
    \\ rw[GSYM inf_set_tids_subset_def]
    \\ match_mp_tac (t_walkstar_set_tids|> SIMP_RULE std_ss [])
    \\ simp[inf_set_tids_subset_def,inf_set_tids_def]
    \\ imp_res_tac infer_e_wfs
    \\ imp_res_tac pure_add_constraints_wfs
    \\ fs[init_state_def,init_infer_state_def] \\ rw[] \\ rfs[]
    \\ irule pure_add_constraints_set_tids
    \\ goal_assum(first_assum o mp_then (Pat`pure_add_constraints`) mp_tac)
    \\ simp[MAP_ZIP,LENGTH_COUNT_LIST]
    \\ simp[EVERY_MAP,inf_set_tids_subset_def,inf_set_tids_def]
    \\ match_mp_tac (el 4 (CONJUNCTS infer_e_inf_set_tids) |> SIMP_RULE std_ss [AND_IMP_INTRO] )
    \\ asm_exists_tac \\ fs[]
    \\ imp_res_tac infer_e_next_id_const
    \\ CONJ_TAC >-
      fs[prim_tids_def,prim_type_nums_def]
    \\ fs[inf_set_tids_ienv_def]
    \\ rw[] >>
    TRY(match_mp_tac nsAll_nsAppend >> rw[] ) >>
    TRY(qpat_x_assum`_ _ ienv.inf_t` mp_tac>>  match_mp_tac nsAll_mono)>>
    TRY(qpat_x_assum`_ _ ienv.inf_c` mp_tac>>  match_mp_tac nsAll_mono)>>
    TRY(qpat_x_assum`_ _ ienv.inf_v` mp_tac>>  match_mp_tac nsAll_mono)>>
    fs[inf_set_tids_unconvert,inf_set_tids_subset_def,set_tids_subset_def]>>
    match_mp_tac nsAll_alist_to_ns >>
    simp[MAP2_MAP,LENGTH_COUNT_LIST,EVERY_MAP,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_ZIP]>>
    rw[]>> rpt (pairarg_tac >> fs[])>> rw[]>>
    simp[EL_MAP,LENGTH_COUNT_LIST,inf_set_tids_def])
  >- (
    rw[]
    >- (
      match_mp_tac nsAll_alist_to_ns>>fs[n_fresh_id_def]>>rw[]>>
      simp[MAP2_MAP,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_ZIP]>>
      rw[]>>
      rpt(pairarg_tac>>fs[])>>rw[]>>
      simp[set_tids_subset_def,set_tids_def,SUBSET_DEF,MEM_MAP]>>rw[]>>
      fs[set_tids_def])
    >>
      fs[n_fresh_id_def] >> rw[]>>
      simp[build_ctor_tenv_FOLDL]
      \\ match_mp_tac nsAll_FOLDL_nsAppend
      \\ simp[EVERY_REVERSE]
      \\ simp[MAP_MAP_o, o_DEF, UNCURRY, MAP2_MAP, EVERY_MAP]
      \\ simp[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_GENLIST]
      \\ rw[]
      \\ match_mp_tac nsAll_alist_to_ns
      \\ simp[EVERY_REVERSE, EVERY_MAP, UNCURRY, MEM_MAP, PULL_EXISTS]
      \\ simp[EVERY_MEM] \\ rw[]
      \\ match_mp_tac set_tids_subset_type_name_subst
      \\ conj_tac
      >- simp[start_type_id_prim_tids_count]
      \\ match_mp_tac nsAll_nsAppend
      \\ conj_tac
      >- (
        match_mp_tac nsAll_alist_to_ns
        \\ simp[EVERY_MAP, UNCURRY, set_tids_subset_def, set_tids_def, MAP_MAP_o, o_DEF]
        \\ simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, every_zip_snd, EVERY_GENLIST] )
      \\ irule nsAll_mono
      \\ HINT_EXISTS_TAC
      \\ simp[set_tids_subset_def, SUBSET_DEF, UNCURRY]
      \\ rw[]
      \\ res_tac
      \\ rw[] )
  >- (
    imp_res_tac type_name_check_subst_state >>
    imp_res_tac type_name_check_subst_thm >>
    fs [] >>
    match_mp_tac set_tids_subset_type_name_subst
    \\ fs[] )
  >- (
    imp_res_tac type_name_check_subst_state >>
    imp_res_tac type_name_check_subst_thm >>
    fs [] >>
    fs[EVERY_MAP, set_tids_subset_type_name_subst]
    \\ fs[start_type_id_def] \\ EVAL_TAC \\ fs[] )
  >- ( fs[lift_ienv_def] )
  \\ ( (* cases with two components (x::xs and [Dlocal lds ds]) *)
    qpat_x_assum` _ ⇒ _` mp_tac>>
    imp_res_tac infer_d_next_id_mono>>
    impl_tac
    >- (
      fs[extend_dec_ienv_def]>>
      dep_rewrite.DEP_REWRITE_TAC [nsAll_nsAppend]>>fs[]>>
      rw[]>>
      TRY(qpat_x_assum`_ _ ienv.inf_t` mp_tac>>  match_mp_tac nsAll_mono)>>
      TRY(qpat_x_assum`_ _ ienv.inf_c` mp_tac>>  match_mp_tac nsAll_mono)>>
      TRY(qpat_x_assum`_ _ ienv.inf_v` mp_tac>>  match_mp_tac nsAll_mono)>>
      rw[]>>TRY(pairarg_tac>>fs[])>>
      fs[set_tids_subset_def,SUBSET_DEF,EVERY_MEM]>>
      rw[]>>
      first_x_assum old_drule>>fs[]>>
      disch_then old_drule>>fs[])
    >>
      strip_tac>>
      fs[extend_dec_ienv_def]>>
      dep_rewrite.DEP_REWRITE_TAC [nsAll_nsAppend]>>fs[]>>
      rw[]>>
      TRY(qpat_x_assum`_ _ ienv''.inf_t` mp_tac>>  match_mp_tac nsAll_mono)>>
      TRY(qpat_x_assum`_ _ ienv''.inf_c` mp_tac>>  match_mp_tac nsAll_mono)>>
      TRY(qpat_x_assum`_ _ ienv''.inf_v` mp_tac>>  match_mp_tac nsAll_mono)>>
      rw[]>>TRY(pairarg_tac>>fs[])>>
      fs[set_tids_subset_def,SUBSET_DEF,EVERY_MEM]>>
      rw[]>>
      first_x_assum old_drule>>fs[]>>
      disch_then old_drule>>fs[])
QED

Theorem infer_d_wfs:
   (∀d ienv st ienv' st'.
     infer_d ienv d st = (Success ienv', st') ∧
     t_wfs st.subst
     ⇒
     t_wfs st'.subst) ∧
  (∀ds ienv st ienv' st'.
     infer_ds ienv ds st = (Success ienv', st') ∧
     t_wfs st.subst
     ⇒
     t_wfs st'.subst)
Proof
  Induct
  \\ rw[infer_d_def, success_eqns, init_state_def]
  \\ rpt(pairarg_tac \\ fs[success_eqns])
  \\ rw[] >>
  imp_res_tac type_name_check_subst_state >>
  imp_res_tac type_name_check_subst_thm >>
  fs []
  \\ imp_res_tac infer_e_wfs \\ fs[]
  \\ imp_res_tac infer_p_wfs \\ fs[]
  \\ imp_res_tac t_unify_wfs \\ fs[]
  \\ imp_res_tac pure_add_constraints_wfs
  \\ fs[n_fresh_id_def] \\ rw[]
  \\ metis_tac[]
QED
