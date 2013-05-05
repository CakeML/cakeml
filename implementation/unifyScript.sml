open preamble finite_mapTheory optionTheory LibTheory AstTheory; 
open unifPropsTheory unifDefTheory walkTheory walkstarTheory collapseTheory;

val option_bind_thm = Q.prove (
`!x f. OPTION_BIND x f =
  case x of
    | NONE => NONE
    | SOME y => f y`,
cases_on `x` >>
rw [OPTION_BIND_def]);

val I_o_f = Q.prove (
`!m. I o_f m = m`,
rw [GSYM fmap_EQ_THM]);

val _ = new_theory "unify";

val _ = Hol_datatype `
infer_t = 
    Infer_Tvar_db of num
  | Infer_Tapp of infer_t list => tc0
  | Infer_Tuvar of num`;

val infer_t_size_def = fetch "-" "infer_t_size_def";
val infer_t_induction = fetch "-" "infer_t_induction";

val _ = Hol_datatype `
atom = 
    TC_tag of tc0
  | DB_tag of num
  | Tapp_tag
  | Null_tag`;

val encode_infer_t_def = Define `
(encode_infer_t (Infer_Tvar_db n) =
  Const (DB_tag n)) ∧
(encode_infer_t (Infer_Tapp ts tc) =
  Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) (encode_infer_ts ts))) ∧
(encode_infer_t (Infer_Tuvar n) =
  Var n) ∧
(encode_infer_ts [] =
  Const Null_tag) ∧
(encode_infer_ts (t::ts) =
  Pair (encode_infer_t t) (encode_infer_ts ts))`;

val decode_infer_t_def = Define `
(decode_infer_t (Var n) =
  Infer_Tuvar n) ∧
(decode_infer_t (Const (DB_tag n)) =
  Infer_Tvar_db n) ∧
(decode_infer_t (Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) s)) =
  Infer_Tapp (decode_infer_ts s) tc) ∧
(decode_infer_ts (Const Null_tag) =
  []) ∧ 
(decode_infer_ts (Pair s1 s2) =
  decode_infer_t s1 :: decode_infer_ts s2)`;

val decode_left_inverse = Q.prove (
`(!t. decode_infer_t (encode_infer_t t) = t) ∧
 (!ts. decode_infer_ts (encode_infer_ts ts) = ts)`,
Induct >>
rw [encode_infer_t_def, decode_infer_t_def]);

val decode_left_inverse_I = Q.prove (
`decode_infer_t o encode_infer_t = I`,
rw [FUN_EQ_THM] >>
metis_tac [decode_left_inverse]);

val t_wfs_def = Define `
t_wfs s = wfs (encode_infer_t o_f s)`;

val t_vwalk_def = Define `
t_vwalk s v = decode_infer_t (vwalk (encode_infer_t o_f s) v)`;

val t_vwalk_ind' = Q.prove (
`!s'. t_wfs s' ⇒
   ∀P. 
     (∀v. (∀v1 u. (FLOOKUP s' v = SOME v1) ∧ (v1 = Infer_Tuvar u) ⇒ P u) ⇒ P v) ⇒
     ∀v. P v`,
ntac 4 STRIP_TAC >>
fs [t_wfs_def] >>
imp_res_tac (DISCH_ALL vwalk_ind) >>
pop_assum ho_match_mp_tac >>
rw [] >>
qpat_assum `∀v. (∀u. (FLOOKUP s' v = SOME (Infer_Tuvar u)) ⇒ P u) ⇒ P v` ho_match_mp_tac >>
rw [] >>
qpat_assum `∀u. Q u ⇒ P u` ho_match_mp_tac >>
rw [FLOOKUP_o_f, option_map_def, encode_infer_t_def]);

val t_vwalk_ind = save_thm("t_vwalk_ind", (UNDISCH o Q.SPEC `s`) t_vwalk_ind')

val t_vwalk_eqn = Q.store_thm ("t_vwalk_eqn",
`!s. 
  t_wfs s ⇒
  (!v. 
    t_vwalk s v =
    case FLOOKUP s v of
      | NONE => Infer_Tuvar v
      | SOME (Infer_Tuvar u) => t_vwalk s u
      | SOME (Infer_Tapp ts tc') => Infer_Tapp ts tc'
      | SOME (Infer_Tvar_db n) => Infer_Tvar_db n)`,
rw [t_vwalk_def] >>
full_case_tac >>
rw [] >>
fs [t_wfs_def] >|
[rw [Once vwalk_def] >>
     full_case_tac >>
     rw [decode_infer_t_def] >>
     fs [FLOOKUP_o_f, option_map_def] >>
     cases_on `FLOOKUP s v` >>
     fs [],
 rw [Once vwalk_def, FLOOKUP_o_f, option_map_def] >>
     cases_on `x` >>
     rw [encode_infer_t_def, decode_infer_t_def, decode_left_inverse]]);

val t_walk_def = Define `
t_walk s t = decode_infer_t (walk (encode_infer_t o_f s) (encode_infer_t t))`;

val t_walk_eqn = Q.store_thm ("t_walk_eqn",
`(!s v. t_walk s (Infer_Tuvar v) = t_vwalk s v) ∧
 (!s ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) ∧
 (!s n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)`,
rw [t_walk_def, walk_def, t_vwalk_def, encode_infer_t_def,
    decode_infer_t_def, decode_left_inverse]);

val t_oc_def = Define `
t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v`;

(*
val t_vars_def = Define `
t_vars t = vars (encode_infer_t t)`;

val t_oc_ind' = Q.prove (
`∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. oc (FMAP_MAP2 (λ(n,t). encode_infer_t t) s) a0 a1 ⇒ !a0'. (a0 = encode_infer_t a0') ⇒ oc' a0' a1)`,
NTAC 3 STRIP_TAC >>
ho_match_mp_tac oc_ind >>
rw [] >|
[qpat_assum `∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v` ho_match_mp_tac >>
     fs [t_vars_def, FMAP_MAP2_THM],
 qpat_assum `∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v` ho_match_mp_tac >>
     rw [t_vars_def] >>
     qexists_tac `u` >>
     rw [] >>
     pop_assum ho_match_mp_tac >>
     rw [encode_vwalk]]);

val t_oc_ind = Q.store_thm ("t_oc_ind",
`∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. t_oc s a0 a1 ⇒ oc' a0 a1)`,
rw [t_oc_def] >>
metis_tac [t_oc_ind', FMAP2_FMAP2, FMAP2_id, decode_left_inverse]);
*)

val encode_vwalk = Q.prove (
`!s. t_wfs s ⇒ !u. vwalk (encode_infer_t o_f s) u = encode_infer_t (t_vwalk s u)`,
NTAC 2 STRIP_TAC >>
ho_match_mp_tac t_vwalk_ind >>
rw [] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
rw [Once vwalk_def] >>
rw [Once t_vwalk_eqn, FLOOKUP_o_f] >>
cases_on `FLOOKUP s u` >>
rw [option_map_def, encode_infer_t_def] >>
cases_on `x` >>
rw [encode_infer_t_def]);

val t_oc_eqn_help = Q.prove (
`!l v s.
  oc (encode_infer_t o_f s) (encode_infer_ts l) v ⇔
  EXISTS (λt. oc (encode_infer_t o_f s) (encode_infer_t t) v) l`,
induct_on `l` >>
rw [encode_infer_t_def]);

val t_oc_eqn = Q.store_thm ("t_oc_eqn",
`!s. t_wfs s ⇒
  !t v. t_oc s t v =
    case t_walk s t of
      | Infer_Tuvar u => v = u
      | Infer_Tapp ts tc' => EXISTS (\t. t_oc s t v) ts
      | Infer_Tvar_db n => F`,
rw [t_oc_def] >>
`wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
rw [Once oc_walking, t_walk_def] >>
cases_on `t` >>
rw [walk_def, encode_infer_t_def, decode_infer_t_def, decode_left_inverse,
    encode_vwalk, t_oc_eqn_help] >>
cases_on `t_vwalk s n` >>
rw [encode_infer_t_def, t_oc_eqn_help]);

val t_ext_s_check_def = Define `
t_ext_s_check s v t =
  option_map 
    ((o_f) decode_infer_t)
    (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;

val t_ext_s_check_eqn = Q.store_thm ("t_ext_s_check_eqn",
`!s v t.
  t_ext_s_check s v t = if t_oc s t v then NONE else SOME (s |+ (v,t))`,
rw [t_ext_s_check_def, t_oc_def, option_map_def, decode_left_inverse_I,
    I_o_f, decode_left_inverse] >>
metis_tac [FUPDATE_PURGE]);

val t_unify_def = Define `
t_unify s t1 t2 = 
  option_map 
    ((o_f) decode_infer_t)
    (unify (encode_infer_t o_f s) (encode_infer_t t1) (encode_infer_t t2))`;

val ts_unify_def = Define `
(ts_unify s [] [] = SOME s) ∧
(ts_unify s (t1::ts1) (t2::ts2) =
  case t_unify s t1 t2 of
   | NONE => NONE
   | SOME s' => ts_unify s' ts1 ts2) ∧
(ts_unify s _ _ = NONE)`;

val encode_walk = prove(
  ``∀s. t_wfs s ⇒
      ∀t. walk (encode_infer_t o_f s) (encode_infer_t t) = encode_infer_t (t_walk s t)``,
  rw[walk_def] >>
  imp_res_tac encode_vwalk >>
  fs[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[t_walk_def,decode_left_inverse] >>
  metis_tac[decode_left_inverse])

val encode_pair_cases = prove(
  ``(∀t t1 t2.
    (encode_infer_t t = Pair t1 t2) ⇒
      ((t1 = Const Tapp_tag) ∧
       (∃tc ts. t2 = Pair (Const (TC_tag tc)) (encode_infer_ts ts))))``,
  Cases >> rw[encode_infer_t_def] >>
  PROVE_TAC[])

(* TODO: move to examples/unification *)
val unify_same_lemma = prove(
  ``∀s t1 t2. wfs s ∧ (t1 = t2) ⇒ (unify s t1 t2 = SOME s)``,
  ho_match_mp_tac unify_ind >> rw[] >>
  pop_assum mp_tac >>
  simp_tac std_ss [Once unify_def] >>
  Cases_on `walk s t1` >> rw[])
val unify_same = store_thm("unify_same",
 ``∀s. wfs s ⇒ ∀t. unify s t t = SOME s``,
 PROVE_TAC[unify_same_lemma])
val _ = export_rewrites["unify_same"]

val option_map_OPTION_MAP = store_thm("option_map_OPTION_MAP",
  ``option_map = OPTION_MAP``,
  simp[FUN_EQ_THM] >>
  gen_tac >> Cases >>
  rw[option_map_def])

val encode_unify_lemma = Q.prove (
`!s t1 t2 s' t1' t2'.
  (s = (encode_infer_t o_f s')) ∧
  (((t1 = encode_infer_t t1') ∧ (t2 = encode_infer_t t2')) ∨
   (∃c. (t1 = Const c) ∧ (t2 = Const c) ∧ (t1' = t2')) ∨
   (∃c ts1 ts2.
     (t1 = Pair (Const c) (encode_infer_ts ts1)) ∧
     (t2 = Pair (Const c) (encode_infer_ts ts2)) ∧
     (t1' = Infer_Tapp ts1 ARB) ∧
     (t2' = Infer_Tapp ts2 ARB)) ∨
   (∃ts1 ts2.
      (t1 = encode_infer_ts ts1) ∧
      (t2 = encode_infer_ts ts2) ∧
      (t1' = Infer_Tapp ts1 ARB) ∧
      (t2' = Infer_Tapp ts2 ARB))) ∧
  t_wfs s' ⇒
  (unify s t1 t2
   =
   option_map ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
ho_match_mp_tac unify_ind >>
simp[] >>
rw [t_unify_def] >>
fs[t_wfs_def] >>
qmatch_assum_abbrev_tac `wfs es` >>
TRY(simp[option_map_def] >>
  rw[GSYM fmap_EQ_THM,Abbr`es`,decode_left_inverse] >>
  NO_TAC) >>
  (*
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def,SimpRHS] >>
  rw[option_map_def] >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  simp[Once unify_def] >>
  rw[] >>
  first_x_assum(qspecl_then[`s'`,`t1a`,`t2a`]mp_tac) >>
  rw[option_map_def] >> fs[] >>
  `wfs sx` by (PROVE_TAC[unify_unifier]) >>
  qabbrev_tac`dx = decode_infer_t o_f sx` >>
  first_x_assum(qspecl_then[`dx`,`t1d`,`t2d`]mp_tac) >>
  `sx = encode_infer_t o_f dx` by rw[Abbr`dx`] >>
  pop_assum (SUBST1_TAC o  SYM) >>
  simp[] >>
  rw[option_map_def] >>
  NO_TAC ) >>
  *)
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def,SimpRHS] >>
  simp[Once unify_def,SimpRHS] >>
  rw[option_map_def] >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  Cases_on `ts1` >> Cases_on `ts2` >> simp[encode_infer_t_def,Once unify_def] >- (
    rw[] >>
    rw[Abbr`es`,GSYM fmap_EQ_THM,decode_left_inverse] ) >>
  rw[] >>
  fs[encode_infer_t_def] >>
  first_x_assum(qspecl_then[`s'`,`h`,`h'`]mp_tac) >>
  simp[option_map_def] >>
  rw[] >>
  `wfs sx` by (PROVE_TAC[unify_unifier]) >>
  qabbrev_tac`dx = decode_infer_t o_f sx` >>
  `sx = encode_infer_t o_f dx` by rw[Abbr`dx`] >>
  first_x_assum(qspecl_then[`dx`,`Infer_Tapp t ARB`,`Infer_Tapp t' ARB`]mp_tac) >>
  pop_assum (SUBST1_TAC o  SYM) >>
  simp[] >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[option_map_def] >>
  NO_TAC ) >>
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def,SimpRHS] >>
  simp[Once unify_def,SimpRHS] >>
  rw[option_map_def] >>
  BasicProvers.CASE_TAC >>
  first_x_assum(qspecl_then[`s'`,`h`,`h'`]kall_tac) >>
  first_x_assum(qspecl_then[`s'`,`Infer_Tapp ts1 ARB`,`Infer_Tapp ts2 ARB`]mp_tac) >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[option_map_def] >>
  NO_TAC ) >>
qmatch_abbrev_tac `unify es e1 e2 = X` >>
qunabbrev_tac`X`>>
Cases_on `unify es e1 e2` >>
rw[option_map_def] >>
qsuff_tac `∃s. x = encode_infer_t o_f s` >- (
  rw[] >> rw[GSYM fmap_EQ_THM,decode_left_inverse] ) >>
pop_assum mp_tac >>
simp[Once unify_def] >>
Cases_on `walk es e1` >> fs[] >>
Cases_on `walk es e2` >> fs[] >>
TRY (
  strip_tac >> fs[] >>
  qmatch_assum_rename_tac`walk es e1 = Pair t1a t1d`[] >>
  qmatch_assum_rename_tac`walk es e2 = Pair t2a t2d`[] >>
  `Pair t1a t1d = encode_infer_t (t_walk s' t1')` by metis_tac[encode_walk,t_wfs_def] >>
  `Pair t2a t2d = encode_infer_t (t_walk s' t2')` by metis_tac[encode_walk,t_wfs_def] >>
  `wfs sx` by metis_tac[unify_unifier] >>
  `∀c1 c2. (((t1a = Const c1) ∧ (t2a = Const c2)) ∨
            ((t1d = Const c1) ∧ (t2d = Const c2)))
    ⇒ (c1 = c2)` by (
    rpt gen_tac >> strip_tac >>
    qpat_assum `unify X Y Z = SOME A` mp_tac >>
    qpat_assum `unify X Y Z = SOME A` mp_tac >>
    asm_simp_tac std_ss [Once unify_def] >>
    strip_tac >>
    asm_simp_tac std_ss [Once unify_def] >>
    pop_assum mp_tac >>
    simp[] ) >>
  qspecl_then[`t_walk s' t1'`,`t1a`,`t1d`]mp_tac encode_pair_cases >>
  qspecl_then[`t_walk s' t2'`,`t2a`,`t2d`]mp_tac encode_pair_cases >>
  simp[] >>
  strip_tac >> strip_tac >> fs[] (*>- (
    rfs[] >> rw[] >>
    rpt (qpat_assum `Pair X Y = Z` (assume_tac o SYM)) >>
    first_x_assum (qspecl_then[`s'`,`ARB`,`ARB`]kall_tac) >>
    first_x_assum (qspecl_then[`s'`,`Infer_Tfn ta' td'`,`Infer_Tfn ta td`]mp_tac) >>
    simp[option_map_def,encode_infer_t_def] >>
    simp[Once unify_def] >>
    metis_tac[o_f_o_f] )*) >>
  rfs[] >> rw[] >>
  rpt (qpat_assum `Pair X Y = Z` (assume_tac o SYM)) >>
  qpat_assum`unify es X Y = Z`mp_tac >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[] >>
  first_x_assum (qspecl_then[`s'`,`Infer_Tapp ts' ARB`,`Infer_Tapp ts ARB`]mp_tac) >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[option_map_def] >>
  metis_tac[o_f_o_f] ) >>
metis_tac[o_f_FUPDATE,o_f_DOMSUB,FUPDATE_PURGE,encode_walk,t_wfs_def])

val encode_unify = Q.prove (
`!s t1 t2 s' t1' t2'.
  (s = encode_infer_t o_f s') ∧
  (t1 = encode_infer_t t1') ∧ (t2 = encode_infer_t t2') ∧
  t_wfs s' ⇒
  (unify s t1 t2
   =
   option_map ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
metis_tac[encode_unify_lemma])

val wfs_unify = Q.prove (
`!s t1 t2 s'. wfs s ∧ (unify s t1 t2 = SOME s') ⇒ wfs s'`,
metis_tac [unify_unifier]);

val ts_unify_thm = Q.prove (
`!s l1 l2.
  t_wfs s ⇒
  (ts_unify s l1 l2 =
   option_map ((o_f) decode_infer_t)
     (unify (encode_infer_t o_f s) (encode_infer_ts l1) (encode_infer_ts l2)))`,
induct_on `l1` >>
cases_on `l2` >>
rw [ts_unify_def, encode_infer_t_def] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >|
[rw [Once unify_def, option_map_def, decode_left_inverse_I, I_o_f],
 rw [Once unify_def, option_map_def, ts_unify_def],
 rw [Once unify_def, option_map_def, ts_unify_def],
 rw [Once unify_def] >>
     cases_on `t_unify s h' h` >>
     rw [] >|
     [fs [t_unify_def, option_bind_thm] >>
          every_case_tac >>
          fs [option_map_def],
      fs [t_unify_def, option_bind_thm] >>
          every_case_tac >>
          fs [option_map_def] >>
          rw [I_o_f] >>
          `?x. x' = encode_infer_t o_f x`
                by (imp_res_tac encode_unify >>
                    fs [option_map_def] >>
                    cases_on `t_unify s h' h` >>
                    fs [] >>
                    metis_tac []) >>
          `t_wfs x` by
                 (rw [t_wfs_def] >>
                  metis_tac [wfs_unify]) >>
          rw [I_o_f, decode_left_inverse_I]]]);

val t_unify_eqn = Q.store_thm ("t_unify_eqn",
`(!t1 t2 s.
  t_wfs s ⇒
  (t_unify s t1 t2 =
   case (t_walk s t1, t_walk s t2) of
      (Infer_Tuvar v1, Infer_Tuvar v2) =>
        SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2))
    | (Infer_Tuvar v1, t2) => t_ext_s_check s v1 t2
    | (t1, Infer_Tuvar v2) => t_ext_s_check s v2 t1
    | (Infer_Tapp ts1 tc1, Infer_Tapp ts2 tc2) =>
        if tc1 = tc2 then
          ts_unify s ts1 ts2
        else
          NONE
    | (Infer_Tvar_db n1, Infer_Tvar_db n2) =>
        if n1 = n2 then 
          SOME s 
        else
          NONE
    | _ => NONE))`,
rw [t_unify_def] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
rw [Once unify_def, t_walk_def] >>
cases_on `t1` >>
cases_on `t2` >>
rw [encode_infer_t_def, decode_infer_t_def, option_map_def, decode_left_inverse,
    decode_left_inverse_I, I_o_f, encode_vwalk, option_bind_thm] >|
[cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def, option_map_def, decode_left_inverse,
         decode_left_inverse_I, I_o_f, o_f_FUPDATE, decode_infer_t_def] >>
     rw [t_ext_s_check_eqn] >>
     imp_res_tac t_oc_eqn >>
     pop_assum (fn x => ALL_TAC) >>
     pop_assum (fn x => ALL_TAC) >>
     pop_assum (ASSUME_TAC o Q.SPECL [`n''`, `Infer_Tvar_db n`]) >>
     fs [] >>
     rw [t_walk_def, encode_infer_t_def, decode_infer_t_def] >>
     metis_tac [FUPDATE_PURGE],
 rw [Once unify_def] >>
     rw [ts_unify_thm, option_map_def],
 rw [Once unify_def] >>
     rw [Once unify_def] >>
     rw [Once unify_def],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [ts_unify_thm, option_map_def, decode_left_inverse, decode_left_inverse_I,
         I_o_f, o_f_FUPDATE, decode_infer_t_def, t_ext_s_check_eqn, option_map_def] >>
     rw [Once oc_walking, encode_infer_t_def, t_oc_def] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse_I, decode_left_inverse,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm, 
         option_map_def] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse_I, decode_left_inverse,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm, 
         option_map_def] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse, decode_left_inverse_I,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm, 
         option_map_def] >|
     [metis_tac [FUPDATE_PURGE],
      rw [Once unify_def],
      metis_tac [FUPDATE_PURGE],
      metis_tac [FUPDATE_PURGE], 
      metis_tac [FUPDATE_PURGE], 
      metis_tac [FUPDATE_PURGE]]]);

val apply_subst_t_def = Define `
apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t o_f s) (encode_infer_t t))`;

val apply_subst_t_eqn = Q.store_thm ("apply_subst_t_eqn",
`(!s n.
  apply_subst_t s (Infer_Tuvar n) =
   case FLOOKUP s n of
     | NONE => Infer_Tuvar n
     | SOME t => t) ∧
 (!s ts tc.
  apply_subst_t s (Infer_Tapp ts tc) =
    Infer_Tapp (MAP (apply_subst_t s) ts) tc) ∧
 (!s n.
  apply_subst_t s (Infer_Tvar_db n) = 
    Infer_Tvar_db n)`, 
rw [apply_subst_t_def, encode_infer_t_def, FLOOKUP_o_f,
    decode_infer_t_def, option_map_def] >>
every_case_tac >>
rw [decode_left_inverse, decode_infer_t_def] >>
induct_on `ts` >>
rw [apply_subst_t_def, encode_infer_t_def, decode_infer_t_def]);

val t_walkstar_def = Define `
t_walkstar s t = 
  decode_infer_t (walkstar (encode_infer_t o_f s) (encode_infer_t t))`;

val ts_walkstar_thm = Q.prove (
`!l s.
  t_wfs s ⇒
  (decode_infer_ts ((encode_infer_t o_f s) ◁ encode_infer_ts l) = 
   MAP (t_walkstar s) l)`,
induct_on `l` >>
rw [t_wfs_def, encode_infer_t_def, Once walkstar_def, decode_infer_t_def] >>
rw [t_walkstar_def]);

val t_walkstar_eqn = Q.store_thm ("t_walkstar_eqn",
`!s. t_wfs s ⇒
  !t.
    t_walkstar s t =
    case t_walk s t of
      | Infer_Tuvar v => Infer_Tuvar v
      | Infer_Tapp ts tc0 => Infer_Tapp (MAP (t_walkstar s) ts) tc0
      | Infer_Tvar_db n => Infer_Tvar_db n`,
rw [t_walkstar_def] >>
`wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
rw [Once walkstar_def, t_walk_def] >>
cases_on `t` >>
rw [encode_infer_t_def, decode_infer_t_def, decode_left_inverse, encode_vwalk] >|
[rw [ts_walkstar_thm],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def, decode_infer_t_def, ts_walkstar_thm]]);

val t_collapse_def = Define `
t_collapse s = 
  decode_infer_t o_f collapse (encode_infer_t o_f s)`;

val t_collapse_eqn = Q.store_thm ("t_collapse_eqn",
`!s. t_collapse s = FUN_FMAP (\v. t_walkstar s (Infer_Tuvar v)) (FDOM s)`,
rw [collapse_def, t_collapse_def, t_walkstar_def, encode_infer_t_def, walkstar_def] >>
rw [GSYM fmap_EQ_THM, FUN_FMAP_DEF]);

val _ = export_theory ();
