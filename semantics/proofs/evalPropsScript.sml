(* Various basic properties of the big and small step semantics, and their
 * semantic primitives. *)

open preamble;
open optionTheory;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory;
open miscLib boolSimps;

val _ = new_theory "evalProps";

val lit_same_type_refl = store_thm("lit_same_type_refl",
  ``∀l. lit_same_type l l``,
  Cases >> simp[semanticPrimitivesTheory.lit_same_type_def])
val _ = export_rewrites["lit_same_type_refl"]

val lit_same_type_sym = store_thm("lit_same_type_sym",
  ``∀l1 l2. lit_same_type l1 l2 ⇒ lit_same_type l2 l1``,
  Cases >> Cases >> simp[semanticPrimitivesTheory.lit_same_type_def])

val pmatch_append = Q.store_thm ("pmatch_append",
`(!(cenv : envC) (st : v store) p v env env' env''.
    (pmatch cenv st p v env = Match env') ⇒
    (pmatch cenv st p v (env++env'') = Match (env'++env''))) ∧
 (!(cenv : envC) (st : v store) ps v env env' env''.
    (pmatch_list cenv st ps v env = Match env') ⇒
    (pmatch_list cenv st ps v (env++env'') = Match (env'++env'')))`,
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, bind_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val do_app_cases = Q.store_thm ("do_app_cases",
`!st op st' vs v.
  (do_app st op vs = SOME (st',v))
  =
  ((?op' n1 n2.
    (op = Opn op') ∧ (vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∧
    (((((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (v = Rerr (Rraise (prim_exn "Div")))) ∨
     ~(((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (v = Rval (Litv (IntLit (opn_lookup op' n1 n2)))))) ∨
  (?op' n1 n2.
    (op = Opb op') ∧ (vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∧
    (st = st') ∧ (v = Rval (Litv (Bool (opb_lookup op' n1 n2))))) ∨
  ((op = Equality) ∧ (st = st') ∧
    ((?v1 v2. 
      (vs = [v1;v2]) ∧ 
      ((?b. (do_eq v1 v2 = Eq_val b) ∧ (v = Rval (Litv (Bool b)))) ∨
       ((do_eq v1 v2 = Eq_closure) ∧ (v = Rerr (Rraise (prim_exn "Eq")))))))) ∨
  (?lnum v2.
    (op = Opassign) ∧ (vs = [Loc lnum; v2]) ∧ (store_assign lnum (Refv v2) st = SOME st') ∧
     (v = Rval (Litv Unit))) ∨
  (?lnum v2.
    (op = Opref) ∧ (vs = [v2]) ∧ (store_alloc (Refv v2) st = (st',lnum)) ∧
     (v = Rval (Loc lnum))) ∨
  (?lnum v2.
    (st = st') ∧
    (op = Opderef) ∧ (vs = [Loc lnum]) ∧ (store_lookup lnum st = SOME (Refv v2)) ∧
    (v = Rval v2)) ∨
  (?i w.
      (op = Aw8alloc) ∧ (vs = [Litv (IntLit i); Litv (Word8 w)]) ∧
      (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ (st = st')) ∨
       (?lnum. ~(i < 0) ∧
        (st',lnum) = store_alloc (W8array (REPLICATE (Num (ABS i)) w)) st ∧
        v = Rval (Loc lnum)))) ∨
  (?ws lnum i.
    (op = Aw8sub) ∧ (vs = [Loc lnum; Litv (IntLit i)]) ∧ (st = st') ∧
    store_lookup lnum st = SOME (W8array ws) ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript"))) ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH ws ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH ws ∧
      (v = Rval (Litv (Word8 (EL (Num(ABS i)) ws))))))) ∨
  (?lnum ws.
    (op = Aw8length) ∧ (vs = [Loc lnum]) ∧ st = st' ∧
    store_lookup lnum st = SOME (W8array ws) ∧ 
    v = Rval (Litv (IntLit (&(LENGTH ws))))) ∨
  (?ws lnum i w.
    (op = Aw8update) ∧ (vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∧ 
    store_lookup lnum st = SOME (W8array ws) ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ st = st') ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH ws ∧ st = st' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH ws ∧
      store_assign lnum (W8array (LUPDATE w (Num (ABS i)) ws)) st = SOME st' ∧
      v = Rval (Litv Unit)))) ∨
  (?vs' v'.
    (op = VfromList) ∧ (vs = [v']) ∧ (SOME vs' = v_to_list v') ∧
    st = st' ∧
    v = Rval (Vectorv vs')) ∨
  (?vs' lnum i.
    (op = Vsub) ∧ (vs = [Vectorv vs'; Litv (IntLit i)]) ∧ (st = st') ∧
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript"))) ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH vs' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH vs' ∧
      (v = Rval (EL (Num(ABS i)) vs'))))) ∨
  (?vs'.
    (op = Vlength) ∧ (vs = [Vectorv vs']) ∧ st = st' ∧
    v = Rval (Litv (IntLit (&(LENGTH vs'))))) ∨
  (?i v'.
      (op = Aalloc) ∧ (vs = [Litv (IntLit i); v']) ∧
      (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ (st = st')) ∨
       (?lnum. ~(i < 0) ∧
        (st',lnum) = store_alloc (Varray (REPLICATE (Num (ABS i)) v')) st ∧
        v = Rval (Loc lnum)))) ∨
  (?vs' lnum i.
    (op = Asub) ∧ (vs = [Loc lnum; Litv (IntLit i)]) ∧ (st = st') ∧
    store_lookup lnum st = SOME (Varray vs') ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript"))) ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH vs' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH vs' ∧
      (v = Rval (EL (Num(ABS i)) vs'))))) ∨
  (?lnum vs'.
    (op = Alength) ∧ (vs = [Loc lnum]) ∧ st = st' ∧
    store_lookup lnum st = SOME (Varray vs') ∧ 
    v = Rval (Litv (IntLit (&(LENGTH vs'))))) ∨
  (?vs' lnum i v'.
    (op = Aupdate) ∧ (vs = [Loc lnum; Litv (IntLit i); v']) ∧ 
    store_lookup lnum st = SOME (Varray vs') ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ st = st') ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH vs' ∧ st = st' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH vs' ∧
      store_assign lnum (Varray (LUPDATE v' (Num (ABS i)) vs')) st = SOME st' ∧
      v = Rval (Litv Unit)))))`,
 SIMP_TAC (srw_ss()) [do_app_def] >>
 cases_on `op` >>
 rw [] >>
 cases_on `vs` >>
 rw [] >>
 every_case_tac >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 TRY (eq_tac >> rw [] >> NO_TAC) >>
 TRY (cases_on `do_eq v1 v2`) >>
 rw [] >>
 UNABBREV_ALL_TAC >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 every_case_tac >>
 rw [] >>
 metis_tac []);

val do_opapp_cases = store_thm("do_opapp_cases",
  ``∀env' vs v.
    (do_opapp vs = SOME (env',v))
    =
  ((∃v2 menv'' cenv'' env'' n e.
    (vs = [Closure (menv'',cenv'',env'') n e; v2]) ∧
    (env' = (menv'',cenv'',bind n v2 env'')) ∧ (v = e)) ∨
  (?v2 menv'' cenv'' env'' funs n' n'' e.
    (vs = [Recclosure (menv'',cenv'',env'') funs n'; v2]) ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ∧
    (env' = (menv'',cenv'', bind n'' v2 (build_rec_env funs (menv'',cenv'',env'') env''))) ∧ (v = e)))``,
  rw[do_opapp_def] >>
  cases_on `vs` >> rw [] >>
  every_case_tac >> metis_tac []);

val build_rec_env_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure env funs' f) env') env' funs =
merge (MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs) env'`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
`∀funs funs' env env'.
  build_rec_env funs env env' =
  merge (MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs) env'`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val do_con_check_build_conv = Q.store_thm ("do_con_check_build_conv",
`!tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v`,
rw [do_con_check_def, build_conv_def] >>
every_case_tac >>
fs []);

val merge_envC_empty_assoc = Q.store_thm ("merge_envC_empty_assoc",
`!envC1 envC2 envC3.
  merge_envC ([],envC1) (merge_envC ([],envC2) envC3)
  =
  merge_envC ([],envC1++envC2) envC3`,
 rw [] >>
 PairCases_on `envC3` >>
 rw [merge_envC_def, merge_def]);

val same_ctor_and_same_tid = Q.store_thm ("same_ctor_and_same_tid",
`!cn1 tn1 cn2 tn2.
  same_tid tn1 tn2 ∧
  same_ctor (cn1,tn1) (cn2,tn2)
  ⇒
  tn1 = tn2 ∧ cn1 = cn2`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 fs [same_tid_def, same_ctor_def]);

val same_tid_sym = Q.store_thm ("same_tid_sym",
`!tn1 tn2. same_tid tn1 tn2 = same_tid tn2 tn1`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 rw [same_tid_def] >>
 metis_tac []);

val build_tdefs_cons = Q.store_thm ("build_tdefs_cons",
`(!tvs tn ctors tds mn.
  build_tdefs mn ((tvs,tn,ctors)::tds) =
    build_tdefs mn tds ++ REVERSE (MAP (\(conN,ts). (conN, LENGTH ts, TypeId (mk_id mn tn))) ctors)) ∧
 (!mn. build_tdefs mn [] = [])`,
rw [build_tdefs_def]);

val check_dup_ctors_cons = Q.store_thm ("check_dup_ctors_cons",
`!tvs ts ctors tds.
  check_dup_ctors ((tvs,ts,ctors)::tds)
  ⇒
  check_dup_ctors tds`,
induct_on `tds` >>
rw [check_dup_ctors_def, LET_THM, RES_FORALL] >>
PairCases_on `h` >>
fs [] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
rw [] >>
PairCases_on `h` >>
fs []);

val map_error_result_def = Define`
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f Rtype_error = Rtype_error) ∧
  (map_error_result f Rtimeout_error = Rtimeout_error)`
val _ = export_rewrites["map_error_result_def"]

val map_error_result_Rtype_error = store_thm("map_error_result_Rtype_error",
  ``map_error_result f e = Rtype_error ⇔ e = Rtype_error``,
  Cases_on`e`>>simp[])
val map_error_result_Rtimeout_error = store_thm("map_error_result_Rtimeout_error",
  ``map_error_result f e = Rtimeout_error ⇔ e = Rtimeout_error``,
  Cases_on`e`>>simp[])
val _ = export_rewrites["map_error_result_Rtimeout_error","map_error_result_Rtype_error"]

val map_result_def = Define`
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`
val _ = export_rewrites["map_result_def"]

val map_result_Rerr = store_thm("map_result_Rerr",
  ``map_result f1 f2 e = Rerr e' ⇔ ∃a. e = Rerr a ∧ map_error_result f2 a = e'``,
  Cases_on`e`>>simp[EQ_IMP_THM])
val _ = export_rewrites["map_result_Rerr"]

val exc_rel_def = Define`
  (exc_rel R (Rraise v1) (Rraise v2) = R v1 v2) ∧
  (exc_rel _ Rtype_error Rtype_error = T) ∧
  (exc_rel _ Rtimeout_error Rtimeout_error = T) ∧
  (exc_rel _ _ _ = F)`
val _ = export_rewrites["exc_rel_def"]

val exc_rel_raise1 = store_thm("exc_rel_raise1",
  ``exc_rel R (Rraise v) e = ∃v'. (e = Rraise v') ∧ R v v'``,
  Cases_on`e`>>rw[])
val exc_rel_raise2 = store_thm("exc_rel_raise2",
  ``exc_rel R e (Rraise v) = ∃v'. (e = Rraise v') ∧ R v' v``,
  Cases_on`e`>>rw[])
val exc_rel_type_error = store_thm("exc_rel_type_error",
  ``(exc_rel R Rtype_error e = (e = Rtype_error)) ∧
    (exc_rel R e Rtype_error = (e = Rtype_error))``,
  Cases_on`e`>>rw[])
val exc_rel_timeout_error = store_thm("exc_rel_timeout_error",
  ``(exc_rel R Rtimeout_error e = (e = Rtimeout_error)) ∧
    (exc_rel R e Rtimeout_error = (e = Rtimeout_error))``,
  Cases_on`e`>>rw[])
val _ = export_rewrites["exc_rel_raise1","exc_rel_raise2","exc_rel_type_error","exc_rel_timeout_error"]

val exc_rel_refl = store_thm(
"exc_rel_refl",
  ``(∀x. R x x) ⇒ ∀x. exc_rel R x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["exc_rel_refl"];

val exc_rel_trans = store_thm(
"exc_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. exc_rel R x y ∧ exc_rel R y z ⇒ exc_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val result_rel_def = Define`
(result_rel R1 _ (Rval v1) (Rval v2) = R1 v1 v2) ∧
(result_rel _ R2 (Rerr e1) (Rerr e2) = exc_rel R2 e1 e2) ∧
(result_rel _ _ _ _ = F)`
val _ = export_rewrites["result_rel_def"]

val result_rel_Rval = store_thm(
"result_rel_Rval",
``result_rel R1 R2 (Rval v) r = ∃v'. (r = Rval v') ∧ R1 v v'``,
Cases_on `r` >> rw[])
val result_rel_Rerr1 = store_thm(
"result_rel_Rerr1",
``result_rel R1 R2 (Rerr e) r = ∃e'. (r = Rerr e') ∧ exc_rel R2 e e'``,
Cases_on `r` >> rw[EQ_IMP_THM])
val result_rel_Rerr2 = store_thm(
"result_rel_Rerr2",
``result_rel R1 R2 r (Rerr e) = ∃e'. (r = Rerr e') ∧ exc_rel R2 e' e``,
Cases_on `r` >> rw[EQ_IMP_THM])
val _ = export_rewrites["result_rel_Rval","result_rel_Rerr1","result_rel_Rerr2"]

val result_rel_refl = store_thm(
"result_rel_refl",
``(∀x. R1 x x) ∧ (∀x. R2 x x) ⇒ ∀x. result_rel R1 R2 x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["result_rel_refl"]

val result_rel_trans = store_thm(
"result_rel_trans",
``(∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀x y z. R2 x y ∧ R2 y z ⇒ R2 x z) ⇒ (∀x y z. result_rel R1 R2 x y ∧ result_rel R1 R2 y z ⇒ result_rel R1 R2 x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[exc_rel_trans])

val every_error_result_def = Define`
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P Rtype_error = T) ∧
  (every_error_result P Rtimeout_error = T)`
val _ = export_rewrites["every_error_result_def"]

val every_result_def = Define`
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))`
val _ = export_rewrites["every_result_def"]

val map_sv_def = Define`
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs))`
val _ = export_rewrites["map_sv_def"]

val dest_Refv_def = Define`
  dest_Refv (Refv v) = v`
val is_Refv_def = Define`
  is_Refv (Refv _) = T ∧
  is_Refv _ = F`
val _ = export_rewrites["dest_Refv_def","is_Refv_def"]

val sv_every_def = Define`
  sv_every P (Refv v) = P v ∧
  sv_every P (Varray vs) = EVERY P vs ∧
  sv_every P _ = T`
val _ = export_rewrites["sv_every_def"]

val sv_rel_def = Define`
  sv_rel R (Refv v1) (Refv v2) = R v1 v2 ∧
  sv_rel R (W8array w1) (W8array w2) = (w1 = w2) ∧
  sv_rel R (Varray vs1) (Varray vs2) = LIST_REL R vs1 vs2 ∧
  sv_rel R _ _ = F`
val _ = export_rewrites["sv_rel_def"]

val sv_rel_refl = store_thm("sv_rel_refl",
  ``∀R x. (∀x. R x x) ⇒ sv_rel R x x``,
  gen_tac >> Cases >> rw[sv_rel_def] >>
  induct_on `l` >>
  rw [])
val _ = export_rewrites["sv_rel_refl"]

val sv_rel_trans = store_thm("sv_rel_trans",
  ``∀R. (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ ∀x y z. sv_rel R x y ∧ sv_rel R y z ⇒ sv_rel R x z``,
  gen_tac >> strip_tac >> Cases >> Cases >> Cases >> rw [] >> fs [sv_rel_def] >> metis_tac[LIST_REL_trans]);

val sv_rel_cases = store_thm("sv_rel_cases",
  ``∀x y.
    sv_rel R x y ⇔
    (∃v1 v2. x = Refv v1 ∧ y = Refv v2 ∧ R v1 v2) ∨
    (∃w. x = W8array w ∧ y = W8array w) ∨
    (?vs1 vs2. x = Varray vs1 ∧ y = Varray vs2 ∧ LIST_REL R vs1 vs2)``,
  Cases >> Cases >> simp[sv_rel_def,EQ_IMP_THM])

val sv_rel_O = store_thm("sv_rel_O",
  ``∀R1 R2. sv_rel (R1 O R2) = sv_rel R1 O sv_rel R2``,
  rw[FUN_EQ_THM,sv_rel_cases,O_DEF,EQ_IMP_THM] >>
  metis_tac[miscTheory.LIST_REL_O])

val sv_rel_mono = store_thm("sv_rel_mono",
  ``(∀x y. P x y ⇒ Q x y) ⇒ sv_rel P x y ⇒ sv_rel Q x y``,
  rw[sv_rel_cases] >> metis_tac [LIST_REL_mono])

val store_v_vs_def = Define`
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = []`
val _ = export_rewrites["store_v_vs_def"]

val store_vs_def = Define`
  store_vs s = FLAT (MAP store_v_vs s)`

val EVERY_sv_every_MAP_map_sv = store_thm("EVERY_sv_every_MAP_map_sv",
  ``∀P f ls. EVERY P (MAP f (store_vs ls)) ⇒ EVERY (sv_every P) (MAP (map_sv f) ls)``,
  rpt gen_tac >>
  simp[EVERY_MAP,EVERY_MEM,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
  strip_tac >> Cases >> simp[] >> rw[] >> res_tac >> fs[EVERY_MEM,MEM_MAP,PULL_EXISTS])

val LIST_REL_store_vs_intro = store_thm("LIST_REL_store_vs_intro",
  ``∀P l1 l2. LIST_REL (sv_rel P) l1 l2 ⇒ LIST_REL P (store_vs l1) (store_vs l2)``,
  gen_tac >>
  Induct >- simp[store_vs_def] >>
  Cases >> simp[PULL_EXISTS,sv_rel_cases] >>
  fs[store_vs_def] >> rw[] >>
  match_mp_tac rich_listTheory.EVERY2_APPEND_suff >> simp[])

val EVERY_sv_every_EVERY_store_vs = store_thm("EVERY_sv_every_EVERY_store_vs",
  ``∀P ls. EVERY (sv_every P ) ls ⇔ EVERY P (store_vs ls)``,
  rw[EVERY_MEM,EQ_IMP_THM,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
  res_tac >> TRY(Cases_on`e`) >> TRY(Cases_on`y`) >> fs[] >>
  fs[EVERY_MEM])

val EVERY_store_vs_intro = store_thm("EVERY_store_vs_intro",
  ``∀P ls. EVERY (sv_every P) ls ⇒ EVERY P (store_vs ls)``,
  rw[EVERY_MEM,store_vs_def,MEM_MAP,MEM_FILTER,MEM_FLAT] >>
  res_tac >>
  qmatch_assum_rename_tac`sv_every P x`[] >>
  Cases_on`x`>>fs[EVERY_MEM])

val map_sv_compose = store_thm("map_sv_compose",
  ``map_sv f (map_sv g x) = map_sv (f o g) x``,
  Cases_on`x`>>simp[MAP_MAP_o])

val map_match_def = Define`
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)`
val _ = export_rewrites["map_match_def"]

val evaluate_decs_evaluate_prog_MAP_Tdec = store_thm("evaluate_decs_evaluate_prog_MAP_Tdec",
  ``∀ck env cs tids ds res.
      evaluate_decs ck NONE env (cs,tids) ds res
      ⇔
      case res of ((s,tids'),envC,r) =>
      evaluate_prog ck env (cs,tids,{}) (MAP Tdec ds) ((s,tids',{}),([],envC),map_result(λenvE. (emp,envE))(I)r)``,
  Induct_on`ds`>>simp[Once evaluate_decs_cases,Once evaluate_prog_cases] >- (
    rpt gen_tac >> BasicProvers.EVERY_CASE_TAC >> simp[emp_def] >>
    Cases_on`r'`>>simp[] ) >>
  srw_tac[DNF_ss][] >>
  PairCases_on`res`>>srw_tac[DNF_ss][]>>
  PairCases_on`env`>>srw_tac[DNF_ss][]>>
  simp[evaluate_top_cases] >> srw_tac[DNF_ss][emp_def] >>
  srw_tac[DNF_ss][EQ_IMP_THM] >- (
    Cases_on`e`>>simp[] )
  >- (
    disj1_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(split_pair_match o concl) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[] >> strip_tac >>
    fs[merge_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`r`>> simp[combine_dec_result_def,combine_mod_result_def,merge_def,emp_def,merge_envC_def] )
  >- (
    disj2_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM,FORALL_PROD,merge_def,merge_envC_def] >>
    `∃z. r' = map_result (λenvE. (emp,envE)) I z` by (
      Cases_on`r'`>>fs[combine_mod_result_def,merge_def] >>
      TRY(METIS_TAC[]) >>
      Cases_on`a`>>fs[]>>
      Cases_on`res4`>>fs[]>>rw[]>>
      qexists_tac`Rval r` >> simp[emp_def] ) >>
    PairCases_on`new_tds'`>>fs[merge_envC_def,merge_def]>>rw[]>>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[combine_dec_result_def,combine_mod_result_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    TRY (Cases_on`res4`>>fs[]) >>
    Cases_on`a`>>Cases_on`e`>>fs[]>>rw[])
  >- (
    Cases_on`a`>>fs[]))

val find_recfun_ALOOKUP = store_thm(
"find_recfun_ALOOKUP",
``∀funs n. find_recfun n funs = ALOOKUP funs n``,
Induct >- rw[semanticPrimitivesTheory.find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
rw[semanticPrimitivesTheory.find_recfun_def])

val pat_bindings_accum = Q.store_thm ("pat_bindings_accum",
`(!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)`,
 Induct >>
 rw []
 >- rw [pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val ctors_of_tdef_def = Define`
  ctors_of_tdef (_,_,condefs) = MAP FST condefs`
val _ = export_rewrites["ctors_of_tdef_def"]

val ctors_of_dec_def = Define`
  ctors_of_dec (Dtype tds) = FLAT (MAP ctors_of_tdef tds) ∧
  ctors_of_dec (Dexn s _) = [s] ∧
  ctors_of_dec _ = []`
val _ = export_rewrites["ctors_of_dec_def"]

val evaluate_decs_ctors_in = store_thm("evaluate_decs_ctors_in",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀cn.
        IS_SOME (lookup cn (FST(SND res))) ⇒
        MEM cn (FLAT (MAP ctors_of_dec decs))``,
  HO_MATCH_MP_TAC evaluate_decs_ind >>
  simp[libTheory.emp_def] >>
  rw[Once evaluate_dec_cases] >> simp[] >>
  fs[libTheory.merge_def,libTheory.emp_def] >>
  fs[libPropsTheory.lookup_append] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[libTheory.bind_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[miscTheory.IS_SOME_EXISTS] >>
  imp_res_tac libPropsTheory.lookup_in2 >>
  fs[MEM_MAP,semanticPrimitivesTheory.build_tdefs_def,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
  METIS_TAC[])

val check_dup_ctors_flat = Q.store_thm("check_dup_ctors_flat",
`!defs.
  check_dup_ctors (defs:type_def) =
  ALL_DISTINCT (MAP FST (build_tdefs mn defs))`,
 rw [check_dup_ctors_thm, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
     semanticPrimitivesTheory.build_tdefs_def,
     rich_listTheory.MAP_REVERSE, ALL_DISTINCT_REVERSE]);

(* free vars *)

val FV_def = tDefine "FV"`
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (App _ es) = FV_list es) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)`
  (WF_REL_TAC `inv_image $< (λx. case x of
     | INL e => exp_size e
     | INR (INL es) => exp6_size es
     | INR (INR (INL pes)) => exp3_size pes
     | INR (INR (INR (defs))) => exp1_size defs)`)
val _ = export_rewrites["FV_def"]

val _ = Parse.overload_on("SFV",``λe. {x | Short x ∈ FV e}``)

val FV_pes_MAP = store_thm("FV_pes_MAP",
  ``FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes))``,
  Induct_on`pes`>>simp[]>>
  qx_gen_tac`p`>>PairCases_on`p`>>rw[])

val FV_defs_MAP = store_thm("FV_defs_MAP",
  ``∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))``,
  Induct_on`ls`>>simp[FORALL_PROD])

val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _) = {}) ∧
  (FV_dec (Dexn _ _) = {})`
val _ = export_rewrites["FV_dec_def"]

val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _) = []) ∧
  (new_dec_vs (Dtabbrev _ _ _) = []) ∧
  (new_dec_vs (Dexn _ _) = []) ∧
  (new_dec_vs (Dlet p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"]

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"]

val new_top_vs_def = Define`
  new_top_vs (Tdec d) = MAP Short (new_dec_vs d) ∧
  new_top_vs (Tmod mn _ ds) = MAP (Long mn) (new_decs_vs ds)`
val _ = export_rewrites["new_top_vs_def"]

val FV_prog_def = Define`
  (FV_prog [] = {}) ∧
  (FV_prog (t::ts) = FV_top t ∪ ((FV_prog ts) DIFF (set (new_top_vs t))))`

val all_env_dom_def = Define`
  all_env_dom (envM,envC,envE) =
    IMAGE Short (set (MAP FST envE)) ∪
    { Long m x | ∃e. lookup m envM = SOME e ∧ MEM x (MAP FST e) }`

(* REPL bootstrap lemmas *)

val evaluate_decs_last3 = prove(
  ``∀ck mn env s decs a b c k i j s1 x y decs0 decs1 v p q r.
      evaluate_decs ck mn env s decs (((k,s1),a),b,Rval c) ∧
      decs = decs0 ++ [Dlet (Pvar x) (App Opref [Con i []]);Dlet(Pvar y)(App Opref [Con j []]);Dlet (Pvar p) (Fun q r)]
      ⇒
      ∃n ls1 ls2 ls.
      c = ((p,(Closure(FST env,merge_envC([],b)(FST(SND env)),merge ls1(SND(SND env))) q r))::ls1) ∧
      ls1 = ((y,Loc (n+1))::ls2) ∧ n+1 < LENGTH s1 ∧
      ls2 = ((x,Loc n)::ls) ∧
      is_Refv (EL n s1) ∧
      is_Refv (EL (n+1) s1)``,
  Induct_on`decs0` >>
  rw[Once bigStepTheory.evaluate_decs_cases] >- (
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    fs[semanticPrimitivesTheory.combine_dec_result_def] >>
    fs[Once bigStepTheory.evaluate_dec_cases] >>
    fs[Once bigStepTheory.evaluate_cases] >>
    fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[semanticPrimitivesTheory.do_app_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,LET_THM] >>
    fs[terminationTheory.pmatch_def] >> rw[] >>
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    fs[semanticPrimitivesTheory.combine_dec_result_def] >>
    fs[Once bigStepTheory.evaluate_dec_cases] >>
    rator_x_assum`evaluate`mp_tac >>
    simp[Once bigStepTheory.evaluate_cases] >> rw[] >>
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    rw[libTheory.merge_def,libTheory.emp_def,libTheory.bind_def] >>
    fs[pmatch_def,libTheory.bind_def] >> rw[] >>
    fs[Once evaluate_cases] >>
    fs[Once evaluate_cases] >> rw[] >>
    PairCases_on`cenv` >>
    rw[libTheory.emp_def,semanticPrimitivesTheory.merge_envC_def,libTheory.merge_def] >>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2]) >>
  Cases_on`r'`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rfs[semanticPrimitivesTheory.all_env_to_cenv_def] >>
  rw[libTheory.merge_def] >>
  PairCases_on`cenv` >>
  rw[libTheory.emp_def,semanticPrimitivesTheory.merge_envC_def,libTheory.merge_def])

val evaluate_Tmod_last3 = store_thm("evaluate_Tmod_last3",
  ``evaluate_top ck env0 st (Tmod mn NONE decs) ((cs,u),envC,Rval ([(mn,env)],v)) ⇒
    decs = decs0 ++[Dlet (Pvar x) (App Opref [Con i []]);Dlet (Pvar y) (App Opref [Con j []]);Dlet (Pvar p) (Fun q z)]
  ⇒
    ∃n ls1 ls.
    env = (p,(Closure (FST env0,merge_envC ([],SND(HD(FST envC))) (FST(SND env0)),merge ls (SND(SND env0))) q z))::ls ∧
    (ls = (y,Loc (n+1))::(x,Loc n)::ls1) ∧
    n+1 < LENGTH (SND cs) ∧
    is_Refv (EL n (SND cs)) ∧
    is_Refv (EL (n+1) (SND cs))``,
  Cases_on`cs`>>rw[bigStepTheory.evaluate_top_cases]>>
  imp_res_tac evaluate_decs_last3 >> fs[]) |> GEN_ALL

val evaluate_decs_tys = prove(
  ``∀decs0 decs1 decs ck mn env s s' tys c tds tvs tn cts cn as.
    evaluate_decs ck (SOME mn) env s decs (s',tys,Rval c) ∧
    decs = decs0 ++ [Dtype tds] ++ decs1 ∧
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (lookup cn tys = SOME (LENGTH as, TypeId (Long mn tn)))``,
  Induct >> rw[Once evaluate_decs_cases] >- (
    fs[Once evaluate_dec_cases] >> rw[] >>
    simp[libTheory.merge_def,libPropsTheory.lookup_append] >>
    imp_res_tac evaluate_decs_ctors_in >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    Cases_on`lookup cn (build_tdefs (SOME mn) tds)` >- (
      imp_res_tac libPropsTheory.lookup_notin >>
      fs[semanticPrimitivesTheory.build_tdefs_def,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    imp_res_tac (fst(EQ_IMP_RULE(SPEC_ALL check_dup_ctors_flat))) >>
    imp_res_tac libPropsTheory.lookup_in3 >>
    `MEM (cn,LENGTH as,TypeId(Long mn tn)) (build_tdefs (SOME mn) tds)` by (
      simp[semanticPrimitivesTheory.build_tdefs_def,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
      simp[astTheory.mk_id_def] >> METIS_TAC[] ) >>
    first_x_assum(qspec_then`SOME mn`mp_tac) >>
    strip_tac >>
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(cn,X) = EL n1 ls`["X","ls"] >>
    qmatch_assum_rename_tac`(cn,x) = EL n2 ls`["ls"] >>
    `EL n1 (MAP FST (build_tdefs (SOME mn) tds)) =
     EL n2 (MAP FST (build_tdefs (SOME mn) tds))` by (
       simp[EL_MAP] >> METIS_TAC[FST] ) >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    `n1 = n2` by METIS_TAC[] >>
    fs[] >>
    METIS_TAC[PAIR_EQ] ) >>
  simp[libPropsTheory.lookup_append,libTheory.merge_def] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  simp[])

val evaluate_Tmod_tys = store_thm("evaluate_Tmod_tys",
  ``evaluate_top F env s (Tmod mn NONE decs) (s',([m,tys],e),Rval r) ⇒
    decs = decs0 ++ [Dtype tds] ++ decs1 ⇒
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (lookup cn tys = SOME (LENGTH as, TypeId (Long mn tn)))``,
  rw[evaluate_top_cases] >>
  METIS_TAC[evaluate_decs_tys]) |> GEN_ALL

val _ = export_theory ();
