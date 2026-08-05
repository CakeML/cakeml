(*
  Various basic properties of the semantic primitives.
*)
Theory semanticPrimitivesProps
Ancestors
  ast namespace ffi semanticPrimitives namespaceProps
Libs
  preamble boolSimps


Theorem with_same_v[simp]:
   (env:'v sem_env) with v := env.v = env
Proof
  srw_tac[][sem_env_component_equality]
QED

Theorem unchanged_env[simp]:
  !(env : 'a sem_env).
  <| v := env.v; c := env.c |> = env
Proof
 rw [sem_env_component_equality]
QED

Theorem with_same_clock:
   (st:'ffi semanticPrimitives$state) with clock := st.clock = st
Proof
  rw[semanticPrimitivesTheory.state_component_equality]
QED

Theorem Boolv_11[simp]:
  Boolv b1 = Boolv b2 ⇔ (b1 = b2)
Proof
srw_tac[][Boolv_def]
QED

Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    =
    extend_dec_env (extend_dec_env env1 env2) env3
Proof
 rw [extend_dec_env_def]
QED

Definition shift_lookup_def[simp]:
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)
End

Definition do_shift_def[simp]:
  (do_shift sh n W8 (Word8 w) = SOME (Word8 (shift_lookup sh w n))) ∧
  (do_shift sh n W64 (Word64 w) = SOME (Word64 (shift_lookup sh w n))) ∧
  (do_shift _ _ _ _ = NONE)
End

(*
Definition do_word_op_def[simp]:
  (do_word_op op W8 (Word8 w1) (Word8 w2) = SOME (Word8 (opw_lookup op w1 w2))) ∧
  (do_word_op op W64 (Word64 w1) (Word64 w2) = SOME (Word64 (opw_lookup op w1 w2))) ∧
  (do_word_op op _ _ _ = NONE)
End

Definition do_word_to_int_def[simp]:
  (do_word_to_int W8 (Word8 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int W64 (Word64 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int _ _ = NONE)
End

Definition do_word_from_int_def[simp]:
  (do_word_from_int W8 i = Word8 (i2w i)) ∧
  (do_word_from_int W64 i = Word64 (i2w i))
End
*)

Theorem lit_same_type_refl[simp]:
   ∀l. lit_same_type l l
Proof
  Cases >> simp[semanticPrimitivesTheory.lit_same_type_def]
QED

Theorem lit_same_type_sym:
   ∀l1 l2. lit_same_type l1 l2 ⇒ lit_same_type l2 l1
Proof
  Cases >> Cases >> simp[semanticPrimitivesTheory.lit_same_type_def]
QED

Theorem pmatch_append:
 (!(cenv : env_ctor) (st : v store) p v env env' env''.
    (pmatch cenv st p v env = Match env') ⇒
    (pmatch cenv st p v (env++env'') = Match (env'++env''))) ∧
 (!(cenv : env_ctor) (st : v store) ps v env env' env''.
    (pmatch_list cenv st ps v env = Match env') ⇒
    (pmatch_list cenv st ps v (env++env'') = Match (env'++env'')))
Proof
ho_match_mp_tac pmatch_ind >>
srw_tac[][pmatch_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
metis_tac []
QED

Theorem pmatch_extend:
 (!cenv s p v env env' env''.
  pmatch cenv s p v env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p) ∧
 (!cenv s ps vs env env' env''.
  pmatch_list cenv s ps vs env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps)
Proof
 ho_match_mp_tac pmatch_ind >>
 srw_tac[][pat_bindings_def, pmatch_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 res_tac >> rveq >>
 srw_tac[][]
QED

Theorem pmatch_nsAppend:
  (∀ns st pat v env m ns'.
    (pmatch ns st pat v env = No_match
   ⇒ pmatch (nsAppend ns ns') st pat v env = No_match) ∧
    (pmatch ns st pat v env = Match m
   ⇒ pmatch (nsAppend ns ns') st pat v env = Match m)) ∧
  (∀ns st pats vs env m ns'.
    (pmatch_list ns st pats vs env = No_match
   ⇒ pmatch_list (nsAppend ns ns') st pats vs env = No_match) ∧
    (pmatch_list ns st pats vs env = Match m
   ⇒ pmatch_list (nsAppend ns ns') st pats vs env = Match m))
Proof
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def]
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >>
    `nsLookup (nsAppend ns ns') n = SOME x` by
      gvs[namespacePropsTheory.nsLookup_nsAppend_some] >>
    gvs[] >> PairCases_on `x` >> gvs[] >>
    rpt (TOP_CASE_TAC >> gvs[])
    )
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >>
    `nsLookup (nsAppend ns ns') n = SOME x` by
      gvs[namespacePropsTheory.nsLookup_nsAppend_some] >>
    gvs[] >> PairCases_on `x` >> gvs[] >>
    rpt (TOP_CASE_TAC >> gvs[])
    )
  >- (TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[])
  >- (TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[])
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[]
    )
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[]
    )
QED

Theorem pmatch_nsAppend_No_match = pmatch_nsAppend |> cj 1 |> cj 1;
Theorem pmatch_nsAppend_Match = pmatch_nsAppend |> cj 1 |> cj 2;

Theorem pmatch_acc:
  (!envc store p v env env' env2.
    (pmatch envc store p v env = Match env' ⇔
     pmatch envc store p v (env++env2) = Match (env'++env2)) ∧
    (pmatch envc store p v env = No_match ⇔
     pmatch envc store p v (env++env2) = No_match) ∧
    (pmatch envc store p v env = Match_type_error ⇔
     pmatch envc store p v (env++env2) = Match_type_error)) ∧
  (!envc store ps vs env env' env2.
    (pmatch_list envc store ps vs env = Match env' ⇔
     pmatch_list envc store ps vs (env++env2) = Match (env'++env2)) ∧
    (pmatch_list envc store ps vs env = No_match ⇔
     pmatch_list envc store ps vs (env++env2) = No_match) ∧
    (pmatch_list envc store ps vs env = Match_type_error ⇔
     pmatch_list envc store ps vs (env++env2) = Match_type_error))
Proof
 ho_match_mp_tac pmatch_ind
 >> rw [pmatch_def]
 >- (every_case_tac >> rw [])
 >- (every_case_tac >> rw [])
 >- (every_case_tac >> rw [])
 >- (every_case_tac >> rw [])
 >- (every_case_tac >> rw [])
 >- (every_case_tac >> rw [])
 >> rpt (CASE_TAC >> rw [])
 >> metis_tac [match_result_distinct, match_result_11]
QED

val eqs = LIST_CONJ (map TypeBase.case_eq_of
  [``:op``, ``:'a list``, ``:'a option``, ``:v``, ``:'a store_v``, ``:lit``,
   ``:eq_result``, ``:word_size``])

Theorem pair_case_eq[local]:
  pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v
Proof
  Cases_on `x` >>
 srw_tac[][]
QED

Theorem pair_lam_lem[local]:
  !f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)
Proof
  srw_tac[][]
QED

Theorem do_app_cases =
  ``do_app (s,t) op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV)

Theorem do_opapp_cases:
   ∀env' vs v.
    (do_opapp vs = SOME (env',v))
    =
  ((∃v2 env'' n e.
    (vs = [Closure env'' n e; v2]) ∧
    (env' = env'' with <| v := nsBind n v2 env''.v |>) ∧ (v = e)) ∨
  (?v2 env'' funs n' n'' e.
    (vs = [Recclosure env'' funs n'; v2]) ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (ALL_DISTINCT (MAP (\ (f,x,e). f) funs)) ∧
    (env' = env'' with <| v :=  nsBind n'' v2 (build_rec_env funs env'' env''.v) |> ∧ (v = e))))
Proof
  gvs [AllCaseEqs(),do_opapp_def] \\ rpt strip_tac \\ gvs [] >>
  cases_on `vs` >> srw_tac[][] >>
  Cases_on ‘t’ \\ fs [] \\ Cases_on ‘h’ \\ fs [] >>
  eq_tac \\ rw [] \\ fs []
QED

Theorem do_app_NONE_ffi:
   do_app (refs,ffi) op args = NONE ⇒
   do_app (refs,ffi') op args = NONE
Proof
  Cases_on `op` \\ fs [do_app_def,thunk_op_def]
  \\ gvs [AllCaseEqs()] \\ rpt strip_tac \\ gvs []
  \\ rpt (pairarg_tac \\ gvs[])
  \\ every_case_tac \\ fs[]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
QED

Theorem do_app_SOME_ffi_same:
   do_app (refs,ffi) op args = SOME ((refs',ffi),r)
   ∧ (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome))) ⇒
   do_app (refs,ffi') op args = SOME ((refs',ffi'),r)
Proof
  rw[]
  \\ gvs [do_app_def,AllCaseEqs(),thunk_op_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ fs[ffiTheory.call_FFI_def]
  \\ gvs [do_app_def,AllCaseEqs()]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
  \\ rveq \\ fs[ffiTheory.ffi_state_component_equality]
QED

Theorem do_app_ffi_unchanged:
  ∀st ffi op vs st' ffi' res.
    (∀s. op ≠ FFI s) ∧
    do_app (st, ffi) op vs = SOME ((st', ffi'), res)
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >> simp[do_app_def,thunk_op_def] >>
  Cases_on ‘op’ >> simp[] >> Cases_on ‘vs’ >> simp[] >>
  dsimp[AllCaseEqs(), PULL_EXISTS] >>
  simp[store_alloc_def]
QED

Theorem do_app_ffi_changed:
  do_app (st, ffi) op vs = SOME ((st', ffi'), res) ∧
  ffi ≠ ffi' ⇒
  ∃s conf lnum ws ffi_st ws' b.
    op = FFI s ∧
    vs = [Litv (StrLit conf); Loc b lnum] ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ «» ∧
    ffi.oracle
       (ExtCall s)
       ffi.ffi_state
       (MAP (λc. n2w $ ORD c) (explode conf))
       ws =
    Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event (ExtCall s) (MAP (λc. n2w $ ORD c) (explode conf))
                  (ZIP (ws,ws'))]
Proof
  simp[do_app_def,thunk_op_def] >>
  Cases_on ‘op’ >> simp[] >> Cases_on ‘vs’ >> simp[] >>
  dsimp[AllCaseEqs(), PULL_EXISTS, UNCURRY_EQ] >>
  simp[call_FFI_def, AllCaseEqs(), SF CONJ_ss] >>
  rw[] >>
  gvs[combinTheory.o_DEF, store_assign_def]
QED

Theorem do_app_not_timeout:
  do_app s op vs = SOME (s', Rerr (Rabort a))
  ⇒
  a ≠ Rtimeout_error
Proof
  Cases_on `s` >>
  srw_tac[][do_app_cases,thunk_op_def,AllCaseEqs(),store_alloc_def] >>
  gvs []
QED

Theorem do_app_type_error:
  do_app s op es = SOME (x,Rerr (Rabort a)) ⇒ x = s
Proof
  PairCases_on `s` >>
  simp[do_app_def,thunk_op_def] >>
  Cases_on ‘op’ >> simp[] >> Cases_on ‘es’ >> simp[] >>
  dsimp[AllCaseEqs(), PULL_EXISTS, UNCURRY_EQ]
QED

Theorem build_rec_env_help_lem[local]:
  ∀funs env funs'.
    FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env funs' f) env') env' funs =
    nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs' f)) funs)) env'
Proof
  Induct >>
 srw_tac[][] >>
 PairCases_on `h` >>
 srw_tac[][]
QED

(* Alternate definition for build_rec_env *)
Theorem build_rec_env_merge:
 ∀funs funs' env env'.
  build_rec_env funs env env' =
  nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs f)) funs)) env'
Proof
srw_tac[][build_rec_env_def, build_rec_env_help_lem]
QED

Theorem do_con_check_build_conv:
 !tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v
Proof
srw_tac[][do_con_check_def, build_conv_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[]
QED

Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End

Theorem map_error_result_Rtype_error[simp]:
   map_error_result f e = (Rabort a) ⇔ e = Rabort a
Proof
  Cases_on`e`>>simp[]
QED

Theorem map_error_result_I[simp]:
   map_error_result I e = e
Proof
  Cases_on`e`>>EVAL_TAC
QED

Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End

Theorem map_result_Rval[simp]:
   map_result f1 f2 e = Rval x ⇔ ∃y. e = Rval y ∧ x = f1 y
Proof
  Cases_on`e`>>simp[EQ_IMP_THM]
QED

Theorem map_result_Rerr[simp]:
   map_result f1 f2 e = Rerr e' ⇔ ∃a. e = Rerr a ∧ map_error_result f2 a = e'
Proof
  Cases_on`e`>>simp[EQ_IMP_THM]
QED

Definition exc_rel_def[simp]:
  (exc_rel R (Rraise v1) (Rraise v2) = R v1 v2) ∧
  (exc_rel _ (Rabort a1) (Rabort a2) ⇔ a1 = a2) ∧
  (exc_rel _ _ _ = F)
End

Theorem exc_rel_raise1[simp]:
   exc_rel R (Rraise v) e = ∃v'. (e = Rraise v') ∧ R v v'
Proof
  Cases_on`e`>>srw_tac[][]
QED
Theorem exc_rel_raise2[simp]:
   exc_rel R e (Rraise v) = ∃v'. (e = Rraise v') ∧ R v' v
Proof
  Cases_on`e`>>srw_tac[][]
QED
Theorem exc_rel_type_error1[simp]:
   (exc_rel R (Rabort a) e = (e = Rabort a))
Proof
  Cases_on`e`>>srw_tac[][]>>metis_tac []
QED
Theorem exc_rel_type_error2[simp]:
   (exc_rel R e (Rabort a) = (e = Rabort a))
Proof
  Cases_on`e`>>srw_tac[][]>>metis_tac []
QED

Theorem exc_rel_refl[simp]:
   (∀x. R x x) ⇒ ∀x. exc_rel R x x
Proof
strip_tac >> Cases >> srw_tac[][]
QED

Theorem exc_rel_trans:
 (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. exc_rel R x y ∧ exc_rel R y z ⇒ exc_rel R x z)
Proof
srw_tac[][] >>
Cases_on `x` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> PROVE_TAC[]
QED

Definition result_rel_def[simp]:
(result_rel R1 _ (Rval v1) (Rval v2) = R1 v1 v2) ∧
(result_rel _ R2 (Rerr e1) (Rerr e2) = exc_rel R2 e1 e2) ∧
(result_rel _ _ _ _ = F)
End

Theorem result_rel_Rval[simp]:
 result_rel R1 R2 (Rval v) r = ∃v'. (r = Rval v') ∧ R1 v v'
Proof
Cases_on `r` >> srw_tac[][]
QED
Theorem result_rel_Rerr1[simp]:
 result_rel R1 R2 (Rerr e) r = ∃e'. (r = Rerr e') ∧ exc_rel R2 e e'
Proof
Cases_on `r` >> srw_tac[][EQ_IMP_THM]
QED
Theorem result_rel_Rerr2[simp]:
 result_rel R1 R2 r (Rerr e) = ∃e'. (r = Rerr e') ∧ exc_rel R2 e' e
Proof
Cases_on `r` >> srw_tac[][EQ_IMP_THM]
QED

Theorem result_rel_refl[simp]:
 (∀x. R1 x x) ∧ (∀x. R2 x x) ⇒ ∀x. result_rel R1 R2 x x
Proof
strip_tac >> Cases >> srw_tac[][]
QED

Theorem result_rel_trans:
 (∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀x y z. R2 x y ∧ R2 y z ⇒ R2 x z) ⇒ (∀x y z. result_rel R1 R2 x y ∧ result_rel R1 R2 y z ⇒ result_rel R1 R2 x z)
Proof
srw_tac[][] >>
Cases_on `x` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> PROVE_TAC[exc_rel_trans]
QED

Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End

Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End

Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End

Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End
Definition is_Refv_def[simp]:
  is_Refv (Refv _) = T ∧
  is_Refv _ = F
End

Definition sv_every_def[simp]:
  sv_every P (Refv v) = P v ∧
  sv_every P (Varray vs) = EVERY P vs ∧
  sv_every P (Thunk m v) = P v ∧
  sv_every P _ = T
End

Definition sv_rel_def[simp]:
  sv_rel R (Refv v1) (Refv v2) = R v1 v2 ∧
  sv_rel R (W8array w1) (W8array w2) = (w1 = w2) ∧
  sv_rel R (Varray vs1) (Varray vs2) = LIST_REL R vs1 vs2 ∧
  sv_rel R (Thunk m1 v1) (Thunk m2 v2) = (m1 = m2 ∧ R v1 v2) ∧
  sv_rel R _ _ = F
End

Theorem sv_rel_refl[simp]:
   ∀R x. (∀x. R x x) ⇒ sv_rel R x x
Proof
  gen_tac >> Cases >> srw_tac[][sv_rel_def] >>
  induct_on `l` >>
  srw_tac[][]
QED

Theorem sv_rel_trans:
   ∀R. (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ ∀x y z. sv_rel R x y ∧ sv_rel R y z ⇒ sv_rel R x z
Proof
  gen_tac >> strip_tac >> Cases >> Cases >> Cases >> srw_tac[][] >> full_simp_tac(srw_ss())[sv_rel_def] >> metis_tac[LIST_REL_trans]
QED

Theorem sv_rel_cases:
   ∀x y.
    sv_rel R x y ⇔
    (∃v1 v2. x = Refv v1 ∧ y = Refv v2 ∧ R v1 v2) ∨
    (∃w. x = W8array w ∧ y = W8array w) ∨
    (∃m v1 v2. x = Thunk m v1 ∧ y = Thunk m v2 ∧ R v1 v2) ∨
    (?vs1 vs2. x = Varray vs1 ∧ y = Varray vs2 ∧ LIST_REL R vs1 vs2)
Proof
  Cases >> Cases >> simp[sv_rel_def,EQ_IMP_THM] >> metis_tac []
QED

Theorem sv_rel_O:
   ∀R1 R2. sv_rel (R1 O R2) = sv_rel R1 O sv_rel R2
Proof
  srw_tac[][FUN_EQ_THM,sv_rel_cases,O_DEF,EQ_IMP_THM, LIST_REL_O] >>
   metis_tac[]
QED

Theorem sv_rel_mono:
   (∀x y. P x y ⇒ Q x y) ⇒ sv_rel P x y ⇒ sv_rel Q x y
Proof
  srw_tac[][sv_rel_cases] >> metis_tac [LIST_REL_mono]
QED

Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End

Definition store_vs_def:
  store_vs s = FLAT (MAP store_v_vs s)
End

Theorem EVERY_sv_every_MAP_map_sv:
   ∀P f ls. EVERY P (MAP f (store_vs ls)) ⇒ EVERY (sv_every P) (MAP (map_sv f) ls)
Proof
  rpt gen_tac >>
  simp[EVERY_MAP,EVERY_MEM,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
  strip_tac >> Cases >> simp[] >> srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem LIST_REL_store_vs_intro:
   ∀P l1 l2. LIST_REL (sv_rel P) l1 l2 ⇒ LIST_REL P (store_vs l1) (store_vs l2)
Proof
  gen_tac >>
  Induct >- simp[store_vs_def] >>
  Cases >> simp[PULL_EXISTS,sv_rel_cases] >>
  full_simp_tac(srw_ss())[store_vs_def] >> srw_tac[][] >>
  match_mp_tac rich_listTheory.EVERY2_APPEND_suff >> simp[]
QED

Theorem EVERY_sv_every_EVERY_store_vs:
   ∀P ls. EVERY (sv_every P ) ls ⇔ EVERY P (store_vs ls)
Proof
  srw_tac[][EVERY_MEM,EQ_IMP_THM,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >>
  res_tac >> TRY(Cases_on`e`) >> TRY(Cases_on`y`) >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[EVERY_MEM]
QED

Theorem EVERY_store_vs_intro:
   ∀P ls. EVERY (sv_every P) ls ⇒ EVERY P (store_vs ls)
Proof
  srw_tac[][EVERY_MEM,store_vs_def,MEM_MAP,MEM_FILTER,MEM_FLAT] >>
  res_tac >>
  qmatch_assum_rename_tac`sv_every P x` >>
  Cases_on`x`>>full_simp_tac(srw_ss())[EVERY_MEM]
QED

Theorem map_sv_compose:
   map_sv f (map_sv g x) = map_sv (f o g) x
Proof
  Cases_on`x`>>simp[MAP_MAP_o]
QED

Definition map_match_def[simp]:
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)
End

Theorem find_recfun_ALOOKUP:
 ∀funs n. find_recfun n funs = ALOOKUP funs n
Proof
Induct >- srw_tac[][semanticPrimitivesTheory.find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
srw_tac[][semanticPrimitivesTheory.find_recfun_def]
QED

Theorem find_recfun_el:
   !f funs x e n.
    ALL_DISTINCT (MAP (\ (f,x,e). f) funs) ∧
    n < LENGTH funs ∧
    EL n funs = (f,x,e)
    ⇒
    find_recfun f funs = SOME (x,e)
Proof
  simp[find_recfun_ALOOKUP] >>
  induct_on `funs` >>
  srw_tac[][] >>
  cases_on `n` >>
  full_simp_tac(srw_ss())[] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  full_simp_tac(srw_ss())[MEM_MAP, MEM_EL, FORALL_PROD] >>
  metis_tac []
QED

Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End

Definition ctors_of_dec_def[simp]:
  ctors_of_dec (Dtype locs tds) = FLAT (MAP ctors_of_tdef tds) ∧
  ctors_of_dec (Dexn locs s _) = [s] ∧
  ctors_of_dec _ = []
End

(* free vars *)

Definition FV_def[simp]:
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
  (FV (Tannot e t) = FV e) ∧
  (FV (Lannot e l) = FV e) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p)))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)
End

Overload SFV = ``λe. {x | Short x ∈ FV e}``

Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p)))) (set pes))
Proof
  Induct_on`pes`>>simp[]>>
  qx_gen_tac`p`>>PairCases_on`p`>>srw_tac[][]
QED

Theorem FV_defs_MAP:
   ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))
Proof
  Induct_on`ls`>>simp[FORALL_PROD]
QED

Definition FV_dec_def[simp]:
  (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
  (FV_dec (Dtype _ _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
  (FV_dec (Dexn _ _ _) = {})
End

Theorem nat_to_v_11[simp]:
  !i j. nat_to_v i = nat_to_v j <=> i = j
Proof
  simp [nat_to_v_def]
QED

Theorem concrete_v_list[simp]:
  !xs. concrete_v_list xs = EVERY concrete_v xs
Proof
  Induct \\ simp [concrete_v_def]
QED

Theorem concrete_v_simps[simp]:
  (concrete_v (Litv l) = T) /\
  (concrete_v (Loc b n) = T) /\
  (concrete_v (Conv stmp xs) = EVERY concrete_v xs) /\
  (concrete_v (Vectorv xs) = EVERY concrete_v xs) /\
  (concrete_v (Env id e) = F) /\
  (concrete_v (Closure e2 nm x) = F) /\
  (concrete_v (Recclosure e3 funs nm2) = F)
Proof
  simp [concrete_v_def]
QED

Theorem prim_type_cases:
  ∀ty.
    ty = BoolT ∨
    ty = IntT ∨
    ty = CharT ∨
    ty = StrT ∨
    ty = WordT W8 ∨
    ty = WordT W64 ∨
    ty = Float64T
Proof
  Cases \\ fs [] \\ Cases_on ‘w’ \\ fs []
QED

Theorem do_conversion_check_type:
  do_conversion v ty1 ty2 = SOME (INR res) ⇒
  check_type ty2 res
Proof
  Cases_on ‘ty2’ using prim_type_cases
  \\ gvs [oneline do_conversion_def, AllCaseEqs()]
  \\ rw [] \\ fs [semanticPrimitivesTheory.check_type_def]
QED

Theorem do_arith_check_type:
  do_arith a ty vs = SOME (INR res) ⇒
  check_type ty res
Proof
  Cases_on ‘ty’ using prim_type_cases
  \\ gvs [oneline do_arith_def, AllCaseEqs()]
  \\ rw [] \\ fs [semanticPrimitivesTheory.check_type_def]
QED

Definition is_clos_def:
  (is_clos (Closure _ _ _) ⇔ T) ∧
  (is_clos (Recclosure _ _ _) ⇔ T) ∧
  (is_clos _ ⇔ F)
End

Theorem is_clos_iff:
  is_clos x ⇔
  (∃a b c. x = Closure a b c) ∨
  (∃a b c. x = Recclosure a b c)
Proof
  Cases_on`x`>>fs[is_clos_def]
QED

(* Preservation for a generalized value relation *)
Definition simple_val_rel_def:
  simple_val_rel vr ⇔
  ∀x y. vr x y ⇔
  case y of
    Conv stmp ys =>
    ∃xs. x = Conv stmp xs ∧ LIST_REL vr xs ys
  | Vectorv ys =>
    ∃xs. x = Vectorv xs ∧ LIST_REL vr xs ys
  | Closure _ _ _ => is_clos x
  | Recclosure _ _ _ => is_clos x
  | Env envy id => ∃envx. x = Env envx id
  | gv => x = y
End

Theorem simple_val_rel_vr:
  simple_val_rel vr ∧
  vr x y ⇒
  case y of
    Conv stmp ys =>
    ∃xs. x = Conv stmp xs ∧ LIST_REL vr xs ys
  | Vectorv ys =>
    ∃xs. x = Vectorv xs ∧ LIST_REL vr xs ys
  | Closure _ _ _ => is_clos x
  | Recclosure _ _ _ => is_clos x
  | Env envy id => ∃envx. x = Env envx id
  | gv => x = y
Proof
  rw[simple_val_rel_def]>>
  metis_tac[]
QED

Theorem ctor_same_type_refl:
  ctor_same_type x x
Proof
  rw[ctor_same_type_def] >>
  every_case_tac>>simp[]>>
  Cases_on`x'`>>EVAL_TAC
QED

Theorem do_eq_sym:
  (∀x y.
  do_eq x y = Eq_val T ⇒
  do_eq y x = Eq_val T) ∧
  (∀xs ys.
  do_eq_list xs ys = Eq_val T ⇒
  do_eq_list ys xs = Eq_val T)
Proof
  ho_match_mp_tac do_eq_ind>>
  rw[do_eq_def]>>
  fs[]
  >- (
    fs[lit_same_type_def]>>
    every_case_tac>>fs[])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
QED

Theorem do_eq_trans:
  (∀x y z.
  do_eq x y = Eq_val T ∧
  do_eq y z = Eq_val T ⇒
  do_eq x z = Eq_val T) ∧
  (∀xs ys zs.
  do_eq_list xs ys = Eq_val T ∧
  do_eq_list ys zs = Eq_val T ⇒
  do_eq_list xs zs = Eq_val T)
Proof
  ho_match_mp_tac do_eq_ind>>
  reverse (rw[do_eq_def])>>
  fs[]
  >- (
    every_case_tac>>gvs[]>>
    Cases_on`zs`>>gvs[do_eq_def]>>
    last_x_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[])
  >- (
    Cases_on`z`>>fs[do_eq_def]>>
    Cases_on`p`>>fs[do_eq_def])
  >>
  Cases_on`z`>>gvs[do_eq_def]>>
  every_case_tac>>fs[]
QED

(* Note: this cannot be strengthened to do_eq x y = Eq_val T, because
   do_eq (Loc F n) (Loc F n) = Eq_type_error. *)
Theorem simple_val_rel_do_eq:
  simple_val_rel vr ⇒
  (∀x y.
    vr x y ⇒
    do_eq x y = do_eq y y) ∧
  (∀xs ys.
    LIST_REL vr xs ys ⇒
    do_eq_list xs ys = do_eq_list ys ys)
Proof
  strip_tac>>
  ho_match_mp_tac do_eq_ind>>
  rw[]>>
  imp_res_tac simple_val_rel_vr>>
  gvs[]>>
  rw[do_eq_def]>>
  gvs[LIST_REL_EL_EQN,is_clos_iff]>>
  TOP_CASE_TAC>>gvs[]>>
  IF_CASES_TAC>>gvs[]
QED

Theorem simple_val_rel_do_eq_2:
  simple_val_rel vr ⇒
  (∀x y a b.
    vr x y ∧
    vr a b ⇒
    do_eq y b = do_eq x a) ∧
  (∀xs ys as bs.
    LIST_REL vr xs ys ∧
    LIST_REL vr as bs ⇒
    do_eq_list ys bs = do_eq_list xs as)
Proof
  strip_tac>>
  ho_match_mp_tac do_eq_ind>>
  reverse(rw[])
  >- (
    Cases_on`bs`>>
    gvs[do_eq_def]>>
    last_x_assum drule>>
    rw[]>>
    TOP_CASE_TAC>>gs[]>>
    TOP_CASE_TAC>>gs[]>>
    `do_eq y y = Eq_val T` by metis_tac[do_eq_sym,do_eq_trans]>>
    `do_eq x y = Eq_val T` by metis_tac[simple_val_rel_do_eq]>>
    gvs[])
  >- (
    Cases_on`bs`>>
    gvs[do_eq_def])>>
  imp_res_tac simple_val_rel_vr>>
  gvs[]>>
  Cases_on`b`>>gvs[do_eq_def,is_clos_iff]>>
  every_case_tac>>gvs[do_eq_def,is_clos_iff]>>
  imp_res_tac LIST_REL_LENGTH>>
  gvs[ctor_same_type_refl]>>
  Cases_on`p`>>gvs[do_eq_def]
QED

Theorem vr_v_to_char_list:
  simple_val_rel vr ⇒
  ∀y x.
  vr x y ⇒
  v_to_char_list x = v_to_char_list y
Proof
  strip_tac>>
  ho_match_mp_tac v_to_char_list_ind>>
  rw[]>>
  imp_res_tac simple_val_rel_vr>>
  gvs[]>>
  simp[v_to_char_list_def]>>
  imp_res_tac simple_val_rel_vr>>
  gvs[]>>
  simp[v_to_char_list_def]>>
  fs[is_clos_iff,v_to_char_list_def]
QED

Theorem LIST_REL_vr_vs_to_string:
  simple_val_rel vr ⇒
  ∀ys xs.
  LIST_REL vr xs ys ⇒
  vs_to_string xs = vs_to_string ys
Proof
  strip_tac>>
  ho_match_mp_tac vs_to_string_ind>>
  rw[]>>
  imp_res_tac simple_val_rel_vr>>
  gvs[is_clos_iff]>>
  rw[vs_to_string_def]
QED

Theorem vr_v_to_list:
  simple_val_rel vr ⇒
  ∀y x.
  vr x y ⇒
  OPTREL (LIST_REL vr) (v_to_list x) (v_to_list y)
Proof
  strip_tac>>
  ho_match_mp_tac v_to_list_ind>>
  rw[]>>
  imp_res_tac simple_val_rel_vr>>
  gvs[is_clos_iff]>>
  simp[v_to_list_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>fs[]
QED

Theorem LIST_REL_OPTREL_store_lookup:
  LIST_REL R s t ⇒
  OPTREL R
  (store_lookup n s)
  (store_lookup n t)
Proof
  rw[store_lookup_def]>>
  metis_tac[LIST_REL_EL_EQN]
QED

Theorem LIST_REL_store_lookup:
  LIST_REL R s t ⇒
  (store_lookup n t = NONE ⇒ store_lookup n s = NONE) ∧
  (store_lookup n t = SOME y ⇒
  ∃x. store_lookup n s = SOME x ∧ R x y)
Proof
  rw[store_lookup_def]>>
  metis_tac[LIST_REL_EL_EQN]
QED

Theorem sv_rel_store_v_same_type:
  (sv_rel R) x y ∧
  (sv_rel R) w z ⇒
  (store_v_same_type x w ⇔ store_v_same_type y z)
Proof
  rw[sv_rel_cases]>>
  EVAL_TAC
QED

Theorem LIST_REL_store_assign_NONE:
  LIST_REL (sv_rel R) s t ∧
  sv_rel R z w ∧
  store_assign n w t = NONE ⇒
  store_assign n z s = NONE
Proof
  rw[store_assign_def]>>
  metis_tac[sv_rel_store_v_same_type,LIST_REL_EL_EQN]
QED

Theorem LIST_REL_store_assign_SOME:
  LIST_REL (sv_rel R) s t ∧
  sv_rel R z w ∧
  store_assign n w t = SOME y ⇒
  ∃x. store_assign n z s = SOME x ∧ LIST_REL (sv_rel R) x y
Proof
  rw[store_assign_def]
  >- metis_tac[sv_rel_store_v_same_type,LIST_REL_EL_EQN]
  >- metis_tac[sv_rel_store_v_same_type,LIST_REL_EL_EQN]
  >- metis_tac[EVERY2_LUPDATE_same]
QED

Theorem store_assign_sv_rel:
  LIST_REL (sv_rel R) sa sb ∧ sv_rel R z w ⇒
  (store_assign n z sa = NONE ⇔ store_assign n w sb = NONE) ∧
  (∀sb2. store_assign n w sb = SOME sb2 ⇒
     ∃sa2. store_assign n z sa = SOME sa2 ∧ LIST_REL (sv_rel R) sa2 sb2)
Proof
  rw[store_assign_def]>>
  imp_res_tac LIST_REL_LENGTH>>gvs[]>>
  metis_tac[sv_rel_store_v_same_type,LIST_REL_EL_EQN,EVERY2_LUPDATE_same]
QED

Theorem store_assign_NONE_Refv:
  LIST_REL (sv_rel R) sa sb ∧ R x y ∧ store_assign n (Refv y) sb = NONE ⇒
  store_assign n (Refv x) sa = NONE
Proof
  rw[]>>irule LIST_REL_store_assign_NONE>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_NONE_W8:
  LIST_REL (sv_rel R) sa sb ∧ store_assign n (W8array w) sb = NONE ⇒
  store_assign n (W8array w) sa = NONE
Proof
  rw[]>>irule LIST_REL_store_assign_NONE>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_NONE_Varray:
  LIST_REL (sv_rel R) sa sb ∧ LIST_REL R xs ys ∧
  store_assign n (Varray ys) sb = NONE ⇒
  store_assign n (Varray xs) sa = NONE
Proof
  rw[]>>irule LIST_REL_store_assign_NONE>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_Thunk_NONE:
  LIST_REL (sv_rel R) sa sb ∧ R v w ⇒
  (store_assign n (Thunk m v) sa = NONE ⇔ store_assign n (Thunk m w) sb = NONE)
Proof
  rw[]>>irule (cj 1 store_assign_sv_rel)>>
  qexists_tac`R`>>simp[]
QED

Theorem store_assign_Thunk_SOME:
  LIST_REL (sv_rel R) sa sb ∧ R v w ∧ store_assign n (Thunk m w) sb = SOME sb2 ⇒
  ∃sa2. store_assign n (Thunk m v) sa = SOME sa2 ∧ LIST_REL (sv_rel R) sa2 sb2
Proof
  rw[]>>irule (cj 2 store_assign_sv_rel)>>
  first_x_assum (irule_at Any)>>simp[]
QED

(* The shape of a related value is determined by the value it is related to. *)
Theorem simple_val_rel_cases:
  simple_val_rel vr ⇒
  (∀x l. vr x (Litv l) ⇔ x = Litv l) ∧
  (∀x b n. vr x (Loc b n) ⇔ x = Loc b n) ∧
  (∀x stmp ys. vr x (Conv stmp ys) ⇔ ∃xs. x = Conv stmp xs ∧ LIST_REL vr xs ys) ∧
  (∀x ys. vr x (Vectorv ys) ⇔ ∃xs. x = Vectorv xs ∧ LIST_REL vr xs ys) ∧
  (∀x e n b. vr x (Closure e n b) ⇔ is_clos x) ∧
  (∀x e f n. vr x (Recclosure e f n) ⇔ is_clos x) ∧
  (∀x e id. vr x (Env e id) ⇔ ∃envx. x = Env envx id)
Proof
  simp[simple_val_rel_def]>>rw[]
QED

Theorem simple_val_rel_check_type:
  simple_val_rel vr ∧ vr x y ∧ check_type ty y ⇒ x = y
Proof
  rw[]>> drule_all simple_val_rel_vr>>
  Cases_on`ty` using prim_type_cases>>
  gvs[check_type_def,Boolv_def]>>
  every_case_tac>>gvs[]
QED

Theorem simple_val_rel_check_type_iff:
  simple_val_rel vr ∧ vr x y ⇒ (check_type ty x ⇔ check_type ty y)
Proof
  rw[]>> drule_all simple_val_rel_vr>>
  Cases_on`ty` using prim_type_cases>>
  gvs[check_type_def,Boolv_def]>>
  every_case_tac>>rw[]>>gvs[is_clos_iff]>>
  Cases_on`xs`>>gvs[]
QED

Theorem simple_val_rel_check_type_split:
  simple_val_rel vr ∧ vr x y ⇒ x = y ∨ (¬check_type ty x ∧ ¬check_type ty y)
Proof
  rw[]>>Cases_on`check_type ty y`
  >- metis_tac[simple_val_rel_check_type]>>
  metis_tac[simple_val_rel_check_type_iff]
QED

Theorem LIST_REL_check_type:
  simple_val_rel vr ⇒
  ∀xs ys. LIST_REL vr xs ys ∧ EVERY (check_type ty) ys ⇒ xs = ys
Proof
  strip_tac>> Induct_on`LIST_REL`>>rw[]>>
  metis_tac[simple_val_rel_check_type]
QED

Theorem LIST_REL_EVERY_check_type:
  simple_val_rel vr ⇒
  ∀xs ys. LIST_REL vr xs ys ⇒
    (EVERY (check_type ty) xs ⇔ EVERY (check_type ty) ys)
Proof
  strip_tac>> Induct_on`LIST_REL`>>rw[]>>
  metis_tac[simple_val_rel_check_type_iff]
QED

Theorem simple_val_rel_dest_Litv:
  simple_val_rel vr ∧ vr x y ⇒ dest_Litv x = dest_Litv y
Proof
  rw[]>>drule_all simple_val_rel_vr>>
  Cases_on`y`>>gvs[]>>rw[]>>gvs[is_clos_iff]>>gvs[]
QED

Theorem simple_val_rel_do_test:
  simple_val_rel vr ∧ vr x y ∧ vr a b ⇒
  do_test tst ty y b = do_test tst ty x a
Proof
  strip_tac>>
  Cases_on`tst`>>
  gvs[do_test_def]>>
  imp_res_tac simple_val_rel_dest_Litv>>
  gvs[]>>
  `(check_type ty x ⇔ check_type ty y) ∧ (check_type ty a ⇔ check_type ty b)`
     by metis_tac[simple_val_rel_check_type_iff]>>
  gvs[]>>
  IF_CASES_TAC>>gvs[]>>
  `x = y ∧ a = b` by metis_tac[simple_val_rel_check_type]>>
  gvs[]
QED

Theorem vr_v_to_list_NONE:
  simple_val_rel vr ∧ vr x y ∧ v_to_list y = NONE ⇒ v_to_list x = NONE
Proof
  rw[]>>drule vr_v_to_list>>disch_then drule>>gvs[OPTREL_def]
QED

Theorem vr_v_to_list_SOME:
  simple_val_rel vr ∧ vr x y ∧ v_to_list y = SOME l ⇒
  ∃xl. v_to_list x = SOME xl ∧ LIST_REL vr xl l
Proof
  rw[]>>drule vr_v_to_list>>disch_then drule>>gvs[OPTREL_def]
QED

Theorem simple_val_rel_bad_thunk_update:
  simple_val_rel vr ∧ LIST_REL (sv_rel vr) s t ∧ vr v w ⇒
  (bad_thunk_update m v s ⇔ bad_thunk_update m w t)
Proof
  rw[bad_thunk_update_def]>>
  drule_all simple_val_rel_vr>>
  Cases_on`w`>>gvs[dest_thunk_def,is_clos_iff]>>
  rw[]>>gvs[dest_thunk_def]>>
  imp_res_tac LIST_REL_OPTREL_store_lookup>>
  pop_assum (qspec_then`n` mp_tac)>>
  simp[OPTREL_def]>>
  rw[]>>simp[]>>
  gvs[sv_rel_cases]>>
  every_case_tac>>gvs[]
QED

Theorem simple_val_rel_thunk_op:
  simple_val_rel vr ∧ LIST_REL (sv_rel vr) sa sb ∧ LIST_REL vr xs ys ⇒
  (thunk_op (sb,ffi) th_op ys =
     (NONE:((v store_v list # 'ffi ffi_state) # (v,v) result) option) ⇒
   thunk_op (sa,ffi) th_op xs = NONE) ∧
  (∀sb2 ffi2 rb. thunk_op (sb,ffi) th_op ys = SOME ((sb2,ffi2),rb) ⇒
     ∃sa2 ra. thunk_op (sa,ffi) th_op xs = SOME ((sa2,ffi2),ra) ∧
              LIST_REL (sv_rel vr) sa2 sb2 ∧ result_rel vr vr ra rb)
Proof
  strip_tac>>
  `∀m v w. vr v w ⇒ (bad_thunk_update m v sa ⇔ bad_thunk_update m w sb)`
     by metis_tac[simple_val_rel_bad_thunk_update]>>
  Cases_on`th_op`>>
  Cases_on`ys`>>gvs[thunk_op_def]>>
  rename1`LIST_REL vr _ ytl`>>
  Cases_on`ytl`>>gvs[thunk_op_def]>>
  every_case_tac>>
  gvs[simple_val_rel_cases,store_alloc_def,is_clos_iff]>>
  imp_res_tac LIST_REL_LENGTH>>gvs[]>>
  first_x_assum drule>>strip_tac>>gvs[]>>
  imp_res_tac store_assign_Thunk_NONE>>
  imp_res_tac store_assign_Thunk_SOME>>
  gvs[]
QED

Theorem simple_val_rel_thunk_op_NONE =
  simple_val_rel_thunk_op |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL

Theorem simple_val_rel_thunk_op_SOME =
  simple_val_rel_thunk_op |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> DISCH_ALL

Theorem simple_val_rel_do_app_rev_NONE:
  simple_val_rel vr ∧
  LIST_REL (sv_rel vr) s t ∧
  LIST_REL vr xs ys ∧
  do_app (t,ffi) op ys = NONE ⇒
  do_app (s,ffi) op xs = NONE
Proof
  strip_tac>>gvs[]>>
  qpat_x_assum`do_app _ _ _ = NONE` mp_tac>>
  simp[Once do_app_def]>>
  strip_tac>>
  gvs[AllCaseEqs(),simple_val_rel_cases,is_clos_iff]>>
  simp[do_app_def]>>
  imp_res_tac LIST_REL_store_lookup>>
  gvs[sv_rel_cases,store_alloc_def]
  >>~- (
    [`do_arith`],
    IF_CASES_TAC>>gvs[]>>
    TRY (drule LIST_REL_check_type>>disch_then drule>>
         disch_then (qspec_then`ty` mp_tac)>>simp[]>>NO_TAC)>>
    drule LIST_REL_EVERY_check_type>>disch_then drule>>
    disch_then (qspec_then`ty` mp_tac)>>simp[]>>
    strip_tac>>
    gvs[NOT_EVERY,combinTheory.o_DEF,EVERY_MEM,EXISTS_MEM])
  >>~- (
    [`do_conversion`],
    IF_CASES_TAC>>simp[]>>
    drule simple_val_rel_check_type_split>>disch_then drule>>
    disch_then (qspec_then`ty1` strip_assume_tac)>>gvs[])
  >>~- (
    [`do_eq`],
    drule simple_val_rel_do_eq_2>>strip_tac>>res_tac>>gvs[])
  >>~- (
    [`do_test`],
    drule simple_val_rel_do_test>>strip_tac>>res_tac>>gvs[])
  >>~- (
    [`thunk_op`],
    metis_tac[simple_val_rel_thunk_op_NONE])
  >>~- (
    [`v_to_char_list`],
    drule vr_v_to_char_list>>disch_then drule>>strip_tac>>gvs[])
  >>~- (
    [`v_to_list`],
    imp_res_tac vr_v_to_list_NONE>>imp_res_tac vr_v_to_list_SOME>>gvs[]>>
    imp_res_tac LIST_REL_vr_vs_to_string>>gvs[])>>
  imp_res_tac LIST_REL_LENGTH>>gvs[]>>
  imp_res_tac store_assign_NONE_Refv>>
  imp_res_tac store_assign_NONE_W8>>
  imp_res_tac EVERY2_LUPDATE_same>>
  imp_res_tac store_assign_NONE_Varray>>
  gvs[]
QED

Theorem simple_val_rel_rewrites:
  simple_val_rel vr ⇒
  (∀x y.
    vr (Litv x) (Litv y) ⇔ x = y) ∧
  (∀b1 x b2 y.
    vr (Loc b1 x) (Loc b2 y) ⇔ b1 = b2 ∧ x = y) ∧
  (∀a b x y.
    vr (Conv a b) (Conv x y) ⇔ a = x ∧ LIST_REL vr b y) ∧
  (∀x y.
    vr (Boolv x) (Boolv y) ⇔ x = y) ∧
  (∀x y.
    vr (Vectorv x) (Vectorv y) ⇔ LIST_REL vr x y)
Proof
  simp[simple_val_rel_def]>>
  rw[Boolv_def]>>
  rw[]
QED

Theorem simple_val_rel_list_to_v:
  simple_val_rel vr ⇒
  ∀x y.
  vr (list_to_v x) (list_to_v y) ⇔ LIST_REL vr x y
Proof
  strip_tac>>
  Induct>>rw[list_to_v_def]>>
  Cases_on`y`>>
  rw[list_to_v_def,simple_val_rel_rewrites]
QED

Theorem result_rel_Rval2:
 result_rel R1 R2 r (Rval v) = ∃v'. (r = Rval v') ∧ R1 v' v
Proof
Cases_on `r` >> srw_tac[][]
QED

Theorem store_assign_SOME_Refv:
  LIST_REL (sv_rel R) sa sb ∧ R x y ∧ store_assign n (Refv y) sb = SOME sb2 ⇒
  ∃sa2. store_assign n (Refv x) sa = SOME sa2 ∧ LIST_REL (sv_rel R) sa2 sb2
Proof
  rw[]>>irule LIST_REL_store_assign_SOME>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_SOME_W8:
  LIST_REL (sv_rel R) sa sb ∧ store_assign n (W8array w) sb = SOME sb2 ⇒
  ∃sa2. store_assign n (W8array w) sa = SOME sa2 ∧ LIST_REL (sv_rel R) sa2 sb2
Proof
  rw[]>>irule LIST_REL_store_assign_SOME>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_SOME_Varray:
  LIST_REL (sv_rel R) sa sb ∧ LIST_REL R xs ys ∧
  store_assign n (Varray ys) sb = SOME sb2 ⇒
  ∃sa2. store_assign n (Varray xs) sa = SOME sa2 ∧ LIST_REL (sv_rel R) sa2 sb2
Proof
  rw[]>>irule LIST_REL_store_assign_SOME>>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))>>simp[]
QED

Theorem store_assign_SOME_Varray_LUPDATE:
  LIST_REL (sv_rel R) sa sb ∧ LIST_REL R xs ys ∧ R x y ∧
  store_assign n (Varray (LUPDATE y k ys)) sb = SOME sb2 ⇒
  ∃sa2. store_assign n (Varray (LUPDATE x k xs)) sa = SOME sa2 ∧
        LIST_REL (sv_rel R) sa2 sb2
Proof
  rw[]>>irule store_assign_SOME_Varray>>
  first_x_assum (irule_at Any)>>
  simp[EVERY2_LUPDATE_same]
QED

Theorem simple_val_rel_check_type_refl:
  simple_val_rel vr ∧ check_type ty v ⇒ vr v v
Proof
  strip_tac>>
  Cases_on`ty` using prim_type_cases>>
  gvs[check_type_def]>>rw[]>>
  gvs[simple_val_rel_rewrites]
QED

Theorem do_arith_INL:
  do_arith a ty vs = SOME (INL exn) ⇒ exn = div_exn_v ∨ exn = chr_exn_v
Proof
  Cases_on `ty` using prim_type_cases>>
  gvs[oneline do_arith_def, AllCaseEqs()]>>rw[]>>gvs[]
QED

Theorem do_conversion_INL:
  do_conversion v ty1 ty2 = SOME (INL exn) ⇒ exn = div_exn_v ∨ exn = chr_exn_v
Proof
  Cases_on `ty2` using prim_type_cases>>
  gvs[oneline do_conversion_def, AllCaseEqs()]>>rw[]>>gvs[]
QED

Theorem simple_val_rel_do_app_rev_SOME:
  simple_val_rel vr ∧
  LIST_REL (sv_rel vr) s t ∧
  LIST_REL vr xs ys ∧
  do_app (t,ffi) op ys = SOME((t',ffi'),tres) ⇒
  ∃s' sres.
    do_app (s,ffi) op xs = SOME((s',ffi'),sres) ∧
    LIST_REL (sv_rel vr) s' t' ∧
    result_rel vr vr sres tres
Proof
  strip_tac>>gvs[]>>
  qpat_x_assum`do_app _ _ _ = SOME _` mp_tac>>
  simp[Once do_app_def]>>
  strip_tac>>
  gvs[AllCaseEqs(),simple_val_rel_cases,is_clos_iff]>>
  simp[do_app_def]>>
  imp_res_tac LIST_REL_store_lookup>>
  gvs[sv_rel_cases,store_alloc_def,simple_val_rel_rewrites,
      simple_val_rel_list_to_v,result_rel_Rval2]>>
  imp_res_tac LIST_REL_LENGTH>>gvs[]
  >>~- (
    [`do_arith`],
    drule LIST_REL_check_type>>disch_then drule>>
    disch_then (qspec_then`ty` mp_tac)>>simp[]>>strip_tac>>gvs[]>>
    imp_res_tac do_arith_INL>>
    imp_res_tac do_arith_check_type>>
    imp_res_tac simple_val_rel_check_type_refl>>
    gvs[div_exn_v_def,chr_exn_v_def,simple_val_rel_rewrites])
  >>~- (
    [`do_conversion`],
    drule simple_val_rel_check_type_split>>disch_then drule>>
    disch_then (qspec_then`ty1` strip_assume_tac)>>gvs[]>>
    imp_res_tac do_conversion_INL>>
    imp_res_tac do_conversion_check_type>>
    imp_res_tac simple_val_rel_check_type_refl>>
    gvs[div_exn_v_def,chr_exn_v_def,simple_val_rel_rewrites])
  >>~- (
    [`do_eq`],
    drule simple_val_rel_do_eq_2>>strip_tac>>res_tac>>
    gvs[simple_val_rel_rewrites])
  >>~- (
    [`do_test`],
    drule simple_val_rel_do_test>>strip_tac>>res_tac>>
    gvs[simple_val_rel_rewrites])
  >>~- (
    [`thunk_op`],
    metis_tac[simple_val_rel_thunk_op])
  >>~- (
    [`v_to_char_list`],
    drule vr_v_to_char_list>>disch_then drule>>strip_tac>>
    gvs[simple_val_rel_rewrites])
  >>~- (
    [`v_to_list`],
    imp_res_tac vr_v_to_list_NONE>>imp_res_tac vr_v_to_list_SOME>>gvs[]>>
    imp_res_tac LIST_REL_vr_vs_to_string>>
    gvs[simple_val_rel_rewrites,simple_val_rel_list_to_v]>>
    drule simple_val_rel_list_to_v>>strip_tac>>simp[]>>
    irule EVERY2_APPEND_suff>>simp[])
  >>~- (
    [`store_assign`],
    imp_res_tac store_assign_SOME_Refv>>
    imp_res_tac store_assign_SOME_W8>>
    imp_res_tac store_assign_SOME_Varray_LUPDATE>>
    imp_res_tac EVERY2_LUPDATE_same>>
    imp_res_tac store_assign_SOME_Varray>>
    gvs[simple_val_rel_rewrites])>>
  gvs[simple_val_rel_rewrites,sub_exn_v_def,div_exn_v_def,chr_exn_v_def,
      nat_to_v_def,LIST_REL_EL_EQN,EL_MAP,EL_REPLICATE]
QED
