(*
  Various basic properties of the semantic primitives.
*)

open preamble;
open libTheory astTheory namespaceTheory semanticPrimitivesTheory;
open terminationTheory;
open namespacePropsTheory;
open boolSimps;

val _ = new_theory "semanticPrimitivesProps";

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

 (*
Theorem Tword_simp[simp]:
   (∀z1 z2. (Tword z1 = Tword z2) ⇔ (z1 = z2)) ∧
   (∀z1 z2. (TC_word z1 = TC_word z2) ⇔ (z1 = z2)) ∧
   (∀z. TC_word z ≠ TC_string) ∧
   (∀z. TC_word z ≠ TC_tup) ∧
   (∀z. TC_word z ≠ TC_word8array) ∧
   (∀z. (TC_word z = TC_word8) ⇔ (z = W8)) ∧
   (∀z. (TC_word z = TC_word64) ⇔ (z = W64)) ∧
   (∀z. (TC_word8 = TC_word z) ⇔ (z = W8)) ∧
   (∀z. (TC_word64 = TC_word z) ⇔ (z = W64)) ∧
   (Tword8 ≠ Tword64) ∧
   (∀z. Tword z ≠ Tchar) ∧
   (∀z. Tword z ≠ Tint) ∧
   (∀z v. Tword z ≠ Tvar v) ∧
   (∀z v. Tword z ≠ Tvar_db v) ∧
   (∀z. (Tword8 = Tword z) ⇔ (z = W8)) ∧
   (∀z. (Tword64 = Tword z) ⇔ (z = W64)) ∧
   (∀z. (Tword z = Tword8) ⇔ (z = W8)) ∧
   (∀z. (Tword z = Tword64) ⇔ (z = W64)) ∧
   (∀n a. (Tword W8 = Tapp a n) ⇔ (a = [] ∧ n = TC_word8)) ∧
   (∀n a. (Tword W64 = Tapp a n) ⇔ (a = [] ∧ n = TC_word64)) ∧
   (∀z a n. (Tword z = Tapp a n) ⇔ (a = [] ∧ n = TC_word z)) ∧
   (∀n a. (Tword8 = Tapp a n) ⇔ (a = [] ∧ n = TC_word8)) ∧
   (∀n a. (Tword64 = Tapp a n) ⇔ (a = [] ∧ n = TC_word64))
Proof
  rpt conj_tac \\ rpt Cases \\ EVAL_TAC \\ metis_tac[]
QED
  *)

val opw_lookup_def = Define`
  (opw_lookup Andw = word_and) ∧
  (opw_lookup Orw = word_or) ∧
  (opw_lookup Xor = word_xor) ∧
  (opw_lookup Add = word_add) ∧
  (opw_lookup Sub = word_sub)`;
val _ = export_rewrites["opw_lookup_def"];

val shift_lookup_def = Define`
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)`;
val _ = export_rewrites["shift_lookup_def"];

val do_word_op_def = Define`
  (do_word_op op W8 (Word8 w1) (Word8 w2) = SOME (Word8 (opw_lookup op w1 w2))) ∧
  (do_word_op op W64 (Word64 w1) (Word64 w2) = SOME (Word64 (opw_lookup op w1 w2))) ∧
  (do_word_op op _ _ _ = NONE)`;
val _ = export_rewrites["do_word_op_def"];

val do_shift_def = Define`
  (do_shift sh n W8 (Word8 w) = SOME (Word8 (shift_lookup sh w n))) ∧
  (do_shift sh n W64 (Word64 w) = SOME (Word64 (shift_lookup sh w n))) ∧
  (do_shift _ _ _ _ = NONE)`;
val _ = export_rewrites["do_shift_def"];

val do_word_to_int_def = Define`
  (do_word_to_int W8 (Word8 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int W64 (Word64 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int _ _ = NONE)`;
val _ = export_rewrites["do_word_to_int_def"];

val do_word_from_int_def = Define`
  (do_word_from_int W8 i = Word8 (i2w i)) ∧
  (do_word_from_int W64 i = Word64 (i2w i))`;
val _ = export_rewrites["do_word_from_int_def"];

Theorem lit_same_type_refl:
   ∀l. lit_same_type l l
Proof
  Cases >> simp[semanticPrimitivesTheory.lit_same_type_def]
QED
val _ = export_rewrites["lit_same_type_refl"]

Theorem lit_same_type_sym:
   ∀l1 l2. lit_same_type l1 l2 ⇒ lit_same_type l2 l1
Proof
  Cases >> Cases >> simp[semanticPrimitivesTheory.lit_same_type_def]
QED

Theorem pat_bindings_accum:
 (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)
Proof
 Induct >>
 srw_tac[][]
 >- srw_tac[][pat_bindings_def]
 >- srw_tac[][pat_bindings_def]
 >- srw_tac[][pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- srw_tac[][pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
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
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
 (!cenv s ps vs env env' env''.
  pmatch_list cenv s ps vs env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])
Proof
 ho_match_mp_tac pmatch_ind >>
 srw_tac[][pat_bindings_def, pmatch_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 res_tac >> rveq >>
 srw_tac[][] >>
 metis_tac [pat_bindings_accum]
QED

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
 >> CASE_TAC
 >> rw []
 >> CASE_TAC
 >> rw []
 >> metis_tac [match_result_distinct, match_result_11]
QED

val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def}
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def}
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def}
val v_thms = { nchotomy = v_nchotomy, case_def = v_case_def}
val store_v_thms = { nchotomy = store_v_nchotomy, case_def = store_v_case_def}
val lit_thms = { nchotomy = lit_nchotomy, case_def = lit_case_def}
val eq_v_thms = { nchotomy = eq_result_nchotomy, case_def = eq_result_case_def}
val wz_thms = { nchotomy = word_size_nchotomy, case_def = word_size_case_def}
val eqs = LIST_CONJ (map prove_case_eq_thm
  [op_thms, list_thms, option_thms, v_thms, store_v_thms, lit_thms, eq_v_thms, wz_thms])

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 srw_tac[][]);

val do_app_cases = save_thm ("do_app_cases",
``do_app (s,t) op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

(*
Theorem do_app_cases:
 !st op st' vs v.
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
    (st = st') ∧ (v = Rval (Boolv (opb_lookup op' n1 n2)))) ∨
  ((op = Equality) ∧ (st = st') ∧
    ((?v1 v2.
      (vs = [v1;v2]) ∧
      ((?b. (do_eq v1 v2 = Eq_val b) ∧ (v = Rval (Boolv b))) ∨
       ((do_eq v1 v2 = Eq_closure) ∧ (v = Rerr (Rraise (prim_exn "Eq")))))))) ∨
  (?lnum v2.
    (op = Opassign) ∧ (vs = [Loc lnum; v2]) ∧ (store_assign lnum (Refv v2) st = SOME st') ∧
     (v = Rval (Conv NONE []))) ∨
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
      v = Rval (Conv NONE [])))) ∨
  (?n.
    (op = Chr) ∧ (vs = [Litv(IntLit n)]) ∧ st = st' ∧
    ((n < 0 ∧ v = Rerr (Rraise (prim_exn "Chr"))) ∨
     (n > 255 ∧ v = Rerr (Rraise (prim_exn "Chr"))) ∨
     (~(n < 0) ∧ ~(n > 255) ∧ v = Rval (Litv(Char(CHR(Num(ABS n)))))))) ∨
  (?c.
    (op = Ord) ∧ (vs = [Litv(Char c)]) ∧ st = st' ∧
    (v = Rval(Litv(IntLit(&(ORD c)))))) ∨
  (?opb c1 c2.
    (op = Chopb opb) ∧ (vs = [Litv(Char c1);Litv(Char c2)]) ∧
    (st = st') ∧ (v = Rval(Boolv(opb_lookup opb (&(ORD c1)) (&(ORD c2)))))) ∨
  (?str.
    (op = Explode) ∧ (vs = [Litv(StrLit str)]) ∧
    st = st' ∧
    v = Rval (char_list_to_v (EXPLODE str))) ∨
  (?vs' v'.
    (op = Implode) ∧ (vs = [v']) ∧ (SOME vs' = v_to_char_list v') ∧
    st = st' ∧
    v = Rval (Litv (StrLit (IMPLODE vs')))) ∨
  (?str.
    (op = Strlen) ∧ (vs = [Litv(StrLit str)]) ∧
    st = st' ∧
    v = Rval (Litv(IntLit(&(STRLEN str))))) ∨
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
      v = Rval (Conv NONE [])))))
Proof
 SIMP_TAC (srw_ss()) [do_app_def] >>
 cases_on `op` >>
 srw_tac[][] >>
 cases_on `vs` >>
 srw_tac[][] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 TRY (eq_tac >> srw_tac[][] >> NO_TAC) >>
 TRY (cases_on `do_eq v1 v2`) >>
 srw_tac[][] >>
 UNABBREV_ALL_TAC >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 every_case_tac >>
 srw_tac[][] >>
 metis_tac []
QED
 *)

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
    (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ∧
    (env' = env'' with <| v :=  nsBind n'' v2 (build_rec_env funs env'' env''.v) |> ∧ (v = e))))
Proof
  srw_tac[][do_opapp_def] >>
  cases_on `vs` >> srw_tac[][] >>
  every_case_tac >> metis_tac []
QED

Theorem do_app_NONE_ffi:
   do_app (refs,ffi) op args = NONE ⇒
   do_app (refs,ffi') op args = NONE
Proof
  rw[do_app_def]
  \\ every_case_tac \\ fs[]
  \\ TRY pairarg_tac \\ fs[]
  \\ fs[store_assign_def,store_v_same_type_def]
  \\ every_case_tac \\ fs[]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
QED

Theorem do_app_SOME_ffi_same:
   do_app (refs,ffi) op args = SOME ((refs',ffi),r)
   ∧ (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome))) ⇒
   do_app (refs,ffi') op args = SOME ((refs',ffi'),r)
Proof
  rw[]
  \\ fs[do_app_cases]
  \\ rw[] \\ fs[]
  \\ fs[ffiTheory.call_FFI_def]
  \\ every_case_tac \\ fs[]
  \\ rveq \\ fs[ffiTheory.ffi_state_component_equality]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
QED

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
    FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env funs' f) env') env' funs =
    nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs' f)) funs)) env'`,
 Induct >>
 srw_tac[][] >>
 PairCases_on `h` >>
 srw_tac[][]);

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

(*
Theorem same_ctor_and_same_tid:
 !cn1 tn1 cn2 tn2.
  same_tid tn1 tn2 ∧
  same_ctor (cn1,tn1) (cn2,tn2)
  ⇒
  tn1 = tn2 ∧ cn1 = cn2
Proof
 cases_on `tn1` >>
 cases_on `tn2` >>
 full_simp_tac(srw_ss())[same_tid_def, same_ctor_def]
QED

Theorem same_tid_refl[simp]:
   same_tid t t
Proof
  Cases_on`t`>>EVAL_TAC
QED

Theorem same_tid_sym:
 !tn1 tn2. same_tid tn1 tn2 = same_tid tn2 tn1
Proof
 cases_on `tn1` >>
 cases_on `tn2` >>
 srw_tac[][same_tid_def] >>
 metis_tac []
QED

Theorem same_tid_diff_ctor:
   !cn1 cn2 t1 t2.
    same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
    ⇒
    (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)
Proof
  srw_tac[][] >>
  cases_on `t1` >>
  cases_on `t2` >>
  full_simp_tac(srw_ss())[same_tid_def, same_ctor_def]
QED

Theorem same_tid_tid:
   (same_tid (TypeId x) y ⇔ (y = TypeId x)) ∧
   (same_tid y (TypeId x) ⇔ (y = TypeId x))
Proof
  Cases_on`y`>>EVAL_TAC>>srw_tac[][EQ_IMP_THM]
QED

Theorem build_tdefs_cons:
 (!tvs tn ctors tds mn.
  build_tdefs mn ((tvs,tn,ctors)::tds) =
    nsAppend (build_tdefs mn tds)
           (alist_to_ns (REVERSE (MAP (\(conN,ts). (conN, LENGTH ts, TypeId (mk_id mn tn))) ctors)))) ∧
 (!mn. build_tdefs mn [] = nsEmpty)
Proof
 srw_tac[][build_tdefs_def, REVERSE_APPEND]
QED
*)

 (*
Theorem MAP_FST_build_tdefs:
   set (MAP FST (build_tdefs mn ls)) =
    set (MAP FST (FLAT (MAP (SND o SND) ls)))
Proof
  Induct_on`ls`>>simp[build_tdefs_cons] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[build_tdefs_cons,MAP_REVERSE] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  metis_tac[UNION_COMM]
QED
  *)

  (*
Theorem check_dup_ctors_cons:
 !tvs ts ctors tds.
  check_dup_ctors ((tvs,ts,ctors)::tds)
  ⇒
  check_dup_ctors tds
Proof
induct_on `tds` >>
srw_tac[][check_dup_ctors_def, LET_THM, RES_FORALL] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]
QED
*)

val map_error_result_def = Define`
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)`
val _ = export_rewrites["map_error_result_def"]

Theorem map_error_result_Rtype_error:
   map_error_result f e = (Rabort a) ⇔ e = Rabort a
Proof
  Cases_on`e`>>simp[]
QED
val _ = export_rewrites["map_error_result_Rtype_error"]

Theorem map_error_result_I[simp]:
   map_error_result I e = e
Proof
  Cases_on`e`>>EVAL_TAC
QED

val map_result_def = Define`
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`
val _ = export_rewrites["map_result_def"]

Theorem map_result_Rval[simp]:
   map_result f1 f2 e = Rval x ⇔ ∃y. e = Rval y ∧ x = f1 y
Proof
  Cases_on`e`>>simp[EQ_IMP_THM]
QED

Theorem map_result_Rerr:
   map_result f1 f2 e = Rerr e' ⇔ ∃a. e = Rerr a ∧ map_error_result f2 a = e'
Proof
  Cases_on`e`>>simp[EQ_IMP_THM]
QED
val _ = export_rewrites["map_result_Rerr"]

val exc_rel_def = Define`
  (exc_rel R (Rraise v1) (Rraise v2) = R v1 v2) ∧
  (exc_rel _ (Rabort a1) (Rabort a2) ⇔ a1 = a2) ∧
  (exc_rel _ _ _ = F)`
val _ = export_rewrites["exc_rel_def"]

Theorem exc_rel_raise1:
   exc_rel R (Rraise v) e = ∃v'. (e = Rraise v') ∧ R v v'
Proof
  Cases_on`e`>>srw_tac[][]
QED
Theorem exc_rel_raise2:
   exc_rel R e (Rraise v) = ∃v'. (e = Rraise v') ∧ R v' v
Proof
  Cases_on`e`>>srw_tac[][]
QED
Theorem exc_rel_type_error1:
   (exc_rel R (Rabort a) e = (e = Rabort a))
Proof
  Cases_on`e`>>srw_tac[][]>>metis_tac []
QED
Theorem exc_rel_type_error2:
   (exc_rel R e (Rabort a) = (e = Rabort a))
Proof
  Cases_on`e`>>srw_tac[][]>>metis_tac []
QED
val _ = export_rewrites["exc_rel_raise1","exc_rel_raise2","exc_rel_type_error1","exc_rel_type_error2"]

Theorem exc_rel_refl:
   (∀x. R x x) ⇒ ∀x. exc_rel R x x
Proof
strip_tac >> Cases >> srw_tac[][]
QED
val _ = export_rewrites["exc_rel_refl"];

Theorem exc_rel_trans:
 (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. exc_rel R x y ∧ exc_rel R y z ⇒ exc_rel R x z)
Proof
srw_tac[][] >>
Cases_on `x` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> PROVE_TAC[]
QED

val result_rel_def = Define`
(result_rel R1 _ (Rval v1) (Rval v2) = R1 v1 v2) ∧
(result_rel _ R2 (Rerr e1) (Rerr e2) = exc_rel R2 e1 e2) ∧
(result_rel _ _ _ _ = F)`
val _ = export_rewrites["result_rel_def"]

Theorem result_rel_Rval:
 result_rel R1 R2 (Rval v) r = ∃v'. (r = Rval v') ∧ R1 v v'
Proof
Cases_on `r` >> srw_tac[][]
QED
Theorem result_rel_Rerr1:
 result_rel R1 R2 (Rerr e) r = ∃e'. (r = Rerr e') ∧ exc_rel R2 e e'
Proof
Cases_on `r` >> srw_tac[][EQ_IMP_THM]
QED
Theorem result_rel_Rerr2:
 result_rel R1 R2 r (Rerr e) = ∃e'. (r = Rerr e') ∧ exc_rel R2 e' e
Proof
Cases_on `r` >> srw_tac[][EQ_IMP_THM]
QED
val _ = export_rewrites["result_rel_Rval","result_rel_Rerr1","result_rel_Rerr2"]

Theorem result_rel_refl:
 (∀x. R1 x x) ∧ (∀x. R2 x x) ⇒ ∀x. result_rel R1 R2 x x
Proof
strip_tac >> Cases >> srw_tac[][]
QED
val _ = export_rewrites["result_rel_refl"]

Theorem result_rel_trans:
 (∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀x y z. R2 x y ∧ R2 y z ⇒ R2 x z) ⇒ (∀x y z. result_rel R1 R2 x y ∧ result_rel R1 R2 y z ⇒ result_rel R1 R2 x z)
Proof
srw_tac[][] >>
Cases_on `x` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> PROVE_TAC[exc_rel_trans]
QED

val every_error_result_def = Define`
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)`;
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

Theorem sv_rel_refl:
   ∀R x. (∀x. R x x) ⇒ sv_rel R x x
Proof
  gen_tac >> Cases >> srw_tac[][sv_rel_def] >>
  induct_on `l` >>
  srw_tac[][]
QED
val _ = export_rewrites["sv_rel_refl"]

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
    (?vs1 vs2. x = Varray vs1 ∧ y = Varray vs2 ∧ LIST_REL R vs1 vs2)
Proof
  Cases >> Cases >> simp[sv_rel_def,EQ_IMP_THM]
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

val store_v_vs_def = Define`
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = []`
val _ = export_rewrites["store_v_vs_def"]

val store_vs_def = Define`
  store_vs s = FLAT (MAP store_v_vs s)`

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

val map_match_def = Define`
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)`
val _ = export_rewrites["map_match_def"]

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
    ALL_DISTINCT (MAP (\(f,x,e). f) funs) ∧
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

val ctors_of_tdef_def = Define`
  ctors_of_tdef (_,_,condefs) = MAP FST condefs`
val _ = export_rewrites["ctors_of_tdef_def"]

val ctors_of_dec_def = Define`
  ctors_of_dec (Dtype locs tds) = FLAT (MAP ctors_of_tdef tds) ∧
  ctors_of_dec (Dexn locs s _) = [s] ∧
  ctors_of_dec _ = []`
val _ = export_rewrites["ctors_of_dec_def"]

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
  (FV (Tannot e t) = FV e) ∧
  (FV (Lannot e l) = FV e) ∧
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
     | INR (INR (INR (defs))) => exp1_size defs)`);
val _ = export_rewrites["FV_def"]

val _ = Parse.overload_on("SFV",``λe. {x | Short x ∈ FV e}``)

Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes))
Proof
  Induct_on`pes`>>simp[]>>
  qx_gen_tac`p`>>PairCases_on`p`>>srw_tac[][]
QED

Theorem FV_defs_MAP:
   ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))
Proof
  Induct_on`ls`>>simp[FORALL_PROD]
QED

val FV_dec_def = Define`
  (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
  (FV_dec (Dtype _ _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
  (FV_dec (Dexn _ _ _) = {})`
val _ = export_rewrites["FV_dec_def"]

(*
val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _ _) = []) ∧
  (new_dec_vs (Dtabbrev _ _ _ _) = []) ∧
  (new_dec_vs (Dexn _ _ _) = []) ∧
  (new_dec_vs (Dlet _ p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec _ funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"];

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"];

val new_top_vs_def = Define`
  new_top_vs (Tdec d) = MAP Short (new_dec_vs d) ∧
  new_top_vs (Tmod mn _ ds) = MAP (Long mn o Short) (new_decs_vs ds)`
val _ = export_rewrites["new_top_vs_def"];

val FV_prog_def = Define`
  (FV_prog [] = {}) ∧
  (FV_prog (t::ts) = FV_top t ∪ ((FV_prog ts) DIFF (set (new_top_vs t))))`

val all_env_dom_def = Define`
  all_env_dom (envM,envC,envE) =
    IMAGE Short (set (MAP FST envE)) ∪
    { Long m x | ∃e. ALOOKUP envM m = SOME e ∧ MEM x (MAP FST e) }`;
    *)

val _ = export_theory ();
