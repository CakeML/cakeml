(*
  Properties of the operational semantics.
*)

open preamble evaluateTheory
     namespaceTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     fpSemPropsTheory;
open terminationTheory

val _ = new_theory"evaluateProps";

Theorem call_FFI_LENGTH:
   (call_FFI st index conf x = FFI_return new_st new_bytes) ==>
    (LENGTH x = LENGTH new_bytes)
Proof
  fs[ffiTheory.call_FFI_def] \\ every_case_tac \\ rw[] \\ fs[LENGTH_MAP]
QED

val call_FFI_rel_def = Define `
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t`;

Theorem call_FFI_rel_consts:
   call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)
Proof
  rw[call_FFI_rel_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ fs[CaseEq"bool",CaseEq"oracle_result"]
  \\ rw[]
QED

Theorem RTC_call_FFI_rel_consts:
   ∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)
Proof
  once_rewrite_tac[EQ_SYM_EQ]
  \\ match_mp_tac RTC_lifts_equalities
  \\ rw[call_FFI_rel_consts]
QED

val dest_IO_event_def = Define`
  dest_IO_event (IO_event s c b) = (s,c,b)`;
val _ = export_rewrites["dest_IO_event_def"];

val io_events_mono_def = Define`
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)`;

Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi
Proof
  rw[io_events_mono_def]
QED

Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3
Proof
  rw[io_events_mono_def]
  \\ metis_tac[IS_PREFIX_TRANS, IS_PREFIX_ANTISYM]
QED

Theorem io_events_mono_antisym:
   io_events_mono s1 s2 ∧ io_events_mono s2 s1 ⇒ s1 = s2
Proof
  rw[io_events_mono_def]
  \\ imp_res_tac IS_PREFIX_ANTISYM
  \\ rfs[]
QED

Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
Proof
  REWRITE_TAC[io_events_mono_def] \\
  ho_match_mp_tac RTC_INDUCT
  \\ simp[call_FFI_rel_def,ffiTheory.call_FFI_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[IS_PREFIX_APPEND]
QED

Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
Proof
  srw_tac[][do_app_cases] >> rw[] >>
  FULL_CASE_TAC >>
  fs[option_case_eq] >>
  rpt (FULL_CASE_TAC \\ fs[]) >>
  match_mp_tac RTC_SUBSET >> rw[call_FFI_rel_def] >> fs[] >> every_case_tac
  >> fs[] >> metis_tac[]
QED

Theorem evaluate_call_FFI_rel:
   (∀(s:'ffi state) e f exp.
      RTC call_FFI_rel s.ffi (FST (evaluate s e f exp)).ffi) ∧
   (∀(s:'ffi state) e f v pes errv.
  RTC call_FFI_rel s.ffi (FST (evaluate_match s e f v pes errv)).ffi)
Proof
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  fs[shift_fp_opts_def, astTheory.isFpBool_def] >>
  TRY (
    rename1`isFpOp (FP_sc Opt)` >> fs[] >>
    imp_res_tac do_app_call_FFI_rel >>
    metis_tac[RTC_TRANSITIVE, transitive_def]) >>
  TRY (
    rename1`op ≠ Opapp` >> fs[] >>
    imp_res_tac do_app_call_FFI_rel >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  TRY (
    rename1`op = Opapp` >>
    rev_full_simp_tac(srw_ss())[dec_clock_def] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def,FST]
QED

Theorem evaluate_call_FFI_rel_imp:
   (∀s e f p s' r.
      evaluate s e f p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e f v pes errv s' r.
      evaluate_match s e f v pes errv = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi)
Proof
  metis_tac[PAIR,FST,evaluate_call_FFI_rel]
QED

val evaluate_decs_call_FFI_rel = Q.prove(
  `∀s e f d.
     RTC call_FFI_rel s.ffi (FST (evaluate_decs s e f d)).ffi`,
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,evaluate_call_FFI_rel,FST]);

Theorem evaluate_decs_call_FFI_rel_imp:
   ∀s e f p s' r.
     evaluate_decs s e f p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi
Proof
  metis_tac[PAIR,FST,evaluate_decs_call_FFI_rel]
QED

  (*
val evaluate_tops_call_FFI_rel = Q.prove(
  `∀s e p.
     RTC call_FFI_rel s.ffi (FST (evaluate_tops s e p)).ffi`,
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,evaluate_decs_call_FFI_rel,FST])

Theorem evaluate_tops_call_FFI_rel_imp:
   ∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi
Proof
  metis_tac[PAIR,FST,evaluate_tops_call_FFI_rel]
QED
  *)

Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
Proof
  metis_tac[do_app_call_FFI_rel,call_FFI_rel_io_events_mono]
QED

Theorem evaluate_io_events_mono:
   (∀(s:'ffi state) e f exp.
      io_events_mono s.ffi (FST (evaluate s e f exp)).ffi) ∧
   (∀(s:'ffi state) e f v pes errv.
      io_events_mono s.ffi (FST (evaluate_match s e f v pes errv)).ffi)
Proof
  metis_tac[evaluate_call_FFI_rel,call_FFI_rel_io_events_mono]
QED

Theorem evaluate_io_events_mono_imp:
   (∀s e f p s' r.
      evaluate s e f p = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e f v pes errv s' r.
      evaluate_match s e f v pes errv = (s',r) ⇒
      io_events_mono s.ffi s'.ffi)
Proof
  metis_tac[PAIR,FST,evaluate_io_events_mono]
QED

val evaluate_decs_io_events_mono = Q.prove(
  `∀s e f d.
     io_events_mono s.ffi (FST (evaluate_decs s e f d)).ffi`,
  metis_tac[evaluate_decs_call_FFI_rel,call_FFI_rel_io_events_mono]);

Theorem evaluate_decs_io_events_mono_imp:
   ∀s e f p s' r.
     evaluate_decs s e f p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi
Proof
  metis_tac[PAIR,FST,evaluate_decs_io_events_mono]
QED

  (*
val evaluate_tops_io_events_mono = Q.prove(
  `∀s e p.
     io_events_mono s.ffi (FST (evaluate_tops s e p)).ffi`,
  metis_tac[evaluate_tops_call_FFI_rel,call_FFI_rel_io_events_mono])

Theorem evaluate_tops_io_events_mono_imp:
   ∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi
Proof
  metis_tac[PAIR,FST,evaluate_tops_io_events_mono]
QED
  *)

val is_clock_io_mono_def = Define
  `is_clock_io_mono f s = (case f s of (s', fp, r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ (!clk. case f (s with clock := clk) of (s'', fp', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r /\ fp = fp'
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))`;

Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s, fp, Rval r)) s
Proof
  fs [is_clock_io_mono_def]
QED

(*
Theorem is_clock_io_mono_ret_fpOpt:
  is_clock_io_mono (\s. (s with fp_canOpt := F, Rval v)) s
Proof
  fs [is_clock_io_mono_def]
QED
*)

Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s, fp, Rerr r)) s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
Proof
  Cases_on `x` \\ fs []
QED

Theorem is_clock_io_mono_bind:
   is_clock_io_mono f s /\ (!s' fp r. f s = (s', fp, r)
        ==> is_clock_io_mono (g fp r) s')
    /\ (!fp s'. g fp (Rerr (Rabort Rtimeout_error)) s'
        = (s', fp, Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', fp, r) => g fp r s') s
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC, CASE_TAC])
  \\ fs []
  \\ Cases_on `SND (f s)` \\ rfs[] \\ rveq \\ fs[]
  \\ conj_tac \\ (TRY (irule io_events_mono_trans \\ metis_tac []))
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC, CASE_TAC])
  \\ fs [pair_CASE_eq_forall]
  \\ FIRST_X_ASSUM drule
  \\ rpt DISCH_TAC
  \\ fs []
  (* many cases *)
  \\ Cases_on (`SND (SND (f s)) = Rerr (Rabort Rtimeout_error)`)
  \\ Cases_on (`SND (SND (f (s with clock := clk))) = Rerr (Rabort Rtimeout_error)`)
  \\ rpt (FIRST (map CHANGED_TAC [DISCH_TAC, fs [], rfs [], rveq]))
  \\ TRY (irule io_events_mono_trans \\ metis_tac [])
  (* back to one case *)
  \\ FIRST_X_ASSUM drule
  \\ rpt (FIRST (map CHANGED_TAC [DISCH_TAC, fs [], rfs [], rveq,
        fs [EQ_IMP_THM]]))
QED

Theorem is_clock_io_mono_check:
   (~ (s.clock = 0) ==> is_clock_io_mono f (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s, fp, Rerr (Rabort Rtimeout_error)) else f (dec_clock s)) s
Proof
  fs [is_clock_io_mono_def, dec_clock_def]
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ fs [pair_CASE_eq_forall]
  \\ FIRST_X_ASSUM drule
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ Cases_on `r'' = Rerr (Rabort Rtimeout_error)` \\ fs []
QED

Theorem is_clock_io_mono_refs_lemma:
   is_clock_io_mono (\s'. f (s.refs) s') s
    ==> is_clock_io_mono (\s'. f (s'.refs) s') s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_do_app:
  ! xs (st:'ffi state) fp.
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', fp, Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      if (isFpOp op) then
        (let
           (fp_opt, fpsR) =
             if (fp.canOpt)
             then
               ((case do_fprw r (fp.opts 0) fp.rws of
               NONE => r
               | SOME r_opt => r_opt), shift_fp_opts fp)
             else (r, fp);
           fp_res =
             if isFpBool op then
               case fp_opt of
               Rval (FP_BoolTree fv) =>
                   Rval (Boolv (compress_bool fv))
               | _ => (Rerr (Rabort Rtype_error))
             else fp_opt
         in
           (st' with <|refs := refs; ffi := ffi|>,
            fpsR,
            list_result fp_res))
      else (st' with<| refs := refs; ffi := ffi |>, fp, list_result r)) st
Proof
  fs [is_clock_io_mono_def, shift_fp_opts_def]
  \\ rpt (CASE_TAC ORELSE CHANGED_TAC (fs []) ORELSE CHANGED_TAC rveq ORELSE gen_tac)
  \\ metis_tac [do_app_io_events_mono]
QED

Theorem is_clock_io_mono_fp_optimise:
  ! (s:'ffi state) env fp es.
    is_clock_io_mono (\ s. evaluate s env (fp with canOpt := T) [e]) s ==>
    is_clock_io_mono (\ s. evaluate s env fp [FpOptimise sc e]) s
Proof
  Cases_on `sc` \\ fs[is_clock_io_mono_def, evaluate_def]
  \\ rpt gen_tac
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ rename [`evaluate s env _ [e] = (s1, fp1, r1)`]
  \\ Cases_on `r1` \\ fs[] \\ rveq \\ fs[]
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then `clk` assume_tac)
  \\ pop_assum mp_tac \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ rename [`evaluate (s with clock := clk) _ _ _ = (s2, fp2, r2)`]
  \\ Cases_on `r2` \\ fs[]
QED

Theorem is_clock_io_mono_evaluate:
   (!(s : 'ffi state) env fp es. is_clock_io_mono (\s. evaluate s env fp es) s) /\
   (!(s : 'ffi state) env fp v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env fp v pes err_v) s)
Proof
  ho_match_mp_tac evaluate_ind
  \\ rpt strip_tac \\ fs [evaluate_def]
  \\ TRY (rpt (FIRST ([strip_tac] @ map ho_match_mp_tac [is_clock_io_mono_bind,
        is_clock_io_mono_check]
    @ [CHANGED_TAC (fs [is_clock_io_mono_return, is_clock_io_mono_err,
            is_clock_io_mono_do_app]),
        CASE_TAC,
        CHANGED_TAC (ho_match_mp_tac is_clock_io_mono_refs_lemma)])) \\ NO_TAC)
  \\ TRY (
    drule (SIMP_RULE std_ss [evaluate_def] is_clock_io_mono_fp_optimise) \\fs[])
  \\ ho_match_mp_tac is_clock_io_mono_bind \\ fs[]
  \\ rpt strip_tac
  \\ TRY (fs[is_clock_io_mono_def] \\ NO_TAC)
  \\ ntac 2 (TOP_CASE_TAC
      \\ fs [is_clock_io_mono_return, is_clock_io_mono_err])
  >- (TOP_CASE_TAC \\ fs[astTheory.isFpBool_def]
      \\rpt (FIRST [CHANGED_TAC (fs[is_clock_io_mono_return, is_clock_io_mono_err,
            is_clock_io_mono_do_app]), CASE_TAC])
      \\ ho_match_mp_tac is_clock_io_mono_check \\ fs[])
  \\ assume_tac is_clock_io_mono_do_app \\ fs[]
QED

Theorem is_clock_io_mono_extra:
   (!s. is_clock_io_mono f s)
    ==> f s = (s', fp, r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra, fp, r)
Proof
  DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ ntac 2 CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ rpt DISCH_TAC
  \\ rpt (CHANGED_TAC (fs [semanticPrimitivesPropsTheory.with_same_clock]))
QED

Theorem is_clock_io_mono_extra_mono:
   (!s. is_clock_io_mono f s)
    ==> io_events_mono (FST(f s)).ffi
     (FST(f (s with clock := s.clock + extra))).ffi
Proof
  DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ ntac 2 CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ ntac 2 CASE_TAC
QED

fun mk_extra_lemmas mp_rule monad_rule
  = BODY_CONJUNCTS monad_rule
    |> map (BETA_RULE o MATCH_MP mp_rule o Q.GEN `s`)
fun prove_extra mp_rule monad_rule
  = simp_tac bool_ss (mk_extra_lemmas mp_rule monad_rule)

Theorem evaluate_add_to_clock:
   !(s:'ffi state) env fp es s' fp' r extra.
    evaluate s env fp es = (s', fp', r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (s with clock := s.clock + extra) env fp es =
    (s' with clock := s'.clock + extra, fp', r)
Proof
  prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate
QED

Theorem evaluate_match_add_to_clock:
   !(s:'ffi state) env fp v pes err_v s' fp' r extra.
    evaluate_match s env fp v pes err_v = (s', fp', r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate_match (s with clock := s.clock + extra) env fp v pes err_v =
      (s' with clock := s'.clock + extra, fp', r)
Proof
  prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate
QED

Theorem list_result_eq_Rval[simp]:
   list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
Proof
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM]
QED

Theorem list_result_eq_Rerr[simp]:
   list_result r = Rerr e ⇔ r = Rerr e
Proof
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM]
QED

Theorem result_rel_list_result[simp]:
   result_rel (LIST_REL R) Q (list_result r1) (list_result r2) ⇔
   result_rel R Q r1 r2
Proof
  Cases_on`r1`>>srw_tac[][PULL_EXISTS]
QED

Theorem list_result_inj:
   list_result x = list_result y ⇒ x = y
Proof
  Cases_on`x`>>Cases_on`y`>>EVAL_TAC
QED

Theorem evaluate_length:
   (∀(s:'ffi state) e f p s' f' r. evaluate s e f p = (s', f', Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e f v p er s' f' r. evaluate_match s e f v p er = (s', f', Rval r) ⇒ LENGTH r = 1)
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[list_result_eq_Rval] >>
  srw_tac[][] >> fs[]
QED

Theorem evaluate_nil[simp]:
   ∀(s:'ffi state) env f. evaluate s env f [] = (s, f, Rval [])
Proof
 rw [evaluate_def]
QED

Theorem evaluate_sing:
   ∀(s:'ffi state) env f e s' f' vs. evaluate s env f [e] = (s', f', Rval vs) ⇒ ∃v. vs = [v]
Proof
 rw []
 >> imp_res_tac evaluate_length
 >> Cases_on `vs`
 >> fs []
 >> Cases_on `t`
 >> fs []
QED

Theorem evaluate_cons:
  ∀(s:'ffi state) env fp e es.
   evaluate s env fp (e::es) =
     case evaluate s env fp [e] of
     | (s', fp', Rval vs) =>
      (case evaluate s' env fp' es of
       | (s'', fp'', Rval vs') => (s'', fp'', Rval (vs++vs'))
       | err => err)
     | err => err
Proof
 Cases_on `es`
 >> rw [evaluate_def]
 >- every_case_tac
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate _ _ _ _ = (st',fps', r)`
 >> Cases_on `r`
 >> simp []
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate _ _ _ (e'::es) = (st'', fp'', r)`
 >> Cases_on `r`
 >> simp []
 >> drule evaluate_sing
 >> rw [] >> rw[]
QED

Theorem evaluate_decs_nil[simp]:
   ∀(s:'ffi state) env fp.
    evaluate_decs s env fp [] = (s, fp, Rval <| v := nsEmpty; c := nsEmpty |>)
Proof
 rw [evaluate_decs_def]
QED

Theorem evaluate_decs_cons:
  ∀(s:'ffi state) env fp d ds.
   evaluate_decs s env fp (d::ds) =
     case evaluate_decs s env fp [d] of
     | (s1, fp1, Rval env1) =>
      (case evaluate_decs s1 (extend_dec_env env1 env) fp1 ds of
       | (s2, fp2, r) => (s2, fp2, combine_dec_result env1 r)
       | err => err)
     | err => err
Proof
 Cases_on `ds`
 >> rw [evaluate_decs_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_decs _ _ _ _ = (s1,_,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]
QED

 (*
Theorem evaluate_tops_nil[simp]:
   ∀(s:'ffi state) env. evaluate_tops s env [] = (s,Rval <| v := nsEmpty; c := nsEmpty |>)
Proof
 rw [evaluate_tops_def]
QED

Theorem evaluate_tops_cons:
  ∀(s:'ffi state) env top tops.
   evaluate_tops s env (top::tops) =
     case evaluate_tops s env [top] of
     | (s1, Rval env1) =>
      (case evaluate_tops s1 (extend_dec_env env1 env) tops of
       | (s2, r) => (s2, combine_dec_result env1 r)
       | err => err)
     | err => err
Proof
 Cases_on `tops`
 >> rw [evaluate_tops_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_tops _ _ _ = (s1,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]
QED
 *)

Theorem evaluate_match_list_result:
   evaluate_match s e f v p er = (s', f', r) ⇒
   ∃r'. r = list_result r'
Proof
  Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]
QED

Theorem is_clock_io_mono_evaluate_decs:
   !s e f p. is_clock_io_mono (\s. evaluate_decs s e f p) s
Proof
  ho_match_mp_tac evaluate_decs_ind
  \\ fs [evaluate_decs_def, combine_dec_result_def]
  \\ rpt (strip_tac ORELSE TOP_CASE_TAC
    ORELSE (CHANGED_TAC (fs [is_clock_io_mono_return,
        is_clock_io_mono_err, is_clock_io_mono_evaluate]))
    ORELSE ho_match_mp_tac is_clock_io_mono_bind
  )
  \\ fs [is_clock_io_mono_def]
QED

val evaluate_decs_lemmas
  = BODY_CONJUNCTS is_clock_io_mono_evaluate_decs
    |> map (BETA_RULE o MATCH_MP is_clock_io_mono_extra o Q.GEN `s`)

Theorem evaluate_decs_add_to_clock:
   !s e f p s' f' r extra.
   evaluate_decs s e f p = (s', f', r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs (s with clock := s.clock + extra) e f p =
   (s' with clock := s'.clock + extra, f', r)
Proof
  simp_tac bool_ss evaluate_decs_lemmas
QED

    (*
Theorem evaluate_tops_add_to_clock:
  !s e p s' r extra.
   evaluate_tops s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_tops (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)
Proof
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   split_pair_case_tac
   >> fs []
   >> split_pair_case_tac
   >> fs []
   >> every_case_tac
   >> fs []
   >> rpt var_eq_tac
   >> simp []
   >> rfs [combine_dec_result_def]
   >> fs []
   >> Cases_on `r'`
   >> Cases_on `r''`
   >> simp []
   >> rfs []
   >> fs [])
 >- (
   every_case_tac
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_decs_add_to_clock
   >> fs [])
 >- (
   every_case_tac
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_decs_add_to_clock
   >> rfs []
   >> fs []
   >> rw [])
QED
   *)

val add_lemma = Q.prove (
 `!(k:num) k'. ?extra. k = k' + extra ∨ k' = k + extra`,
 intLib.ARITH_TAC);

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC);

Theorem evaluate_decs_clock_determ:
 !s e f p s1 r1 s2 r2 fp1 fp2 k1 k2.
  evaluate_decs (s with clock := k1) e fp p = (s1, fp1, r1) ∧
  evaluate_decs (s with clock := k2) e fp p = (s2, fp2, r2)
  ⇒
  case (r1,r2) of
  | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
    T
  | (Rerr (Rabort Rtimeout_error), _) =>
    k1 < k2
  | (_, Rerr (Rabort Rtimeout_error)) =>
    k2 < k1
  | _ =>
    s1.ffi = s2.ffi ∧ r1 = r2
Proof
 rw []
 >> Cases_on `r2 = Rerr (Rabort Rtimeout_error)`
 >> Cases_on `r1 = Rerr (Rabort Rtimeout_error)`
 >> fs []
 >> fs []
 >> fs []
 >> rw []
 >- (
   `k2 < k1` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> `?extra. k2 = k1 + extra` by intLib.ARITH_TAC
   >> qpat_x_assum `evaluate_decs _ _ _ _ = _` mp_tac
   >> drule evaluate_decs_add_to_clock
   >> rw [])
 >- (
   `k1 < k2` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> `?extra. k1 = k2 + extra` by intLib.ARITH_TAC
   >> drule evaluate_decs_add_to_clock
   >> fs []
   >> qexists_tac `extra`
   >> simp [])
 >- (
   every_case_tac >>
   fs [] >>
   rw [] >>
   `(?extra. k1 = k2 + extra) ∨ (?extra. k2 = k1 + extra)`
   by intLib.ARITH_TAC >>
   rw [] >>
   imp_res_tac evaluate_decs_add_to_clock >>
   fs [] >>
   rw [])
QED

Theorem evaluate_add_to_clock_io_events_mono:
   (∀(s:'ffi state) e f d extra.
     io_events_mono (FST(evaluate s e f d)).ffi
     (FST(evaluate (s with clock := s.clock + extra) e f d)).ffi) ∧
   (∀(s:'ffi state) e f v d er extra.
     io_events_mono (FST(evaluate_match s e f v d er)).ffi
     (FST(evaluate_match (s with clock := s.clock + extra) e f v d er)).ffi)
Proof
  prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate
QED

Theorem evaluate_decs_add_to_clock_io_events_mono:
   ∀s e f d.
    io_events_mono
    (FST(evaluate_decs s e f d)).ffi
    (FST(evaluate_decs (s with clock := s.clock + extra) e f d)).ffi
Proof
  prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate_decs
QED

  (*
Theorem evaluate_tops_add_to_clock_io_events_mono:
   ∀s e p extra.
   io_events_mono (FST(evaluate_tops s e p)).ffi
   (FST(evaluate_tops (s with clock := s.clock + extra) e p)).ffi
Proof
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_tops_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_tops_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[io_events_mono_trans]) >>
  metis_tac[evaluate_decs_add_to_clock_io_events_mono,FST]
QED
  *)

Theorem evaluate_decs_ffi_mono_clock:
   ∀k1 k2 s e f p.
    k1 ≤ k2 ⇒
    io_events_mono
    (FST (evaluate_decs (s with clock := k1) e f p)).ffi
    (FST (evaluate_decs (s with clock := k2) e f p)).ffi
Proof
  metis_tac [is_clock_io_mono_evaluate_decs
    |> Q.SPEC `s with clock := k1`
    |> SIMP_RULE (srw_ss ()) [is_clock_io_mono_def, pair_CASE_def]]
QED

Theorem evaluate_state_unchanged:
  (!(st:'ffi state) env fp es st' r.
    evaluate st env fp es = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp) ∧
  (!(st:'ffi state) env fp v pes err_v st' r.
    evaluate_match st env fp v pes err_v = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp)
Proof
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def, shift_fp_opts_def]
QED

 (*
Theorem evaluate_decs_state_unchanged:
  !mn st env ds st' r.
  evaluate_decs mn st env ds = (st',r)
  ⇒
  st.defined_mods = st'.defined_mods
Proof
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> every_case_tac
 >> fs []
 >> rw []
 >> metis_tac [evaluate_state_unchanged]
QED

 *)

val evaluate_ffi_sandwich = Q.prove(
  `evaluate s env fp exp = (s', fp', r) ∧
   evaluate s''' env' fp'' exp' = (s'', fp''', r') ∧
   s'''.ffi = s'.ffi ∧ s''.ffi = s.ffi
   ⇒ s'.ffi = s.ffi`,
  rw[] \\
  imp_res_tac evaluate_io_events_mono_imp \\ fs[] \\
  metis_tac[io_events_mono_antisym]);

val evaluate_match_ffi_sandwich = Q.prove(
  `evaluate s env fp exp = (s', fp', r) ∧
   evaluate_match s' env' fp' v pes errv  = (s'', fp'', r') ∧
   s''.ffi = s.ffi ⇒ s'.ffi = s.ffi`,
  rw[] \\
  imp_res_tac evaluate_io_events_mono_imp \\ fs[] \\
  metis_tac[io_events_mono_antisym]);

val result_CASE_fst_cong = Q.prove(
  `result_CASE r (λa. (c, fp, f a)) (λb. (c, fp, g b)) =
   (c, fp, result_CASE r (λa. f a) (λb. g b))`,
  Cases_on`r` \\ fs[]);

val option_CASE_fst_cong = Q.prove(
  `option_CASE r (c,fp,f) (λb. (c,fp,g b)) =
   (c, fp, option_CASE r f (λb. g b))`,
  Cases_on`r` \\ fs[]);

val evaluate_state_const = CONJUNCT1 evaluate_state_unchanged;

local
  val trivial = rpt strip_tac \\ rveq \\ fs[fp_state_component_equality];
  val by_eq =
      `fp1.choices = fp2.choices`
        by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ simp[])
      \\ `fp1 = fp2`
        by (drule fpSemPropsTheory.evaluate_fp_stable \\ disch_then drule \\ fs[])
      \\ fs[fp_state_component_equality];
in
Theorem evaluate_fp_intro:
  (! (s:'a state) env fps1 e s' fps1' r.
    evaluate s env fps1 e = (s', fps1', r) /\
    fps1 = fps1' ==>
    ! fp2.
      fp2.canOpt = fps1.canOpt ==>
      evaluate s env fp2 e = (s', fp2, r))
  /\
  (! (s:'a state) env fps1 v pes errv s' fps1' r.
    evaluate_match s env fps1 v pes errv = (s', fps1', r) /\
    fps1 = fps1' ==>
    ! fp2.
      fp2.canOpt = fps1.canOpt ==>
      evaluate_match s env fp2 v pes errv = (s', fp2, r))
Proof
  ho_match_mp_tac evaluate_ind
  \\ rpt strip_tac \\ fs[evaluate_def, fp_state_component_equality]
  \\ qpat_x_assum `_ = (_, _, _)` mp_tac
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq \\ fs[]
      \\ rename [`evaluate s env fp1 [e1] = (s2, fp2, Rval r)`,
                 `evaluate s2 env fp2 _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (ntac 3 (TOP_CASE_TAC \\ fs[]) \\ trivial)
  >- (ntac 3 (TOP_CASE_TAC \\ fs[]) >- trivial
      \\ reverse TOP_CASE_TAC \\ fs[] >- trivial
      \\ strip_tac
      \\ rename [`evaluate s env fp1 [e1] = (s2, fp2, _)`,
                 `evaluate_match s2 env fp2 _ _ _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (ntac 4 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ TOP_CASE_TAC \\ fs[fp_state_component_equality])
  >- (TOP_CASE_TAC \\ fs[fp_state_component_equality])
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ TOP_CASE_TAC \\ fs[]
      >- (TOP_CASE_TAC \\ fs[] >- trivial
          \\ ntac 2 (TOP_CASE_TAC \\ fs[]) >- trivial
          \\ strip_tac
          \\ rename [`evaluate s env fp1 _ = (s2, fp2, _)`,
                     `evaluate (dec_clock s2) _ fp2 _ = (s3, fp3, _)`]
          \\ by_eq)
      \\ TOP_CASE_TAC \\ fs[] >- trivial
      \\ ntac 3 (TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ rveq \\ fs[evaluateTheory.shift_fp_opts_def]
          \\ rename [`evaluate s env fp1 _ = (s2, fp2, _)`]
          \\ Cases_on `fp2.canOpt`
          >- (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[] \\ rveq \\ fs[])
          \\ fs[] \\ rveq
          \\ `fp2 = fp1` by (fs[fp_state_component_equality])
          \\ fs[])
      \\ trivial)
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ TOP_CASE_TAC \\ fs[] >- trivial
      \\ TOP_CASE_TAC \\ fs[]
      \\ TRY (trivial \\ NO_TAC)
      \\ rpt strip_tac
      \\ rename [`evaluate s env fp1 _ = (s2, fp2, _)`,
                 `evaluate s2 _ fp2 _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ TOP_CASE_TAC \\ fs[] >- trivial
      \\ strip_tac
      \\ rename [`evaluate s env fp1 _ = (s2, fp2, _)`,
                 `evaluate s2 _ fp2 _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ strip_tac
      \\ rename [`evaluate s env fp1 [e1] = (s2, fp2, _)`,
                 `evaluate_match s2 env fp2 _ _ _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
      \\ strip_tac
      \\ rename [`evaluate s env fp1 _ = (s2, fp2, _)`,
                 `evaluate s2 _ fp2 _ = (s3, fp3, _)`]
      \\ by_eq)
  >- (TOP_CASE_TAC \\ fs[] \\ trivial)
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq
      \\ imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv
      \\ fs[fp_state_component_equality])
  >- (ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ trivial)
QED
end

Theorem evaluate_ffi_intro:
    (∀(s:'a state) env fp e s' fp' r.
     evaluate s env fp e = (s', fp', r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome))) ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs ⇒
       evaluate t env fp e = (t with <| clock := s'.clock; refs := s'.refs|>, fp', r)) ∧
  (∀(s:'a state) env fp v pes errv s' fp' r.
     evaluate_match s env fp v pes errv = (s', fp', r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome))) ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs ⇒
       evaluate_match t env fp v pes errv = (t with <| clock := s'.clock; refs := s'.refs|>, fp', r))
Proof
  ho_match_mp_tac evaluate_ind
  \\ rw[state_component_equality]
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ ntac 2 TOP_CASE_TAC \\ fs[result_CASE_fst_cong]
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename [`evaluate s _ _ _ = (s1,_,_)`, `evaluate s1 _ _ _ = (s2, _, _)`]
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ res_tac \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_abbrev_tac`evaluate t1 _ _ (_::_) = _`
    \\ rveq
    \\ simp[]
    \\ imp_res_tac evaluate_state_const \\ fs[]
    \\ every_case_tac >> rfs[]
    \\ res_tac
    \\ first_x_assum (qspec_then `t1` mp_tac) \\ rveq \\ fs[])
  >- (
    rfs[evaluate_def] \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[] \\ fs[]
    \\ first_x_assum(qspec_then`t`mp_tac) \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ _ = (s1,_, _)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_match_ffi_sandwich]
    \\ fs[] \\ rfs[]
    (*
    \\ qmatch_goalsub_abbrev_tac`evaluate_match t1`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[]*) )
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- fs[state_component_equality]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC
    \\ fs[option_CASE_fst_cong,result_CASE_fst_cong]
    \\ rw[]
    \\ rfs[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ impl_tac >- (every_case_tac \\ fs[])
    \\ rw[])
  >- (
    rfs[evaluate_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      ntac 3 (TOP_CASE_TAC \\ fs[])
      >- ( strip_tac \\ rveq \\ fs[] )
      \\ strip_tac \\ fs[]
      \\ rename1`evaluate (dec_clock s1) _ _ _ = _`
      \\ `s1.ffi = s.ffi`
      by (
        imp_res_tac evaluate_ffi_sandwich
        \\ rfs[dec_clock_def] )
      \\ fs[]
      \\ rfs[dec_clock_def] \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ imp_res_tac do_app_NONE_ffi
      \\ fs[] )
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- (strip_tac \\ rveq \\ fs[]
        \\ rveq \\ fs[]
        \\ imp_res_tac do_app_io_events_mono
        \\ imp_res_tac evaluate_io_events_mono_imp
        \\ imp_res_tac io_events_mono_antisym \\ fs[]
        \\ imp_res_tac do_app_SOME_ffi_same \\ fs[]
        \\ rw[state_component_equality])
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      rpt strip_tac  \\ rveq \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ reverse TOP_CASE_TAC
      \\ rename [`evaluate s env fp (REVERSE _) = (s2, fp2, Rval _)`]
      \\ Cases_on `fp2.canOpt`
      \\ fs[shift_fp_opts_def, state_component_equality] \\ rveq
      \\ `s2.ffi = s.ffi`
        by (rveq
        \\ imp_res_tac do_app_io_events_mono
        \\ imp_res_tac evaluate_io_events_mono_imp
        \\ imp_res_tac io_events_mono_antisym \\ fs[]
        \\ first_x_assum irule \\ rfs[])
      \\ res_tac \\ fs[]
      \\ rveq \\ fs[]
      \\ imp_res_tac fpOp_determ \\ fs[]
      \\ rveq \\ fs[state_component_equality]
      \\ imp_res_tac evaluate_fp_opts_inv \\ rveq \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ rename [`evaluate s env fp (REVERSE _) = (s2, fp2, Rval _)`]
    \\ Cases_on `fp2.canOpt`
    \\ fs[shift_fp_opts_def, state_component_equality] \\ rveq
    \\ `s2.ffi = s.ffi`
        by (rveq
            \\ imp_res_tac do_app_io_events_mono
            \\ imp_res_tac evaluate_io_events_mono_imp
            \\ imp_res_tac io_events_mono_antisym
            \\ first_x_assum irule \\ rfs[])
    \\ res_tac \\ fs[]
    \\ qpat_x_assum `s'.ffi = _.ffi` (fn thm => fs[GSYM thm])
    \\ imp_res_tac do_app_SOME_ffi_same \\ fs[state_component_equality]
    \\ `! outcome. r' <> Rerr (Rabort (Rffi_error outcome))`
        by (rpt strip_tac \\ rveq \\ fs[do_fprw_def])
    \\ res_tac \\ fs[]
    \\ first_x_assum (qspec_then `t.ffi` assume_tac)
    \\ fs[state_component_equality])
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename1`evaluate s _ _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    (*
    \\ imp_res_tac evaluate_state_const \\ fs[]*) )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename1`evaluate s _ _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    (*
    \\ imp_res_tac evaluate_state_const \\ fs[] *))
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_match_ffi_sandwich]
    \\ fs[] \\ rfs[]
    (*
    \\ imp_res_tac evaluate_state_const \\ fs[]*) )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ ntac 2 TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    (*
    \\ imp_res_tac evaluate_state_const \\ fs[]*) )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum `_ = (_,_,_)` mp_tac
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ rename1 `evaluate s env _ [e] = (s1, _, Rerr e1)`
    \\ `!outcome. e1 <> Rabort (Rffi_error outcome)` by fs[]
    \\ res_tac
    \\ fs[state_component_equality] \\ rveq \\ fs[state_component_equality])
  >- (
    rfs[evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- rw[state_component_equality]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[state_component_equality] )
QED

Theorem is_clock_io_mono_set_clock:
   is_clock_io_mono f s
    ==> f s = (s', fp, r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, fp, r)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `ck1 + (s.clock − (HD [s';s]).clock)`)
  \\ ntac 2 CASE_TAC
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ metis_tac []
QED

val evaluate_set_clock_lemmas
  = (BODY_CONJUNCTS is_clock_io_mono_evaluate
    @ BODY_CONJUNCTS is_clock_io_mono_evaluate_decs)
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock);

Theorem evaluate_set_clock:
   !(s:'ffi state) env fp exps s1 fpr res.
      evaluate s env fp exps = (s1, fpr, res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate (s with clock := ck1) env fp exps =
                   (s1 with clock := ck, fpr, res)
Proof
  metis_tac evaluate_set_clock_lemmas
QED

Theorem evaluate_decs_set_clock:
   !s env fp decs s1 fpr res.
      evaluate_decs s env fp decs = (s1, fpr, res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate_decs (s with clock := ck1) env fp decs =
                   (s1 with clock := ck, fpr, res)
Proof
  metis_tac evaluate_set_clock_lemmas
QED

Theorem is_clock_io_mono_minimal:
   is_clock_io_mono f s
    ==> f s = (s', fp, r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s'' fp'. f (s with clock := k) = (s'', fp', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ ntac 2 CASE_TAC \\ fs []
QED

val evaluate_minimal_lemmas = BODY_CONJUNCTS is_clock_io_mono_evaluate
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_minimal);

Theorem evaluate_minimal_clock:
   (!(s:'ffi state) env fp es s' fp' r k.
    evaluate s env fp es = (s', fp', r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s'' fp''.
      evaluate (s with clock := k) env fp es =
      (s'', fp'', Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)
Proof
  metis_tac evaluate_minimal_lemmas
QED

Theorem evaluate_match_minimal_clock:
   (!(s:'ffi state) env fp v pes err_v s' fp' r k.
    evaluate_match s env fp v pes err_v = (s', fp', r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s'' fp''.
      evaluate_match (s with clock := k) env fp v pes err_v =
      (s'', fp'', Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)
Proof
  metis_tac evaluate_minimal_lemmas
QED

Theorem evaluate_set_init_clock:
   evaluate st env fp xs = (st', fp', res) /\
   res <> Rerr (Rabort Rtimeout_error) ==>
   !k. ?ck res1 st1 fp1.
   evaluate (st with clock := k) env fp xs = (st1, fp1, res1) /\
   (res1 = res /\ st1 = (st' with clock := ck) /\ fp1 = fp' \/
    res1 = Rerr (Rabort Rtimeout_error) /\
    io_events_mono st1.ffi st'.ffi)
Proof
  rw []
  \\ drule evaluate_set_clock
  \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
  \\ Cases_on `ck1 <= k`
  THEN1 (
    fs [LESS_EQ_EXISTS] \\ rveq
    \\ drule evaluate_add_to_clock
    \\ disch_then (qspec_then `p` mp_tac) \\ fs []
    \\ metis_tac [])
  \\ drule evaluate_minimal_clock \\ fs []
  \\ disch_then (qspec_then `k` mp_tac) \\ fs []
  \\ rw [] \\ fs []
QED

Theorem extend_dec_env_empty_id[local,simp]:
  extend_dec_env <| v := nsEmpty; c := nsEmpty |> env = env
Proof
  Cases_on `env` \\ Cases_on `n` \\ Cases_on `n0` \\ EVAL_TAC
  \\ fs[sem_env_11, sem_env_component_equality]
QED

Theorem combine_dec_result_empty_id[local,simp]:
  combine_dec_result <| v := nsEmpty; c := nsEmpty |> env = env
Proof
  Cases_on `env` \\ fs[combine_dec_result_def] \\ Cases_on `a.c` \\ Cases_on `a.v` \\ EVAL_TAC
  \\ fs[sem_env_11, sem_env_component_equality]
QED

Theorem evaluate_decs_fp_preserving:
  ! s1 env fps1 decls1 decls2 s2 fps2 r.
    evaluate_decs s1 env fps1 (decls1 ++ decls2) = (s2, fps2, r) /\
    fps1.choices = fps2.choices ==>
    fps1 = fps2 /\
    ? s3 r2.
      evaluate_decs s1 env fps1 decls1 = (s3, fps1, r2) /\
      (! e. r2 = Rerr e ==> r = r2) /\
      (! env1. r2 = Rval env1 ==>
        ? r3. evaluate_decs s3 (extend_dec_env env1 env) fps1 decls2 = (s2, fps1, r3) /\
          combine_dec_result env1 r3 = r)
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt gen_tac \\ rpt conj_tac
  \\ rpt (FIRST [gen_tac, (disch_then assume_tac)]) \\ fs[]
  >- (imp_res_tac evaluate_decs_fp_stable \\ fs[] \\ rveq
      \\ fs[evaluate_decs_def])
  >- (`d1 :: d2 :: ds ++ decls2 = [d1] ++ ((d2 :: ds) ++ decls2)`
        by (fs[APPEND_EQ_CONS])
      \\ first_x_assum (qspec_then `(d2::ds) ++ decls2` assume_tac)
      \\ fs[]
      \\ qpat_x_assum `evaluate_decs _ _ _ _ = _`
          (fn thm => (first_x_assum (fn ithm => mp_then Any assume_tac ithm thm)) \\ assume_tac thm)
      \\ fs[]
      \\ simp[Once evaluate_decs_cons]
      \\ Cases_on `r2` \\ fs[] \\ rveq \\ fs[]
      \\ pop_assum mp_tac
      \\ simp[Once evaluate_decs_cons]
      \\ first_x_assum (qspec_then `decls2` assume_tac)
      \\ res_tac \\ fs[]
      \\ Cases_on `r2` \\ fs[] \\ rveq \\ rpt conj_tac
      >- (fs[combine_dec_result_def])
      >- (rpt strip_tac \\ fs[extend_dec_env_def, combine_dec_result_def]
          \\ rveq \\ fs[]
          \\ TOP_CASE_TAC \\ fs[])
      \\ fs[combine_dec_result_def])
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ ntac 4 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ rename [`pmatch env.c s2.refs p (HD r) []`]
      \\ Cases_on `pmatch env.c s2.refs p (HD r) []` \\ fs[]
      >- (rpt strip_tac \\ rveq \\ fs[])
      >- (rpt strip_tac \\ rveq \\ fs[])
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[]
      \\ rename [`evaluate s1 env fps1 _ = (s2, fps2, Rval r)`]
      \\ `fps1 = fps2`
        by (imp_res_tac evaluate_fp_stable
            \\ first_x_assum irule
            \\ imp_res_tac evaluate_fp_opts_inv
            \\ imp_res_tac evaluate_decs_fp_opts_inv
            \\ fs[])
      \\ fs[])
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ ntac 3 (TOP_CASE_TAC \\ fs[]))
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ ntac 3 (TOP_CASE_TAC \\ fs[]))
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ ntac 3 (TOP_CASE_TAC \\ fs[]))
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ ntac 3 (TOP_CASE_TAC \\ fs[]))
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ pop_assum mp_tac
      \\ ntac 3 (TOP_CASE_TAC \\ fs[])
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[]
      \\ imp_res_tac evaluate_decs_fp_opts_inv
      \\ fs[]
      \\ rename [`evaluate_decs s1 env fps1 _ = (s2, fps2, Rval r)`]
      \\ `fps1 = fps2`
        by (drule evaluate_decs_fp_stable \\ fs[])
      \\ rpt conj_tac \\ fs[combine_dec_result_def])
  >- (imp_res_tac evaluate_decs_fp_stable \\ simp[] \\ rveq
      \\ fs[evaluate_decs_def, Once evaluate_decs_cons]
      \\ pop_assum mp_tac
      \\ Cases_on `evaluate_decs s1 env fps1 decls1` \\ fs[]
      \\ rename [`evaluate_decs s1 env fps1 decls1 = (s2, r)`]
      \\ Cases_on `r` \\ fs[]
      \\ rename [`evaluate_decs s1 env fps1 decls1 = (s2, fps2, r)`]
      \\ reverse (Cases_on `r`) \\ fs[]
      >- (rpt strip_tac \\ rveq \\ fs[])
      \\ last_x_assum (qspec_then `[]` assume_tac)
      \\ fs[APPEND_NIL]
      \\ ntac 3 (TOP_CASE_TAC \\ fs[])
      \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[]
      \\ first_x_assum (qspec_then `[]` assume_tac)
      \\ fs[APPEND_NIL]
      \\ res_tac
      \\ rename [`evaluate_decs s2 (extend_dec_env _ env) fps2 _ = (s3, fps3, Rval r)`]
      \\ `fps1 = fps2`
          by (irule evaluate_decs_fp_stable \\ imp_res_tac evaluate_decs_fp_opts_inv
              \\ conj_tac
              >- (irule LESS_EQUAL_ANTISYM \\ conj_tac \\ TRY (first_x_assum (MATCH_ACCEPT_TAC))
                 \\ irule LESS_EQ_TRANS \\ qexists_tac `fps3.choices` \\ conj_tac
                 \\ TRY (first_x_assum (MATCH_ACCEPT_TAC)))
              \\ asm_exists_tac \\ first_x_assum (MATCH_ACCEPT_TAC))
      \\ `fps2 = fps3`
          by (irule evaluate_decs_fp_stable \\ imp_res_tac evaluate_decs_fp_opts_inv
              \\ conj_tac
              >- (irule LESS_EQUAL_ANTISYM \\ conj_tac \\ TRY (first_x_assum (MATCH_ACCEPT_TAC))
                 \\ irule LESS_EQ_TRANS \\ qexists_tac `fps1.choices` \\ conj_tac
                 \\ TRY (first_x_assum (MATCH_ACCEPT_TAC)))
              \\ asm_exists_tac \\ first_x_assum (MATCH_ACCEPT_TAC))
      \\ rveq \\ conj_tac \\ fs[])
QED

val _ = export_theory();
