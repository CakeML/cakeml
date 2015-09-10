open HolKernel Parse boolLib bossLib;

open closRelationTheory closSemTheory
open lcsymtacs

val _ = new_theory "closRelObservational";

val state_rel_io_mono = store_thm(
  "state_rel_io_mono[simp]",
  ``state_rel k s1 s2 ⇒
    state_rel k (s1 with io := io) (s2 with io := io)``,
  ONCE_REWRITE_TAC [val_rel_def] >> simp[]);

val exp_rel_evaluate_with_io = store_thm(
  "exp_rel_evaluate_with_io",
  ``(∀i v. val_rel i v v) ⇒
    ∀e1 e2.
      exp_rel e1 e2 ==>
      ∀s1 s2 k io r.
         state_rel k s1 s2 ⇒
         res_rel (evaluate_with_io e1 s1 (SOME io) k)
                 (evaluate_with_io e2 s2 (SOME io) k)``,
  simp[exp_rel_def, evaluate_with_io_def, exec_rel_rw, evaluate_ev_def] >>
  strip_tac >> qx_genl_tac [`e1`, `e2`] >> strip_tac >>
  qx_genl_tac [`s1`, `s2`, `k`, `io`] >>
  first_x_assum (qspecl_then [`k`, `[]`, `[]`,
                              `s1 with io := SOME io`,
                              `s2 with io := SOME io`]
                             mp_tac) >> simp[])

val resulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:(α,β) result``,
                        nchotomy = TypeBase.nchotomy_of ``:(α,β) result``}

val errorresulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α error_result``,
                        nchotomy = TypeBase.nchotomy_of ``:α error_result``}

val listeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α list``,
                        nchotomy = TypeBase.nchotomy_of ``:α list``}

val refeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α ref``,
                        nchotomy = TypeBase.nchotomy_of ``:α ref``}

val veq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:closSem$v``,
                        nchotomy = TypeBase.nchotomy_of ``:closSem$v``}

val eqresulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:eq_result``,
                        nchotomy = TypeBase.nchotomy_of ``:eq_result``}
val appkindeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:app_kind``,
                        nchotomy = TypeBase.nchotomy_of ``:app_kind``}

val paireq = prove(
  ``pair_CASE p f = v ⇔ ∃a b. p = (a,b) ∧ v = f a b``,
  Cases_on `p` >> simp[] >> metis_tac[]);

val ioeventeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:io_event``,
                        nchotomy = TypeBase.nchotomy_of ``:io_event``}

val booleq = prove(
  ``(if p then x else y) = z ⇔ p ∧ x = z ∨ ¬p ∧ y = z``,
  rw[]);



val optioneq = prove(
  ``option_CASE opt n s = x ⇔ opt = NONE ∧ n = x ∨ ∃y. opt = SOME y ∧ x = s y``,
  Cases_on `opt` >> simp[] >> metis_tac[]);

val do_app_preserves_ioNONE = store_thm(
  "do_app_preserves_ioNONE",
  ``do_app op args s = Rval (v, s') ∧ s.io = NONE ⇒ s'.io = NONE``,
  Cases_on `op` >> Cases_on `args` >>
  simp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  rw[] >> rw[] >> fs[ffiTheory.call_FFI_def]);

val dec_clock_io = store_thm(
  "dec_clock_io[simp]",
  ``(dec_clock n s).io = s.io``,
  simp[dec_clock_def]);

val ioNONE_preserved = store_thm(
  "ioNONE_preserved",
  ``(∀esenvs es env s s' rv.
       evaluate esenvs = (rv, s') ∧ esenvs = (es,env,s) ∧ s.io = NONE ⇒
       s'.io = NONE) ∧
    (∀l f vs s s' rv.
       evaluate_app l f vs s = (rv, s') ∧ s.io = NONE ⇒ s'.io = NONE)``,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[Once evaluate_def, paireq, resulteq, booleq, errorresulteq,
       optioneq, appkindeq, listeq] >>
  rpt strip_tac >> rw[]
  >- metis_tac[do_app_preserves_ioNONE]
  >- metis_tac[]);

open relationTheory
val exp3_size_EQ0 = store_thm(
  "exp3_size_EQ0[simp]",
  ``closLang$exp3_size l = 0 ⇔ l = []``,
  Cases_on `l` >> simp[closLangTheory.exp_size_def]);

val evaluate_ind' = save_thm(
  "evaluate_ind'",
    WF_INDUCTION_THM
      |> Q.ISPEC `
           inv_image ((<) LEX (<) LEX (<))
              (λx. case x of
                     INL (s:closSem$state,xs) =>
                       (s.clock, closLang$exp3_size xs, 0)
                   | INR (s:closSem$state,args) =>
                       (s.clock, 0, LENGTH (args:closSem$v list)))`
      |> SIMP_RULE (srw_ss()) [WF_inv_image, pairTheory.WF_LEX,
                               pairTheory.LEX_DEF, pairTheory.FORALL_PROD,
                               WF_TC, sumTheory.FORALL_SUM]
      |> Q.SPEC `λx. case x of INL (a1,a2) => P0 a1 a2
                             | INR (b1,b2) => Q0 b1 b2`
      |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]);

val _ = augment_srw_ss [rewrites [closLangTheory.exp_size_def]]
val kill_asm_guard =
    disch_then (fn th => SUBGOAL_THEN (lhand (concl th))
                                      (MP_TAC o MATCH_MP th)) >- simp[]

val merge1 = prove(
  ``(∀s:closSem$state x. s.clock < N ⇒ P s x) ∧
    (∀s x. s.clock = N ∧ Q s x ⇒ P s x) ⇒
    (∀s x. s.clock ≤ N ∧ Q s x ⇒ P s x)``,
  dsimp[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``]);

val merge2 = prove(
  ``(∀s:closSem$state x. s.clock < N ⇒ P s x) ∧ (∀s x. s.clock = N ⇒ P s x) ⇒
    ∀s x. s.clock ≤ N ⇒ P s x``,
  dsimp[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``]);

val merge_tac =
  first_x_assum (fn c1 => first_x_assum (fn c2 =>
    assume_tac (HO_MATCH_MP merge1 (CONJ c1 c2)))) ORELSE
  first_x_assum (fn c1 => first_x_assum (fn c2 =>
    assume_tac (HO_MATCH_MP merge2 (CONJ c1 c2))))

val killevalapp =
    rpt (first_x_assum (kall_tac o assert (free_in ``evaluate_app`` o concl)))

val (evclock1, evclock2) = CONJ_PAIR evaluate_clock

val acc_ts = map (fn th => th |> concl |> strip_forall |> #2 |> lhs |> rator)
                 (TypeBase.accessors_of ``:closSem$state``)

val upd_ts = map (fn th => th |> concl |> strip_forall |> #2 |> lhs
                              |> rator)
                 (TypeBase.updates_of ``:closSem$state``)

val extendio_def = Define`
  extendio s io =
    case s.io of
        NONE => s
      | SOME io0 => s with io := SOME (LAPPEND io0 io)
`;

val extendio_accessors = save_thm(
  "extendio_accessors[simp]",
  map (fn acc => prove(``^acc (extendio s io) = ^acc s``,
                       simp[extendio_def] >> Cases_on `s.io` >> simp[]))
      (filter (not o aconv ``state_io``) acc_ts) |> LIST_CONJ)

val extendio_updates = save_thm(
  "extendio_updates[simp]",
  map
    (fn upd => prove(``^upd (extendio s io) = extendio (^upd s) io``,
                     simp[extendio_def]>> Cases_on `s.io` >> simp[]))
    (filter (not o aconv ``state_io_fupd`` o rator) upd_ts) |> LIST_CONJ)

val is_ioextension_def = Define`
  maybeSuffix s0 io io' ⇔
    case s0.io of
        NONE => io' = NONE ∨ ∃n. 0 < n ∧ io' = LDROP n io
      | SOME io0 => io' = io
`;

val is_ioextension_trivial = store_thm(
  "is_ioextension_trivial[simp]",
  ``is_ioextension io s0 (extendio s0 io)``,
  simp[is_ioextension_def, extendio_def] >> Cases_on `s0.io` >> simp[]);

val is_ioextension_clock = store_thm(
  "is_ioextension_clock",
  ``is_ioextension io s1 s2 ⇒ s2.clock = s1.clock``,
  simp[is_ioextension_def] >> Cases_on `s1.io` >> simp[]

val doapp_extendio_type_error = store_thm(
  "doapp_extendio_type_error",
  ``do_app opt args s0 = Rerr (Rabort Rtype_error) ⇒
    do_app opt args (extendio s0 io) = Rerr (Rabort Rtype_error)``,
  Cases_on `opt` >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq])

val doapp_extendio_nonffi = store_thm(
  "doapp_extendio_nonffi",
  ``do_app opt args s0 = Rval (rv, s) ∧ (∀n. opt ≠ FFI n) ⇒
    do_app opt args (extendio s0 io) = Rval (rv, extendio s io)``,
  Cases_on `opt` >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  metis_tac[])

val doapp_extendio_SOMEioresult = store_thm(
  "doapp_extendio_SOMEioresult",
  ``do_app opt args s0 = Rval (rv, s) ∧ s.io ≠ NONE ⇒
    do_app opt args (extendio s0 io) = Rval (rv, extendio s io)``,
  Cases_on `∀n. opt ≠ FFI n` >> simp[] >- metis_tac[doapp_extendio_nonffi] >>
  fs[] >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  simp[ffiTheory.call_FFI_def] >> Cases_on `s0.io` >>
  simp[extendio_def] >> dsimp[optioneq, paireq, ioeventeq, booleq] >>
  csimp[] >> qcase_tac `LHD l0 = SOME (IO_event _ _)` >>
  Q.ISPEC_THEN `l0` STRUCT_CASES_TAC llistTheory.llist_CASES >> simp[]);

(*
val doapp_extendio_rval2 = store_thm(
  "doapp_extendio_rval2",
  ``do_app opt args s0 = Rval (rv, s) ∧ s.io = NONE ⇒
    ∃s'. do_app opt args (extendio s0 io) = Rval (rv, s') ∧
         (s' = s ∨ ∃n. 0 < n ∧ s' = s with io := LDROP n io)``,
  Cases_on `∀n. opt ≠ FFI n` >> simp[]
  >- (strip_tac >> `∀j. extendio s j = s` by simp[extendio_def] >>
      metis_tac[doapp_extendio_nonffi]) >> fs[] >>
  Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  csimp[] >>
  simp[ffiTheory.call_FFI_def, optioneq, paireq, ioeventeq, booleq,
       extendio_def] >> rw[] >> dsimp[] >>
  qcase_tac `io = [||]` >>
  Q.ISPEC_THEN `io` STRUCT_CASES_TAC llistTheory.llist_CASES >> simp[] >>
  simp[closSemTheory.state_component_equality] >>
  qcase_tac `io1 = IO_event _ _` >> Cases_on `io1` >> simp[] >>
  qcase_tac `n:num ≠ m` >> Cases_on `n = m` >> simp[]
*)

fun first_r_assum ttac = first_x_assum (fn th => ttac th >> assume_tac th)

(*
val evaluate_extendio_type_error = store_thm(
  "evaluate_extendio_type_error",
  ``(∀s0 es env rv s.
      evaluate (es,env,s0) = (rv, s) ⇒
      ∀io. ∃io'.
        evaluate (es,env,extendio s0 io) = (rv, extendio s io') ∧
        is_ioextension s io io') ∧
    (∀s0 vs l f rv s.
      evaluate_app l f vs s0 = (rv, s) ⇒
      ∀io. ∃s'.
         evaluate_app l f vs (extendio s0 io) = (rv, s') ∧
         is_ioextension io s s')``,
  ho_match_mp_tac evaluate_ind' >> conj_tac
  >- (qx_genl_tac [`s0`, `es`] >>
      Cases_on `es` >- simp[evaluate_def] >>
      qcase_tac `exp3_size (e1::es)` >> simp[] >> strip_tac >>
      reverse (Cases_on `es`)
      >- (ONCE_REWRITE_TAC [evaluate_def] >> killevalapp >> merge_tac >>
          dsimp[paireq,resulteq] >> rpt strip_tac
          >- (imp_res_tac evclock1 >> qcase_tac `extendio s0 io` >>
              first_r_assum (fn th =>
                qspecl_then [`s0`, `[e1]`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[] >>
                disch_then (qspec_then `io` (qx_choose_then `s1'` mp_tac))) >>
              strip_tac >> simp[]
              qcase_tac `evaluate (_::_,_,s1) = (_, s2)` >>
              Cases_on `s1.io` >> simp[] >>
              `s2.io = NONE` by metis_tac [ioNONE_preserved] >> simp[])
          >- (imp_res_tac evclock1 >>
              disj1_tac >> qcase_tac `evaluate ([e1], env, s0) = _` >>
              first_x_assum (fn th =>
                 qspecl_then [`s0`, `[e1]`] mp_tac th >> simp[] >>
                 disch_then (qspec_then `env` mp_tac) >> simp[] >>
                 assume_tac th) >>
              disch_then kall_tac >>
              qcase_tac `evaluate (e2::es, env, s1) = (Rerr err, s2)` >>
              Cases_on `s1.io` >> simp[] >>
              `s2.io = NONE` by metis_tac [ioNONE_preserved] >> simp[]))
      (* singleton list - cases of e1 *)
      simp[] >>
      Cases_on `e1` >> ONCE_REWRITE_TAC [evaluate_def]
      >- dsimp[booleq]
      >- ((* if *)
          killevalapp >> merge_tac >>
          qx_genl_tac [`env`, `rv`, `s'`, `io`] >>
          simp[SimpL ``$==>``, booleq, paireq, resulteq] >> rw[] >>
          imp_res_tac evclock1
          >- (qcase_tac `evaluate ([gd], env, s0) = (Rval vs, s1)` >>
              first_x_assum (fn th =>
                qspecl_then [`s0`, `[gd]`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[] >>
                assume_tac th) >>
              disch_then kall_tac >>
              qcase_tac `evaluate ([tb], env, s1) = (rv,s2)` >>
              Cases_on `s1.io` >> simp[] >>
              `s2.io = NONE` by metis_tac[ioNONE_preserved] >> simp[])
          >- (qcase_tac `evaluate ([gd], env, s0) = (Rval vs, s1)` >>
              first_x_assum (fn th =>
                qspecl_then [`s0`, `[gd]`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[] >>
                assume_tac th) >>
              disch_then kall_tac >>
              qcase_tac `evaluate ([fb], env, s1) = (rv,s2)` >>
              Cases_on `s1.io` >> simp[] >>
              `s2.io = NONE` by metis_tac[ioNONE_preserved] >> simp[])
          >- (qcase_tac `evaluate ([gd], env, s0) = (Rval vs, s1)` >>
              first_x_assum (qspecl_then [`s0`, `[gd]`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[])
          >- (qcase_tac `evaluate ([gd], env, s0) = (Rerr err, s1)` >>
              first_x_assum (qspecl_then [`s0`, `[gd]`] mp_tac) >>
              simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[]))
      >- ((* Let *) killevalapp >> merge_tac >>
          qcase_tac `Let es e` >> dsimp[paireq,resulteq] >>
          rpt strip_tac >> disj1_tac >> imp_res_tac evclock1 >>
          qcase_tac `evaluate (es,env,s0) = (Rval vs, s1)` >>
          first_x_assum (fn th =>
            qspecl_then [`s0`, `es`] mp_tac th >> simp[] >>
            disch_then (qspec_then `env` mp_tac) >> simp[] >>
            assume_tac th) >>
          disch_then kall_tac >>
          Cases_on `s1.io` >> simp[] >>
          qcase_tac `evaluate ([e], _, s1) = (_, s2)` >>
          `s2.io = NONE` by metis_tac[ioNONE_preserved] >> simp[])
      >- ((* Raise *) killevalapp >> merge_tac >>
          qcase_tac `closLang$Raise ex` >> dsimp[paireq,resulteq] >>
          qx_genl_tac [`env`, `s1`, `io`, `io'`, `vs`] >> rpt strip_tac >>
          first_x_assum (qspecl_then [`s0`, `[ex]`] mp_tac) >> simp[] >>
          disch_then (qspec_then `env` mp_tac) >> simp[])
      >- ((* Handle *) killevalapp >> merge_tac >>
          qcase_tac `closLang$Handle body h` >>
          dsimp[paireq, resulteq, errorresulteq] >>
          qx_genl_tac [`env`, `rv`, `s2`, `io`, `io'`, `s1`, `exnv`] >>
          rpt strip_tac >> imp_res_tac evclock1 >>
          first_x_assum (fn th =>
            qspecl_then [`s0`, `[body]`] mp_tac th >> simp[] >>
            disch_then (qspec_then `env` mp_tac) >> simp[] >>
            assume_tac th) >> disch_then kall_tac >>
          Cases_on `s1.io` >> simp[] >>
          `s2.io = NONE` by metis_tac[ioNONE_preserved] >> simp[])
      >- ((* Tick *) qcase_tac `Tick e` >> dsimp[booleq,dec_clock_def])
      >- ((* Call *)
          qcase_tac `closLang$Call f args` >> simp[] >> killevalapp >>
          qx_genl_tac [`env`, `rv`, `s1`, `io`] >>
          simp[SimpL ``$==>``, resulteq,paireq,optioneq,booleq] >> rw[]
          >- (qcase_tac `_ = (Rval vs, s1)` >> merge_tac >>
              first_x_assum (qspecl_then [`s0`,`args`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[] >>
              Cases_on `s1.io` >> simp[])
          >- (qcase_tac `_ = (Rval vs, s1)` >> merge_tac >>
              first_x_assum (qspecl_then [`s0`, `args`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[] >>
              Cases_on `s1.io` >> simp[])
          >- (qcase_tac `_ = (Rval vs, s')` >> imp_res_tac evaluate_clock >>
              qcase_tac `LAPPEND io io'` >>
              first_x_assum (fn th =>
                qspecl_then [`s0`, `args`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[]) >>
              disch_then kall_tac >>
              Cases_on `s'.io` >> simp[]
              >- (`s1.io = NONE`
                   by metis_tac[ioNONE_preserved, dec_clock_io] >> simp[]) >>
              fs[dec_clock_def] >>
              first_assum irule >- (first_x_assum ACCEPT_TAC) >>
              simp[])
          >- (merge_tac >>
              first_x_assum (qspecl_then [`s0`, `args`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[]))
      >- ((* App *) qcase_tac `App n f args` >>
          Cases_on `LENGTH args = 0` >> simp[] >> rpt merge_tac >>
          simp[SimpL ``$==>``, paireq, resulteq] >> rw[]
          >- (qcase_tac `evaluate (args,env,s0) = (Rval argsv, s1)` >>
              imp_res_tac evaluate_clock
              first_x_assum (fn th =>
                qspecl_then [`s0`, `args`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[] >>
                assume_tac th >> disch_then kall_tac) >>
              qcase_tac `evaluate ([f], env, s1) = (Rval fvs, s2)` >>
              qcase_tac `evaluate_app n (HD fvs) argsv s2 = (rv,s3)` >>
              Cases_on `s1.io` >> simp[]
              >- (`s3.io = NONE` by metis_tac[ioNONE_preserved] >> simp[]) >>
              first_x_assum (qspecl_then [`s1`, `[f]`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[] >>
              disch_then kall_tac >>
              Cases_on `s2.io` >> simp[] >>
              `s3.io = NONE` by metis_tac [ioNONE_preserved] >> simp[])
          >- (killevalapp >>
              qcase_tac `evaluate (args,env,s0) = (Rval argsv, s1)` >>
              first_x_assum (fn th =>
                qspecl_then [`s0`, `args`] mp_tac th >> simp[] >>
                disch_then (qspec_then `env` mp_tac) >> simp[] >>
                assume_tac th >> disch_then kall_tac) >>
              qcase_tac `evaluate ([f], env, s1) = (Rerr err, s2)` >>
              Cases_on `s1.io` >> simp[]
              >- (`s2.io = NONE` by metis_tac[ioNONE_preserved] >> simp[]) >>
              imp_res_tac evaluate_clock >>
              first_x_assum (qspecl_then [`s1`, `[f]`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[])
          >- (dsimp[resulteq, paireq]))
      >- ((* Fn *) qcase_tac `Fn nopt bvs n body` >>
          dsimp[booleq,optioneq])
      >- ((* Letrec *) qcase_tac `Letrec nopt bvs binds body` >>
          dsimp[booleq,optioneq])
      >- ((* Op *) qcase_tac `closLang$Op opt args` >> killevalapp >>
          merge_tac >> dsimp[paireq,resulteq] >> rpt strip_tac
          >- (qcase_tac `evaluate (args,env,s0) = (Rval argsv,s1)` >>
              first_x_assum (qspecl_then [`s0`, `args`] mp_tac) >> simp[] >>
              disch_then (qspec_then `env` mp_tac) >> simp[] >>
              disch_then kall_tac >> Cases_on `s1.io` >> simp[]
              >- (qcase_tac `do_app _ _ _ = Rval (_, s2)` >>
                  `s2.io = NONE` suffices_by simp[] >>
                  metis_tac[do_app_preserves_ioNONE]) >>










rpt strip_tac

  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[] >> ONCE_REWRITE_TAC [evaluate_def] >> dsimp[resulteq, paireq] >>
  rpt strip_tac
  >- (qcase_tac `evaluate ([e1], env, s0) = (Rval v1, s1)` >>
      `evaluate ([e1], env, s0 with io := SOME (LAPPEND io io')) =
         (Rval v1,
          case s1.io of NONE => s1
                      | SOME ior => s1 with io := SOME (LAPPEND ior io'))`
       by metis_tac[] >> simp[]


metis_tac[]

*)

val exp_rel_sem = store_thm(
  "exp_rel_sem",
  ``(∀i s. state_rel i s s) ∧ (∀i v. val_rel i v v) ∧
    (∀rv. res_rel rv rv) ⇒
    ∀e1 e2 s1 s2.
      exp_rel e1 e2 ∧ (∀i. state_rel i s1 s2) ==>
      ∀res. sem e1 s1 res /\ res ≠ Fail ==> sem e2 s2 res``,
  strip_tac >> qx_genl_tac [`e1`, `e2`, `s1`, `s2`] >> strip_tac >>
  qx_gen_tac `res` >>
  Cases_on `res` >> simp[sem_def]
  >- ((* diverge case *)
      strip_tac >> conj_tac
      >- (qx_gen_tac `k` >>
          first_x_assum
            (qspec_then `k` (qx_choose_then `s1'` strip_assume_tac)) >>
          qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME l) k` >>
          qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME l) k` >>
          `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
          pop_assum mp_tac >> simp[res_rel_rw] >> dsimp[] >>
          simp[Once state_rel_rw] >> metis_tac[])
      >- (qx_gen_tac `io` >> strip_tac >>
          `∃k. (SND (evaluate_with_io e1 s1 (SOME io) k)).io = NONE`
            by metis_tac[] >>
          qexists_tac `k` >>
          qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME io) k` >>
          qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME io) k` >>
          `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
          pop_assum mp_tac >>
          `∃r' s'. ev1 = (r',s')` by (Cases_on `ev1` >> simp[]) >>
          Cases_on `r'` >>
          simp[res_rel_rw] >> dsimp[]
          >- (var_eq_tac >> fs[] >> simp[Once state_rel_rw])
          >- (qcase_tac `res_rel (Rerr err, _)` >>
              Cases_on `err` >- (fs[res_rel_rw] >> dsimp[Once state_rel_rw]) >>
              qcase_tac `res_rel (Rerr (Rabort abt), _)` >>
              Cases_on `abt`
              >- ((* type error *) simp[res_rel_rw, Abbr`ev1`] >> fs[] >>
                  yikes)
              >- ((* timeout *)
                  simp[res_rel_rw] >> var_eq_tac >> fs[] >>
                  dsimp[Once state_rel_rw]))))
  >- ((* terminate case *)
      disch_then (qx_choosel_then [`k`, `s1'`, `r`] strip_assume_tac) >>
      qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME (fromList l)) k` >>
      qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME (fromList l)) k` >>
      qexists_tac `k` >>
      `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
      pop_assum mp_tac >> simp[res_rel_rw] >> dsimp[] >>
      simp[Once state_rel_rw]))

val _ = export_theory();
