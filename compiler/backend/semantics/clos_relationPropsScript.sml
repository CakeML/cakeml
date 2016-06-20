open preamble
open clos_relationTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_relationProps";

val state_rel_ffi_mono = store_thm(
  "state_rel_ffi_mono[simp]",
  ``state_rel k (s1:'ffi closSem$state) s2 ⇒
    state_rel k (s1 with ffi := (ffi:'ffi ffi_state)) (s2 with ffi := ffi)``,
  ONCE_REWRITE_TAC [val_rel_def] >> simp[]);

val exp_rel_evaluate = store_thm(
  "exp_rel_evaluate",
  ``∀e1 e2.
      exp_rel (:'ffi) e1 e2 ==>
      ∀(s1: 'ffi closSem$state) s2 k.
         state_rel k s1 s2 ⇒
         res_rel (evaluate (e1,[], s1 with clock := k))
                 (evaluate (e2,[], s2 with clock := k))``,
  simp[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
  qx_genl_tac [`e1`, `e2`] >> strip_tac >>
  qx_genl_tac [`s1`, `s2`, `k`] >>
  first_x_assum (qspecl_then [`k`, `[]`, `[]`, `s1`, `s2`]
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
  srw_tac[][]);

val optioneq = prove(
  ``option_CASE opt n s = x ⇔ opt = NONE ∧ n = x ∨ ∃y. opt = SOME y ∧ x = s y``,
  Cases_on `opt` >> simp[] >> metis_tac[]);

(*
val do_app_preserves_ioNONE = store_thm(
  "do_app_preserves_ioNONE",
  ``do_app op args s = Rval (v, s') ∧ s.io = NONE ⇒ s'.io = NONE``,
  Cases_on `op` >> Cases_on `args` >>
  simp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  srw_tac[][] >> srw_tac[][] >> full_simp_tac(srw_ss())[ffiTheory.call_FFI_def]);
*)

val dec_clock_ffi = store_thm(
  "dec_clock_ffi[simp]",
  ``(dec_clock n s).ffi = s.ffi``,
  simp[dec_clock_def]);

(*
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
  rpt strip_tac >> srw_tac[][]
  >- metis_tac[do_app_preserves_ioNONE]
  >- metis_tac[]);
*)

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
                     INL (s:'ffi closSem$state,xs) =>
                       (s.clock, closLang$exp3_size xs, 0)
                   | INR (s:'ffi closSem$state,args) =>
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
  ``(∀s:'ffi closSem$state x. s.clock < N ⇒ P s x) ∧
    (∀s x. s.clock = N ∧ Q s x ⇒ P s x) ⇒
    (∀s x. s.clock ≤ N ∧ Q s x ⇒ P s x)``,
  dsimp[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``]);

val merge2 = prove(
  ``(∀s:'ffi closSem$state x. s.clock < N ⇒ P s x) ∧ (∀s x. s.clock = N ⇒ P s x) ⇒
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
                 (TypeBase.accessors_of ``:'ffi closSem$state``)

val upd_ts = map (fn th => th |> concl |> strip_forall |> #2 |> lhs
                              |> rator)
                 (TypeBase.updates_of ``:'ffi closSem$state``)

(*
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
  full_simp_tac(srw_ss())[] >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  simp[ffiTheory.call_FFI_def] >> Cases_on `s0.io` >>
  simp[extendio_def] >> dsimp[optioneq, paireq, ioeventeq, booleq] >>
  csimp[] >> qcase_tac `LHD l0 = SOME (IO_event _ _)` >>
  Q.ISPEC_THEN `l0` STRUCT_CASES_TAC llistTheory.llist_CASES >> simp[]);
*)

fun first_r_assum ttac = first_x_assum (fn th => ttac th >> assume_tac th)

val res_rel_ffi = store_thm(
  "res_rel_ffi",
  ``res_rel (r1,s1) (r2,s2) ∧ r1 ≠ Rerr (Rabort Rtype_error) ⇒
    s2.ffi = s1.ffi``,
  Cases_on `r1` >> simp[]
  >- (simp[res_rel_rw] >> strip_tac >> full_simp_tac(srw_ss())[Once state_rel_rw]) >>
  qcase_tac `Rerr e` >> Cases_on `e` >> simp[]
  >- (simp[res_rel_rw] >> strip_tac >> full_simp_tac(srw_ss())[Once state_rel_rw]) >>
  qcase_tac `Rabort a` >> Cases_on `a` >> simp[res_rel_rw, Once state_rel_rw]);

val _ = temp_overload_on("fails",``λe s. ∃k. FST (evaluate (e,[],s with clock := k)) = Rerr (Rabort Rtype_error)``);
val _ = temp_overload_on("terminates",``λe s res.
  ∃k r s' outcome.
    evaluate (e,[],s with clock := k) = (r,s') ∧
    (case s'.ffi.final_event of
     | NONE => (∀a. r ≠ Rerr (Rabort a)) ∧ outcome = Success
     | SOME e => outcome = FFI_outcome e) ∧
    res = Terminate outcome s'.ffi.io_events``)

val exp_rel_semantics = store_thm(
  "exp_rel_semantics",
  ``∀e1 e2 (s1:'ffi closSem$state) s2.
      exp_rel (:'ffi) e1 e2 ∧ (∀i. state_rel i s1 s2) ∧
      semantics [] s1 e1 ≠ Fail ⇒
      semantics [] s1 e1 = semantics [] s2 e2``,
  qx_genl_tac [`e1`, `e2`, `s1`, `s2`] >> strip_tac >>
  simp[semantics_def] >>
  `fails e1 s1 ⇔ fails e2 s2` by (
    srw_tac[][EQ_IMP_THM] >>
    qexists_tac`k` >>
    qabbrev_tac `
      ev = λe (s:'ffi closSem$state). evaluate(e,[],s with clock := k)` >>
    full_simp_tac(srw_ss())[] >>
    `(∃r1 s1'. ev e1 s1 = (r1,s1')) ∧ (∃r2 s2'. ev e2 s2 = (r2,s2'))`
      by metis_tac[pair_CASES] >>
    `res_rel (r1,s1')(r2,s2')` by metis_tac[exp_rel_evaluate] >> full_simp_tac(srw_ss())[]
    >| [Cases_on`r1`,Cases_on`r2`] >>
    full_simp_tac(srw_ss())[]>> qcase_tac `Rerr e` >>
    Cases_on`e`>>full_simp_tac(srw_ss())[] >> qcase_tac `Rabort a` >>
    Cases_on `a` >> full_simp_tac(srw_ss())[res_rel_rw,semantics_def] >|[
      metis_tac[FST],
      Cases_on`r1`>>full_simp_tac(srw_ss())[res_rel_rw] >>
      Cases_on`e`>>full_simp_tac(srw_ss())[res_rel_rw] >>
      Cases_on`a`>>full_simp_tac(srw_ss())[res_rel_rw]]) >>
  simp[] >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  `∀res. terminates e1 s1 res ⇔ terminates e2 s2 res` by (
    srw_tac[][EQ_IMP_THM] >>
    qexists_tac`k`>>simp[] >>
    `state_rel k s1 s2` by metis_tac[] >>
    imp_res_tac exp_rel_evaluate >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    qmatch_assum_abbrev_tac`res_rel p1 p2` >>
    Cases_on`p1`>>Cases_on`p2`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
    imp_res_tac res_rel_ffi >>
    rpt var_eq_tac >> rev_full_simp_tac(srw_ss())[] >>
    ntac 2 (first_x_assum(qspec_then`k`mp_tac))>>simp[] >>
    ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    strip_tac >> full_simp_tac(srw_ss())[res_rel_rw] >>
    qmatch_assum_rename_tac`res_rel (x,_) _` >>
    Cases_on`x`>>full_simp_tac(srw_ss())[res_rel_rw] >> qcase_tac`Rerr e` >>
    Cases_on`e`>>full_simp_tac(srw_ss())[res_rel_rw] >> qcase_tac`Rabort a` >>
    Cases_on`a`>>full_simp_tac(srw_ss())[] >>
    strip_tac >> full_simp_tac(srw_ss())[res_rel_rw]) >>
  simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  strip_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >>
  qx_gen_tac `k` >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  qmatch_abbrev_tac`(SND p1).ffi = (SND p2).ffi` >>
  Cases_on`p1`>>Cases_on`p2`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
  `state_rel k s1 s2` by metis_tac[] >>
  imp_res_tac exp_rel_evaluate >> rev_full_simp_tac(srw_ss())[] >>
  imp_res_tac res_rel_ffi >>
  first_x_assum (match_mp_tac o GSYM) >>
  metis_tac[FST]);

val exp_rel_rtc_semantics_lem = Q.prove (
 `!e1 e2. (exp_rel (:'ffi))^* e1 e2 ⇒
    ∀(s1:'ffi closSem$state) s2.
      (∀i. state_rel i s1 s2) ∧ ¬(semantics [] s1 e1 = Fail) ⇒
       semantics [] s1 e1 = semantics [] s2 e2`,
 ho_match_mp_tac RTC_INDUCT >>
 metis_tac [exp_rel_semantics, state_rel_refl, exp_rel_refl]);

val exp_rel_rtc_semantics = Q.store_thm(
  "exp_rel_rtc_semantics",
  `∀e1 e2 (s1:'ffi closSem$state) s2.
      (exp_rel (:'ffi))^* e1 e2 ∧ (∀i. state_rel i s1 s2) ∧ ¬(semantics [] s1 e1 = Fail) ⇒
       semantics [] s1 e1 = semantics [] s2 e2`,
 metis_tac [exp_rel_rtc_semantics_lem]);

(* ----------------------------------------------------------------------
    Theorems specific to certain transformations

    Could perhaps be in ../proofs/clos_XProofScript.sml for various values
    of X.
   ---------------------------------------------------------------------- *)

val rev_take_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = l`,
 `LASTN (LENGTH l) l = l` by simp [LASTN_LENGTH_ID] >>
 rev_full_simp_tac(srw_ss())[] >>
 simp [GSYM LASTN_def, LASTN_LENGTH_ID]);

val rev_drop_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (DROP n (REVERSE l)) = []`,
 full_simp_tac(srw_ss())[DROP_REVERSE, BUTLASTN_LENGTH_NIL]);

val add_opt = Q.store_thm ("add_opt",
`!n1 n2. exp_rel (:'ffi) [Op Add [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 + n1)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val sub_opt = Q.store_thm ("sub_opt",
`!n1 n2. exp_rel (:'ffi) [Op Sub [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 - n1)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val mult_opt = Q.store_thm ("mult_opt",
`!n1 n2. exp_rel (:'ffi) [Op Mult [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 * n1)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val div_opt = Q.store_thm ("div_opt",
`!n1 n2. exp_rel (:'ffi) [Op Div [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 / n1)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 srw_tac[][res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val mod_opt = Q.store_thm ("mod_opt",
`!n1 n2. exp_rel (:'ffi) [Op Mod [Op (Const n1) []; Op (Const n2) []]]
                 [Op (Const (n2 % n1)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw] >>
 srw_tac[][res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val less_opt = Q.store_thm ("less_opt",
`!n1 n2.
  exp_rel (:'ffi) [Op Less [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 < n1 then true_tag else false_tag)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, Boolv_def, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val leq_opt = Q.store_thm ("leq_opt",
`!n1 n2.
  exp_rel (:'ffi) [Op LessEq [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 ≤ n1 then true_tag else false_tag)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val greater_opt = Q.store_thm ("greater_opt",
`!n1 n2.
  exp_rel (:'ffi) [Op Greater [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 > n1 then true_tag else false_tag)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val geq_opt = Q.store_thm ("geq_opt",
`!n1 n2.
  exp_rel (:'ffi) [Op GreaterEq [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 ≥ n1 then true_tag else false_tag)) []]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val app_combine = Q.store_thm ("app_combine",
`∀f f f' es1 es2 es1' es2'.
  LENGTH es1 = LENGTH es1' ∧
  LENGTH es2 = LENGTH es2' ∧
  LENGTH es1' + LENGTH es2' ≤ max_app ∧
  exp_rel (:'ffi) [f] [f'] ∧
  exp_rel (:'ffi) es1 es1' ∧
  exp_rel (:'ffi) es2 es2' ⇒
  exp_rel (:'ffi) [App NONE (App NONE f es1) es2] [App NONE f' (es2'++es1')]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 simp [evaluate_append] >>
 Cases_on `LENGTH es2 > 0` >>
 simp [res_rel_rw] >>
 qabbrev_tac `res2 = evaluate (es2,env,s with clock := i')` >>
 qabbrev_tac `res2' = evaluate (es2',env',s' with clock := i')` >>
 `res_rel res2 res2'` by metis_tac [] >>
 `?s2. (?v2. res2 = (Rerr v2, s2)) ∨ (?vs2. res2 = (Rval vs2, s2))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 `?s2. (?vs2. res2' = (Rval vs2, s2)) ∨ (?v2. res2' = (Rerr v2, s2))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- (
   Cases_on `v2` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   Cases_on `a` >>
   full_simp_tac(srw_ss())[res_rel_rw]) >>
 Cases_on `LENGTH es1 = 0`
 >- full_simp_tac(srw_ss())[res_rel_rw] >>
 `LENGTH es1' > 0` by decide_tac >>
 qabbrev_tac `res1 = evaluate (es1,env,s2 with clock := s2.clock)` >>
 qabbrev_tac `res1' = evaluate (es1',env',s2' with clock := s2.clock)` >>
 `res_rel res1 res1'`
 by (
   `s2.clock ≤ (s with clock := i').clock` by metis_tac [evaluate_clock] >>
   full_simp_tac(srw_ss())[] >>
   unabbrev_all_tac >>
   ONCE_REWRITE_TAC[Once(GSYM with_same_clock)] >>
   first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]) >>
   qexists_tac `s2.clock` >>
   srw_tac[][] >>
   `s2'.clock ≤ i` by decide_tac >>
   metis_tac [val_rel_mono_list]) >>
 `(s2 with clock := s2.clock) = s2` by simp [state_component_equality] >>
 `(s2' with clock := s2.clock) = s2'` by simp [state_component_equality] >>
 full_simp_tac(srw_ss())[] >>
 `?s1. (?v1. res1 = (Rerr v1, s1)) ∨ (?vs1. res1 = (Rval vs1, s1))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 `?s1. (?vs1. res1' = (Rval vs1, s1)) ∨ (?v1. res1' = (Rerr v1, s1))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- (
   Cases_on `v1` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   Cases_on `a` >>
   full_simp_tac(srw_ss())[res_rel_rw]) >>
 qabbrev_tac `res3 = evaluate ([f],env,s1 with clock := s1.clock)` >>
 qabbrev_tac `res3' = evaluate ([f'],env',s1' with clock := s1.clock)` >>
 `res_rel res3 res3'`
 by (
   `s2.clock ≤ (s with clock := i').clock` by metis_tac [evaluate_clock] >>
   `s1.clock ≤ s2.clock` by metis_tac [evaluate_clock] >>
   full_simp_tac(srw_ss())[] >>
   unabbrev_all_tac >>
   ONCE_REWRITE_TAC[Once(GSYM with_same_clock)] >>
   first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]) >>
   qexists_tac `s1.clock` >>
   srw_tac[][] >>
   `s1'.clock ≤ i` by decide_tac >>
   metis_tac [val_rel_mono_list]) >>
 `(s1 with clock := s1.clock) = s1` by simp [state_component_equality] >>
 `(s1' with clock := s1.clock) = s1'` by simp [state_component_equality] >>
 full_simp_tac(srw_ss())[] >>
 `?s3. (?v3. res3 = (Rerr v3, s3)) ∨ (?vs3. res3 = (Rval vs3, s3))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 `?s3. (?vs3. res3' = (Rval vs3, s3)) ∨ (?v3. res3' = (Rerr v3, s3))`
   by metis_tac [semanticPrimitivesTheory.result_nchotomy, pair_CASES] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- (
   Cases_on `v3` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   Cases_on `a` >>
   full_simp_tac(srw_ss())[res_rel_rw]) >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
 rpt (qpat_assum `_ = evaluate _` (mp_tac o GSYM)) >>
 srw_tac[][] >>
 `LENGTH vs2' + LENGTH vs1' ≤ max_app` by (
   imp_res_tac evaluate_length_imp >>
   full_simp_tac(srw_ss())[] >>
   decide_tac) >>
 simp [evaluate_app_append] >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[] >>
 `res_rel (evaluate_app NONE (HD vs3) vs1 s3) (evaluate_app NONE (HD vs3') vs1' s3')` by (
   Cases_on `vs1 = []` >>
   full_simp_tac(srw_ss())[]
   >- simp [evaluate_def, res_rel_rw] >>
   match_mp_tac res_rel_evaluate_app >>
   srw_tac[][] >>
   imp_res_tac evaluate_clock >>
   full_simp_tac(srw_ss())[] >>
   `s3'.clock ≤ s2'.clock` by decide_tac >>
   metis_tac [val_rel_mono_list]) >>
 rev_full_simp_tac(srw_ss())[] >>
 Cases_on `evaluate_app NONE (HD vs3) vs1 s3` >>
 rev_full_simp_tac(srw_ss())[] >>
 reverse (Cases_on `q`) >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- (
   Cases_on `e` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   srw_tac[][]
   >- metis_tac []
   >- metis_tac [] >>
   Cases_on `a` >>
   full_simp_tac(srw_ss())[res_rel_rw]) >>
 Cases_on `vs2 = []` >>
 full_simp_tac(srw_ss())[] >>
 `LENGTH a = 1 ∧ LENGTH vs' = 1` by (
   imp_res_tac evaluate_app_length_imp >>
   full_simp_tac(srw_ss())[])
 >- (srw_tac[][evaluate_def, res_rel_rw] >>
     Cases_on `a` >>
     Cases_on `vs'` >>
     full_simp_tac(srw_ss())[] >>
     simp [evaluate_def, res_rel_rw]) >>
 match_mp_tac res_rel_evaluate_app >>
 simp [] >>
 Cases_on `a` >>
 Cases_on `vs'` >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_clock >>
 `s''.clock ≤ s2'.clock` by decide_tac >>
 metis_tac [val_rel_mono_list]);

val fn_add_arg_lem = Q.prove (
`!i' num_args num_args' i env env' args args' e e'.
  num_args + num_args' ≤ max_app ∧
  LIST_REL (val_rel (:'ffi) i) env env' ∧
  LIST_REL (val_rel (:'ffi) i) args args' ∧
  i' ≤ i ∧
  exp_rel (:'ffi) [e] [e']
  ⇒
  val_rel (:'ffi) i' (Closure NONE args env num_args (Fn NONE NONE num_args' e))
                     (Closure NONE args' env' (num_args + num_args') e')`,
 completeInduct_on `i'` >>
 srw_tac[][val_rel_rw, is_closure_def] >>
 imp_res_tac LIST_REL_LENGTH
 >- simp [check_closures_def, clo_can_apply_def, clo_to_num_params_def,
          clo_to_partial_args_def, rec_clo_ok_def, clo_to_loc_def] >>
 Cases_on `locopt` >>
 simp [dest_closure_def, check_loc_def] >>
 `num_args' ≤ max_app` by decide_tac >>
 srw_tac[][] >>
 TRY decide_tac >>
 srw_tac[][exec_rel_rw, evaluate_ev_def, evaluate_def, check_loc_def] >>
 full_simp_tac(srw_ss())[NOT_LESS]
 >- ( (* Full application *)
   Cases_on `¬(LENGTH vs' ≤ LENGTH vs' − (num_args − LENGTH args') + (1 + i'''))` >>
   full_simp_tac(srw_ss())[]
   >- (
     `¬(LENGTH vs' ≤ LENGTH vs' − (num_args + num_args' − LENGTH args') + (1 + i'''))` by decide_tac >>
     full_simp_tac(srw_ss())[res_rel_rw] >>
     metis_tac [val_rel_mono, ZERO_LESS_EQ]) >>
   Cases_on `num_args' = 0` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   `num_args ≠ 0` by decide_tac >>
   `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs)) ≠ []` by simp [DROP_NIL]  >>
   `num_args − LENGTH args' ≤ 1 + i'''` by decide_tac >>
   simp [evaluate_app_rw, dest_closure_def, check_loc_def] >>
   srw_tac[][res_rel_rw] >>
   TRY decide_tac
   >- full_simp_tac (srw_ss()++ ARITH_ss) []
   >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
   simp [GSYM REVERSE_APPEND] >>
   simp [GSYM TAKE_SUM] >>
   simp [dec_clock_def] >>
   full_simp_tac(srw_ss())[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
   first_x_assum (qspecl_then [`i''`,
                           `REVERSE (TAKE (num_args + num_args' − LENGTH args') (REVERSE vs)) ++ args ++ env`,
                           `REVERSE (TAKE (num_args + num_args' − LENGTH args') (REVERSE vs')) ++ args' ++ env'`,
                           `s`,
                           `s'`] mp_tac) >>
   simp [] >>
   `LIST_REL (val_rel (:'ffi) i'') (REVERSE (TAKE (num_args + num_args' − LENGTH args') (REVERSE vs)) ++ args ++ env)
            (REVERSE (TAKE (num_args + num_args' − LENGTH args') (REVERSE vs')) ++ args' ++ env')` by (
     match_mp_tac EVERY2_APPEND_suff >>
     `i'' ≤ i` by decide_tac >>
     reverse (srw_tac[][])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     srw_tac[][LIST_REL_REVERSE_EQ, EVERY2_TAKE] >>
     metis_tac [val_rel_mono_list]) >>
   simp [] >>
   disch_then (qspec_then `i''' + (LENGTH args' + 1) − (num_args + num_args')` mp_tac) >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   simp [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   TRY (qcase_tac `(Rerr error, r)`)
   >- (
     Cases_on `REVERSE (DROP num_args' (DROP (num_args − LENGTH args') (REVERSE vs))) = []`
     >- (
       `REVERSE (DROP (num_args + num_args' − LENGTH args') (REVERSE vs')) = []` by (
         full_simp_tac(srw_ss())[DROP_NIL] >>
         decide_tac) >>
       simp [evaluate_def, res_rel_rw] >>
       metis_tac []) >>
     match_mp_tac res_rel_evaluate_app >>
     simp [LIST_REL_REVERSE_EQ] >>
     srw_tac[][DROP_DROP_T] >>
     simp [] >>
     match_mp_tac EVERY2_DROP >>
     simp [LIST_REL_REVERSE_EQ] >>
     imp_res_tac evaluate_clock >>
     full_simp_tac(srw_ss())[] >>
     `r'.clock ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono_list])
  >- (
    Cases_on `error` >>
    full_simp_tac(srw_ss())[res_rel_rw] >>
    qcase_tac `(Rerr (Rabort abort), r)` >>
    Cases_on `abort` >>
    full_simp_tac(srw_ss())[res_rel_rw]))
 >- ( (* Partial application on right, full application on left *)
   Cases_on `¬(LENGTH vs' ≤ LENGTH vs' − (num_args − LENGTH args') + (1 + i'''))` >>
   full_simp_tac(srw_ss())[]
   >- (  (* Timeout on left *)
     `¬(LENGTH vs' ≤ 1 + i''')` by decide_tac >>
     full_simp_tac(srw_ss())[res_rel_rw] >>
     metis_tac [val_rel_mono, ZERO_LESS_EQ]) >>
   Cases_on `num_args = LENGTH args + LENGTH vs`
   >- (`REVERSE (DROP (LENGTH vs') (REVERSE vs)) = []` by simp [DROP_NIL] >>
       simp [evaluate_def, res_rel_def] >>
       `i''' + 1 − LENGTH vs' ≤ i''` by decide_tac >>
       srw_tac[][]
       >- metis_tac [val_rel_mono] >>
       `REVERSE (TAKE (LENGTH vs') (REVERSE vs)) = vs`
         by metis_tac [TAKE_LENGTH_ID, LENGTH_REVERSE, REVERSE_REVERSE] >>
       simp [] >>
       qspecl_then [`i''' + 1 − LENGTH vs`, `i''`, `vs++args`, `vs'++args'`, `env`, `env'`, `[]`, `[]`] mp_tac
         fn_partial_arg >>
       simp [] >>
       srw_tac[][] >>
       pop_assum match_mp_tac >>
       `i'' ≤ i` by decide_tac >>
       metis_tac [EVERY2_APPEND, val_rel_mono_list])
   >- (Cases_on `num_args' = 0` >>
       full_simp_tac(srw_ss())[res_rel_rw] >>
       `num_args ≠ 0` by decide_tac >>
       `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs)) ≠ []` by simp [DROP_NIL] >>
       asm_simp_tac (srw_ss()) [evaluate_app_rw, res_rel_def, dest_closure_def, check_loc_def] >>
       `LENGTH vs' ≤ num_args − LENGTH args' + max_app ∧ 0 < num_args'` by decide_tac >>
       asm_simp_tac (srw_ss()) [] >>
       `(LENGTH vs' < num_args − LENGTH args' + num_args')` by decide_tac >>
       asm_simp_tac (srw_ss()) [] >>
       `LENGTH vs' − (LENGTH vs' − (num_args − LENGTH args')) = num_args - LENGTH args'` by intLib.ARITH_TAC >>
       asm_simp_tac (srw_ss()) [] >>
       srw_tac[][res_rel_rw]
       >- intLib.ARITH_TAC
       >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
       >- (
         simp_tac (srw_ss()) [dec_clock_def] >>
         `i''' − (num_args − LENGTH args' − 1) − (LENGTH vs' − (num_args − LENGTH args')) =
          i''' + 1 - LENGTH vs'` by intLib.ARITH_TAC >>
         simp [] >>
         qspecl_then [`i''' + 1 − LENGTH vs`, `i''`, `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs)) ++ args`,
                      `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) ++ args'`,
                      `env`, `env'`,
                      `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs))`,
                      `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs'))`,
                      `num_args'`, `e`] mp_tac
           fn_partial_arg >>
         `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs')) ++
          REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) = vs'`
           by srw_tac[][GSYM REVERSE_APPEND] >>
         srw_tac[][] >>
         pop_assum (qspecl_then [] mp_tac) >>
         `num_args' + (num_args − LENGTH args' + LENGTH args') = num_args + num_args'` by intLib.ARITH_TAC >>
         srw_tac[][]  >>
         pop_assum match_mp_tac >>
         `i''' + 1 ≤ LENGTH vs' + i'' ∧ i'' ≤ i` by intLib.ARITH_TAC >>
         srw_tac[][] >>
         TRY (match_mp_tac EVERY2_APPEND_suff) >>
         srw_tac[][LIST_REL_REVERSE_EQ] >>
         TRY (match_mp_tac EVERY2_TAKE) >>
         TRY (match_mp_tac EVERY2_DROP) >>
         srw_tac[][LIST_REL_REVERSE_EQ] >>
         metis_tac [val_rel_mono_list])
       >- (
         `i''' − (num_args − LENGTH args' − 1) − (LENGTH vs' − (num_args − LENGTH args')) ≤ i''`
           by intLib.ARITH_TAC >>
         simp_tac (srw_ss()) [dec_clock_def] >>
         metis_tac [val_rel_mono])
       >- (
         simp_tac (srw_ss()) [dec_clock_def] >>
         intLib.ARITH_TAC)
       >- intLib.ARITH_TAC))
 >- ( (* Partial application *)
   Cases_on `¬(LENGTH vs' ≤ 1 + i''')` >>
   full_simp_tac(srw_ss())[res_rel_rw]
   >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
   reverse (srw_tac[][])
   >- (`i''' − (LENGTH vs' − 1) ≤ i''` by  decide_tac >>
       metis_tac [val_rel_mono]) >>
   first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]) >>
   simp [] >>
   qexists_tac `i''` >>
   reverse (srw_tac[][])
   >- decide_tac >>
   `i'' ≤ i` by decide_tac >>
   metis_tac [val_rel_mono_list, EVERY2_APPEND, LIST_REL_LENGTH]));

val fn_add_arg = Q.store_thm ("fn_add_arg",
`!num_args num_args' e e'.
  num_args + num_args' ≤ max_app ∧
  exp_rel (:'ffi) [e] [e'] ⇒
  exp_rel (:'ffi) [Fn NONE NONE num_args (Fn NONE NONE num_args' e)]
          [Fn NONE NONE (num_args + num_args') e']`,
 srw_tac[][] >>
 simp [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 srw_tac[][res_rel_rw] >>
 Cases_on `num_args = 0` >>
 full_simp_tac(srw_ss())[res_rel_rw] >>
 metis_tac [val_rel_mono, fn_add_arg_lem, LIST_REL_NIL]);

 (*
val fn_add_loc = Q.store_thm ("fn_add_loc",
`!vars num_args e l. exp_rel (:'ffi) [Fn NONE vars num_args e] [Fn (SOME l) vars num_args e]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def] >>
 Cases_on `clos_env s.restrict_envs vars env` >>
 srw_tac[][res_rel_rw] >>
 `s.restrict_envs = s'.restrict_envs` by full_simp_tac(srw_ss())[Once state_rel_rw] >>
 imp_res_tac val_rel_clos_env >>
 rev_full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[val_rel_rw, is_closure_def, check_closures_def, clo_can_apply_def,
     clo_to_loc_def, clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 reverse (srw_tac[][])
 >- metis_tac [val_rel_mono] >>
 srw_tac[][exec_rel_rw] >>
 `args ≠ [] ∧ args' ≠ []` by (Cases_on `args` >> Cases_on `args'` >> full_simp_tac(srw_ss())[]) >>
 simp [evaluate_app_rw, dest_closure_def] >>
 Cases_on `loc ` >>
 full_simp_tac(srw_ss())[check_loc_def, res_rel_rw] >>
 srw_tac[][res_rel_rw] >>
 simp [] >>
 imp_res_tac LIST_REL_LENGTH >>
 full_simp_tac(srw_ss())[]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
 full_simp_tac(srw_ss())[dec_clock_def] >>
 simp [rev_take_rev_all, rev_drop_rev_all] >>
 qabbrev_tac `l = LENGTH args'` >>
 `LENGTH args = l` by metis_tac [] >>
 `exp_rel [e] [e]` by metis_tac [exp_rel_refl] >>
 full_simp_tac(srw_ss())[exp_rel_def] >>
 pop_assum (qspecl_then [`i''' - l`,
              `args++x`,
              `args' ++ vs2'`,
              `s'' with clock := i''' - l`,
              `s''' with clock := i''' - l`] mp_tac) >>
              `i'''- l ≤ i''` by decide_tac >>
 imp_res_tac val_rel_mono >>
 simp [state_rel_clock] >>
 rev_full_simp_tac(srw_ss())[] >>
 `i'''- l ≤ i'' ∧ i'''- l ≤ i` by decide_tac >>
 `LIST_REL (val_rel (i''' − l)) (args ++ x) (args' ++ vs2')`
           by metis_tac [EVERY2_APPEND, val_rel_mono_list] >>
 simp [exec_rel_rw] >>
 DISCH_TAC >>
 pop_assum (qspec_then `i'''-l` mp_tac) >>
 simp [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],args ++ x,s'' with clock := i''' − l)`
           result_store_cases)) >>
 simp [res_rel_rw] >>
 DISCH_TAC >>
 full_simp_tac(srw_ss())[]
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][evaluate_def, res_rel_rw] );
 *)

(*
if this is needed, give it a different name...

val exp_rel_semantics = Q.store_thm("exp_rel_semantics",
  `exp_rel (:'ffi) e1 e2 ∧
   semantics [] (s:'ffi closSem$state) e1 ≠ Fail ⇒
   semantics [] s e2 = semantics [] s e1`,
  srw_tac[][] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac exp_rel_semantics >>
  srw_tac[][state_rel_refl]);
*)

val res_rel_val2 = Q.store_thm(
  "res_rel_val2",
  `res_rel v (Rval l2, (s2:'ffi closSem$state)) ⇔
     (∃s1. v = (Rerr (Rabort Rtype_error), s1)) ∨
     (∃l1 s1. v = (Rval l1, s1) ∧ LIST_REL (val_rel (:'ffi) s1.clock) l1 l2 ∧
              s1.clock = s2.clock ∧ state_rel s1.clock s1 s2)`,
  Cases_on `v` >> qcase_tac `res_rel (res,s1)` >> Cases_on `res` >>
  simp[res_rel_rw] >- metis_tac[] >>
  qcase_tac `Rerr err` >> Cases_on `err` >> simp[res_rel_rw] >>
  qcase_tac `Rabort abt` >> Cases_on `abt` >> simp[res_rel_rw]);

val exp_rel_thm = save_thm(
  "exp_rel_thm",
  exp_rel_def
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [exec_rel_rw, evaluate_ev_def,
                                         AND_IMP_INTRO])

val exp_rel_NIL_CONS = Q.store_thm(
  "exp_rel_NIL_CONS[simp]",
  `exp_rel (:'ffi) [] (e::es) ⇔ F`,
  simp[exp_rel_thm, evaluate_def] >>
  simp[Once evaluate_CONS, res_rel_rw, pair_case_eq, eqs] >>
  metis_tac[val_rel_refl, state_rel_refl, DECIDE ``n:num ≤ n``]);

val res_rel_Rerr_Rval = Q.store_thm(
  "res_rel_Rerr_Rval[simp]",
  `res_rel (Rerr e, s1) (Rval rv, s2) ⇔ e = Rabort Rtype_error`,
  Cases_on `e` >> simp[res_rel_rw] >>
  qcase_tac `Rabort a` >> Cases_on `a` >> simp[res_rel_rw]);

val res_rel_Rval_Rerr = Q.store_thm(
  "res_rel_Rval_Rerr[simp]",
  `res_rel (Rval rv, s1) (Rerr e, s2) = F`,
  Cases_on `e` >> simp[res_rel_rw]);

val res_rel_cases = Q.store_thm(
  "res_rel_cases",
  `res_rel v1 v2 ⇔
     (∃s1. v1 = (Rerr (Rabort Rtype_error), s1)) ∨
     (∃rv1 rv2 (s1:'ffi closSem$state) s2.
       v1 = (Rval rv1, s1) ∧ v2 = (Rval rv2, s2) ∧
       state_rel s2.clock s1 s2 ∧ LIST_REL (val_rel (:'ffi) s2.clock) rv1 rv2 ∧
       s1.clock = s2.clock) ∨
     (∃exn1 exn2 (s1:'ffi closSem$state) s2.
       v1 = (Rerr (Rraise exn1), s1) ∧ v2 = (Rerr (Rraise exn2), s2) ∧
       val_rel (:'ffi) s2.clock exn1 exn2 ∧ state_rel s2.clock s1 s2 ∧
       s1.clock = s2.clock) ∨
     (∃s1 s2. v1 = (Rerr (Rabort Rtimeout_error), s1) ∧
              v2 = (Rerr (Rabort Rtimeout_error), s2) ∧
              state_rel s1.clock s1 s2)`,
  Cases_on `v1` >> qcase_tac `res_rel (res1, s1)` >>
  Cases_on `v2` >> qcase_tac `res_rel _ (res2, s2)` >>
  Cases_on `res1` >> simp[] >> Cases_on `res2` >> simp[res_rel_rw]
  >- metis_tac[] >>
  qcase_tac `Rerr e1` >> Cases_on `e1` >> simp[res_rel_rw] >- metis_tac[] >>
  qcase_tac `Rabort a` >> Cases_on `a` >> simp[res_rel_rw])

val res_rel_typeerror = Q.store_thm(
  "res_rel_typeerror[simp]",
  `res_rel (Rerr (Rabort Rtype_error), s) v = T`,
  simp[res_rel_rw]);

val val_rel_bool = Q.store_thm(
  "val_rel_bool[simp]",
  `val_rel (:'ffi) c (Boolv b) v ⇔ v = Boolv b`,
  Cases_on `v` >> simp[val_rel_rw, Boolv_def] >> metis_tac[]);

val _ = export_theory();
