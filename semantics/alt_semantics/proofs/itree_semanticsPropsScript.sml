(*
  Properties about the itree- and FFI state-based CakeML semantics
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory
     arithmeticTheory llistTheory pred_setTheory;
open namespaceTheory astTheory ffiTheory semanticPrimitivesTheory
     evaluatePropsTheory smallStepTheory smallStepPropsTheory lprefix_lubTheory;
open itreeTheory itree_semanticsTheory;

val _ = new_theory "itree_semanticsProps";

(******************** Definitions ********************)


(***** Step-counting version of smallStep RTC definitions *****)

Definition step_n_cml_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) (Estep st) = step_n_cml n (e_step st) ∧
  step_n_cml _ e = e
End

Definition is_halt_cml_def:
  is_halt_cml (Estep (env, st_ffi, fp, Val v, [])) = T ∧
  is_halt_cml (Estep (env, st_ffi, fp, Exn v, [])) = T ∧
  is_halt_cml (Eabort a) = T ∧
  is_halt_cml _ = F
End

Definition step_to_halt_cml_def:
  step_to_halt_cml e =
    case some n. is_halt_cml (step_n_cml n e) of
    | NONE => NONE
    | SOME n => SOME $ step_n_cml n e
End

Definition step_n_cml_def[allow_rebind]:
  step_n_cml env 0 d = d ∧
  step_n_cml env (SUC n) (Dstep st) = step_n_cml env n (decl_step env st) ∧
  step_n_cml env _ d = d
End

Definition is_halt_cml_def[allow_rebind]:
  is_halt_cml (Dstep step) = F ∧
  is_halt_cml (Dabort err) = T ∧
  is_halt_cml Ddone = T ∧
  is_halt_cml (Draise v) = T
End

Definition dstep_to_halt_cml_def:
  dstep_to_halt_cml env e =
    case some n. is_halt_cml (step_n_cml env n e) of
    | NONE => NONE
    | SOME n => SOME $ step_n_cml env n e
End


(***** Relating smallStep and itree-based semantics for expressions *****)

Inductive result_rel:
  result_rel (Rval v) (Rval v) ∧
  result_rel (Rraise v) (Rerr $ Rraise v)
End

Inductive ctxt_frame_rel:
  ctxt_frame_rel Craise (Craise ()) ∧
  ctxt_frame_rel (Chandle pes) (Chandle () pes) ∧
  ctxt_frame_rel (Capp op vs es) (Capp op vs () es) ∧
  ctxt_frame_rel (Clog lop e) (Clog lop () e) ∧
  ctxt_frame_rel (Cif e1 e2) (Cif () e1 e2) ∧
  ctxt_frame_rel (Cmat_check pes v) (Cmat_check () pes v) ∧
  ctxt_frame_rel (Cmat pes v) (Cmat () pes v) ∧
  ctxt_frame_rel (Clet vopt e) (Clet vopt () e) ∧
  ctxt_frame_rel (Ccon idopt vs es) (Ccon idopt vs () es) ∧
  ctxt_frame_rel (Ctannot ty) (Ctannot () ty) ∧
  ctxt_frame_rel (Clannot ls) (Clannot () ls) ∧
  ctxt_frame_rel (Coptimise oldSc sc) (Coptimise oldSc sc ())
End

Definition ctxt_rel_def:
  ctxt_rel cs1 cs2 =
    LIST_REL (λ(c1,env1) (c2,env2). ctxt_frame_rel c1 c2 ∧ env1 = env2) cs1 cs2
End

Inductive step_result_rel:
  (ctxt_rel cs1 cs2 ⇒
    step_result_rel (Estep (env, st, fp, ev, cs1)) (Estep (env, (st, ffi), fp, ev, cs2))) ∧
  step_result_rel Edone Estuck ∧
  step_result_rel (Etype_error fp) (Eabort (fp, Rtype_error))
End

(***** Relating smallStep and itree-based semantics for declarations *****)

Definition dstate_rel_def:
  dstate_rel (dst : dstate) (st : 'a state) ⇔
    dst.refs = st.refs ∧
    dst.next_type_stamp = st.next_type_stamp ∧
    dst.next_exn_stamp = st.next_exn_stamp ∧
    dst.eval_state = st.eval_state ∧
    dst.fp_state = st.fp_state
End

Inductive deval_rel:
  deval_rel (itree_semantics$Decl d) (smallStep$Decl d) ∧
  deval_rel (Env e) (Env e) ∧
  (ctxt_rel cs scs ⇒
    deval_rel (ExpVal env ev cs l p) (ExpVal env ev scs l p))
End

Inductive dstep_result_rel:
  (dstate_rel dst st ∧ deval_rel dev1 dev2 ⇒
    dstep_result_rel
      (itree_semantics$Dstep dst dev1 dcs) (smallStep$Dstep (st, dev2, dcs))) ∧
  dstep_result_rel Ddone Ddone ∧
  dstep_result_rel (Draise v) (Draise v) ∧
  dstep_result_rel (Dtype_error fp) (Dabort (fp, Rtype_error))
End

(***** Play out a particular trace prefix from a given itree, modelling the
       environment as an FFI oracle with associated FFI state (as in CakeML) *****)
Definition trace_prefix_def:
  trace_prefix 0 (oracle, ffi_st) itree = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Ret r) = ([], SOME r) ∧
  trace_prefix (SUC n) (oracle, ffi_st)  Div    = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Vis (s, conf, ws) f) =
    case oracle s ffi_st conf ws of
    | Oracle_return ffi_st' ws' =>
        let (io, res) = trace_prefix n (oracle, ffi_st') (f $ INR ws') in
        if LENGTH ws ≠ LENGTH ws' then (io, res)
        else (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix n (oracle, ffi_st) (f $ INL outcome)
End


(***** Misc definitions *****)

Definition is_Effi_def:
  is_Effi (Effi (ExtCall _) _ _ _ _ _ _) = T ∧
  is_Effi _ = F
End

Definition is_Dffi_def:
  is_Dffi (Dffi _ (ExtCall _,_) _ _ _) = T ∧
  is_Dffi _ = F
End

Definition get_ffi_def:
  get_ffi (Estep (env, (st, ffi), fp, ev, cs)) = SOME ffi ∧
  get_ffi _ = NONE
End

Definition dget_ffi_def:
  dget_ffi (Dstep (st, dev, dcs)) = SOME st.ffi ∧
  dget_ffi _ = NONE
End


(******************** Useful simplifications ********************)

(* Deliberately no `application_def` here *)
val smallstep_ss = simpLib.named_rewrites "smallstep_ss" [
    smallStepTheory.continue_def,
    smallStepTheory.return_def,
    smallStepTheory.push_def,
    smallStepTheory.e_step_def
    ];

val dsmallstep_ss = simpLib.named_rewrites "dsmallstep_ss" [
    smallStepTheory.collapse_env_def,
    smallStepTheory.decl_continue_def,
    smallStepTheory.decl_step_def
    ];

val itree_ss = simpLib.named_rewrites "itree_ss" [
    itree_semanticsTheory.exn_continue_def,
    itree_semanticsTheory.continue_def,
    itree_semanticsTheory.return_def,
    itree_semanticsTheory.push_def,
    itree_semanticsTheory.estep_def,
    get_ffi_def
    ];

val ditree_ss = simpLib.named_rewrites "ditree_ss" [
    itree_semanticsTheory.dcontinue_def,
    itree_semanticsTheory.dreturn_def,
    itree_semanticsTheory.dpush_def,
    itree_semanticsTheory.dstep_def,
    dget_ffi_def
    ];

Theorem step_n_same[simp]:
  (∀env n. step_n env n Ddone = Ddone) ∧
  (∀env n fp. step_n env n (Dtype_error fp) = (Dtype_error fp)) ∧
  (∀env n st ev l p dcs.  step_n env n (Dffi st ev l p dcs) = Dffi st ev l p dcs) ∧
  (∀env n v. step_n env n (Draise v) = Draise v) ∧
  (∀env n. step_n_cml env n Ddone = Ddone) ∧
  (∀env n err. step_n_cml env n (Dabort err) = (Dabort err)) ∧
  (∀env n v. step_n_cml env n (Draise v) = Draise v)
Proof
  rpt conj_tac >> strip_tac >>
  Cases >> rw[step_n_def, step_n_cml_def]
QED

Theorem is_Effi_def[allow_rebind]:
  is_Effi e ⇔ ∃ s ws1 ws2 n env st cs. e = Effi (ExtCall s) ws1 ws2 n env st cs
Proof
  Cases_on `e` >> simp[is_Effi_def] >> rename [‘Effi f’] >>
  Cases_on ‘f’ >> simp[is_Effi_def]
QED

Theorem is_Dffi_def[allow_rebind]:
  is_Dffi d ⇔ ∃st s ev0 l p dcs. d = Dffi st (ExtCall s, ev0) l p dcs
Proof
  Cases_on `d` >> simp[is_Dffi_def] >> rename [‘Dffi d tup’] >>
  PairCases_on ‘tup’ >> Cases_on ‘tup0’ >> simp[is_Dffi_def]
QED

Theorem step_result_rel_not_Effi:
  ∀e1 e2. step_result_rel e1 e2 ⇒ ¬ is_Effi e1
Proof
  rw[step_result_rel_cases, is_Effi_def]
QED

Theorem dstep_result_rel_not_Dffi:
  ∀a b. dstep_result_rel a b ⇒ ¬ is_Dffi a
Proof
  rw[dstep_result_rel_cases, is_Dffi_def]
QED


(******************** Relate smallStep RTC and step-counting ********************)

(***** Lemmas *****)

Theorem cml_application_thm = smallStepPropsTheory.application_thm;

Theorem application_not_Estuck:
  application op env st_ffi fp vs cs ≠ Estuck
Proof
  rw[cml_application_thm] >>
  EVERY_CASE_TAC >> gvs[SF smallstep_ss]
QED

Theorem e_step_to_Estuck:
  e_step (env, st_ffi, fp, ev, cs) = Estuck ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Exn v ∧ cs = [])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF smallstep_ss]) >>
  gvs[e_step_def] >> TOP_CASE_TAC >> gvs[]
  >- (every_case_tac >> gvs[SF smallstep_ss, application_not_Estuck]) >>
  gvs[AllCaseEqs(), SF smallstep_ss, application_not_Estuck]
QED

Theorem step_n_cml_eq_Dstep:
  ∀env n e st.
    step_n_cml env n e = Dstep st
  ⇒ ∀m. m < n ⇒ ∃st'. step_n_cml env m e = Dstep st'
Proof
  strip_tac >> Induct >> rw[step_n_cml_def] >>
  Cases_on `e` >> gvs[step_n_cml_def] >>
  Cases_on `m` >> gvs[step_n_cml_def]
QED

Theorem step_n_cml_alt_def:
  step_n_cml env 0 e = e ∧
  step_n_cml env (SUC n) e = (
    case step_n_cml env n e of
    | Dstep st => decl_step env st
    | e => e)
Proof
  rw[step_n_cml_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[step_n_cml_def] >> simp[]
QED

Theorem step_n_cml_add:
  ∀env a b e. step_n_cml env (a + b) e = step_n_cml env a (step_n_cml env b e)
Proof
  strip_tac >> Induct >> rw[step_n_cml_def] >>
  simp[ADD_CLAUSES, step_n_cml_alt_def]
QED

Theorem is_halt_cml_step_n_cml_eq:
  ∀n m e env.
    is_halt_cml (step_n_cml env n e) ∧
    is_halt_cml (step_n_cml env m e)
  ⇒ step_n_cml env n e = step_n_cml env m e
Proof
  rw[] >> wlog_tac `n < m` [`n`,`m`]
  >- (Cases_on `n = m` >> gvs[]) >>
  imp_res_tac LESS_STRONG_ADD >> gvs[] >>
  gvs[step_n_cml_add |> ONCE_REWRITE_RULE[ADD_COMM]] >>
  Cases_on `step_n_cml env n e` >> gvs[is_halt_cml_def]
QED


(***** Results *****)

Theorem decl_step_reln_eq_step_n_cml:
  (decl_step_reln env)^* st1 st2 ⇔
  ∃n. step_n_cml env n (Dstep st1) = Dstep st2
Proof
  reverse $ eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`st2`,`st1`,`n`] >>
    Induct >> rw[step_n_cml_alt_def] >>
    every_case_tac >> gvs[] >>
    rw[Once relationTheory.RTC_CASES2] >> disj2_tac >>
    last_x_assum $ irule_at Any >> gvs[decl_step_reln_def]
    )
  >- (
    Induct_on `(decl_step_reln env)^*` >> rw[]
    >- (qexists_tac `0` >> gvs[step_n_cml_def])
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_def, decl_step_reln_def])
    )
QED

Theorem small_eval_dec_eq_step_n_cml:
  (small_eval_dec env dst (st, Rval e) ⇔
    ∃n. step_n_cml env n (Dstep dst) = Dstep (st, Env e, [])) ∧
  (small_eval_dec env dst (st, Rerr (Rraise v)) ⇔
    ∃n dev dcs fp.
      step_n_cml env n (Dstep dst) = Dstep (st with fp_state := fp, dev, dcs) ∧
      decl_step env (st with fp_state := fp, dev, dcs) = Draise (st.fp_state, v)) ∧
  (small_eval_dec env dst (st, Rerr (Rabort err)) ⇔
    ∃n dev dcs fp.
      step_n_cml env n (Dstep dst) = Dstep (st with fp_state:= fp, dev, dcs) ∧
      decl_step env (st with fp_state := fp, dev, dcs) = Dabort (st.fp_state, err))
Proof
  rw[small_eval_dec_def, decl_step_reln_eq_step_n_cml] >>
  eq_tac >> rw[PULL_EXISTS] >> rpt $ goal_assum drule
QED

Theorem dec_diverges_eq_step_to_halt_cml:
  small_decl_diverges env dst ⇔ dstep_to_halt_cml env (Dstep dst) = NONE
Proof
  rw[dstep_to_halt_cml_def, small_decl_diverges_def,
     decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  eq_tac >> rw[] >> gvs[e_step_reln_def]
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >>
    Induct_on `x` >> rw[] >> gvs[step_n_cml_alt_def, is_halt_cml_def] >>
    CASE_TAC >> gvs[] >>
    last_x_assum drule >> strip_tac >> gvs[decl_step_reln_def, is_halt_cml_def]
    )
  >- (
    last_x_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
    first_x_assum $ qspec_then `SUC n` assume_tac >>
    gvs[step_n_cml_alt_def] >>
    Cases_on `decl_step env b` >> gvs[is_halt_cml_def, decl_step_reln_def]
    )
QED


(******************** Lemmas ********************)

(***** trace_prefix *****)

Theorem trace_prefix_prefix:
  ∀n m oracle ffi t io res io' res'. n ≤ m ∧
    trace_prefix n (oracle,ffi) t = (io,res) ∧
    trace_prefix m (oracle,ffi) t = (io',res')
  ⇒ io ≼ io'
Proof
  Induct >> rw[] >> gvs[trace_prefix_def] >>
  Cases_on `m` >> gvs[] >> rename1 `_ ≤ m` >>
  first_x_assum drule >> rw[] >>
  Cases_on `t` >> gvs[trace_prefix_def] >>
  PairCases_on `a` >> gvs[trace_prefix_def] >>
  every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem lprefix_chain_trace_prefix:
  lprefix_chain
    { fromList (a ++ io) | ∃n res. trace_prefix n (oracle,ffi) t = (io,res) }
Proof
  rw[lprefix_chain_def] >> simp[LPREFIX_fromList, from_toList] >>
  Cases_on `n ≤ n'` >> imp_res_tac trace_prefix_prefix >> gvs[]
QED

Theorem trace_prefix_Div[simp]:
  ∀n. trace_prefix n (oracle,ffi_st) Div = ([],NONE)
Proof
  Cases >> rw[trace_prefix_def]
QED

Theorem trace_prefix_SOME_mono:
  ∀m n oracle ffi_st t io res.
    trace_prefix n (oracle,ffi_st) t = (io, SOME res) ∧ n ≤ m
  ⇒ trace_prefix m (oracle,ffi_st) t = (io, SOME res)
Proof
  Induct >> rw[] >> gvs[trace_prefix_def] >>
  Cases_on `n` >> gvs[trace_prefix_def] >>
  Cases_on `t` >> gvs[trace_prefix_def] >>
  PairCases_on `a` >> gvs[trace_prefix_def] >> reverse CASE_TAC >> gvs[]
  >- (first_x_assum drule_all >> simp[]) >>
  CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem trace_prefix_NONE_mono:
  ∀m n oracle ffi_st t io res.
    trace_prefix m (oracle,ffi_st) t = (io, NONE) ∧ n ≤ m
  ⇒ ∃io'. isPREFIX io' io ∧ trace_prefix n (oracle,ffi_st) t = (io', NONE)
Proof
  Induct >> rw[] >> gvs[trace_prefix_def] >>
  Cases_on `n` >> gvs[trace_prefix_def] >>
  Cases_on `t` >> gvs[trace_prefix_def] >>
  PairCases_on `a` >> gvs[trace_prefix_def] >> CASE_TAC >> gvs[] >>
  CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  first_x_assum drule_all >> rw[]
QED


(***** lprefix_lub *****)

Theorem lprefix_lub_SING[simp]:
  lprefix_lub { a } l ⇔ l = a
Proof
  eq_tac >> rw[lprefix_lub_def] >>
  first_x_assum $ qspec_then `a` assume_tac >> gvs[LPREFIX_ANTISYM]
QED

Theorem lprefix_lub_LNIL[simp]:
  lprefix_lub {fromList io | io = [] : io_event list} l = (l = [| |]) ∧
  lprefix_lub ll [| |] = (∀l. l ∈ ll ⇒ l = [| |])
Proof
  rw[EXTENSION, lprefix_lub_def] >> eq_tac >> rw[] >>
  pop_assum $ qspec_then `[||]` mp_tac >> simp[]
QED

Theorem lprefix_lub_LCONS:
  lprefix_lub ls (h:::t) ⇒
  ∀l. l ∈ ls ⇒ LHD l = NONE ∨ LHD l = SOME h
Proof
  rw[lprefix_lub_def] >> Cases_on `l` >> gvs[] >>
  last_x_assum drule >> gvs[LPREFIX_LCONS]
QED

Theorem lprefix_lub_LTL:
  lprefix_lub ls (h:::t) ∧
  ltls = { ltl | ∃l. l ∈ ls ∧ LTL l = SOME ltl }
  ⇒ lprefix_lub ltls t
Proof
  rw[lprefix_lub_def] >> gvs[LPREFIX_LCONS, PULL_EXISTS]
  >- (first_x_assum drule >> rw[] >> gvs[]) >>
  qpat_x_assum `∀ub. (∀ll. _) ⇒ _` $ qspec_then `h:::ub` mp_tac >>
  simp[] >> disch_then irule >> rw[] >>
  last_x_assum drule >> rw[] >> gvs[LPREFIX_LCONS] >>
  last_x_assum irule >> goal_assum $ drule_at Any >> simp[]
QED


(***** smallStep FFI-state lemmas *****)

Theorem io_events_mono_step_n_cml:
  ∀env n dst1 dst2.
    step_n_cml env n (Dstep dst1) = Dstep dst2
  ⇒ io_events_mono (FST dst1).ffi (FST dst2).ffi
Proof
  strip_tac >> Induct >> rw[step_n_cml_alt_def] >>
  irule io_events_mono_trans >>
  last_x_assum $ irule_at Any >>
  qspecl_then [`env`,`SUC n`,`Dstep dst1`,`dst2`] mp_tac step_n_cml_eq_Dstep >>
  gvs[step_n_cml_alt_def] >>
  disch_then $ qspec_then `n` mp_tac >> gvs[] >> strip_tac >> gvs[] >>
  irule io_events_mono_decl_step >> simp[] >> goal_assum drule
QED

Theorem step_n_cml_preserved_FFI:
  ∀n e e' env.
    step_n_cml env n e = Dstep e' ∧ dget_ffi (Dstep e') = dget_ffi e
  ⇒ ∀m. m < n ⇒ dget_ffi (step_n_cml env m e) = dget_ffi (Dstep e')
Proof
  rw[] >> imp_res_tac LESS_STRONG_ADD >>
  gvs[step_n_cml_add |> ONCE_REWRITE_RULE[ADD_COMM]] >> rename1 `SUC n` >>
  Cases_on `step_n_cml env m e` >> gvs[] >>
  PairCases_on `p` >> rename1 `(dst1,dev1,dcs1)` >>
  Cases_on `e` >> gvs[] >>
  PairCases_on `p` >> rename1 `_ = dget_ffi $ _ (dst,dev,dcs)` >>
  PairCases_on `e'` >>
  rename1 `step_n_cml _ (SUC _) _ = Dstep (dst2,dev2,dcs2)` >>
  imp_res_tac io_events_mono_step_n_cml >> gvs[dget_ffi_def] >>
  imp_res_tac io_events_mono_antisym >> gvs[]
QED


(***** itree-based lemmas *****)

Theorem step_n_alt_def:
  step_n env 0 e = e ∧
  step_n env (SUC n) e = (
    case step_n env n e of
    | Dstep dst dev dcs => dstep env dst dev dcs
    | e => e)
Proof
  rw[step_n_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[step_n_def] >> simp[]
QED

Theorem step_n_add:
  ∀a b. step_n env (a + b) e = step_n env a (step_n env b e)
Proof
  Induct >> rw[step_n_def] >>
  simp[ADD_CLAUSES, step_n_alt_def]
QED

Theorem is_halt_step_n_eq:
  ∀n m env e.
    is_halt (step_n env n e) ∧
    is_halt (step_n env m e)
  ⇒ step_n env n e = step_n env m e
Proof
  rw[] >> wlog_tac `n < m` [`n`,`m`]
  >- (Cases_on `n = m` >> gvs[]) >>
  imp_res_tac LESS_STRONG_ADD >> gvs[] >>
  gvs[step_n_add |> ONCE_REWRITE_RULE[ADD_COMM]] >>
  Cases_on `step_n env n e` >> gvs[is_halt_def, step_n_def]
QED

Theorem application_thm:
  ∀op env s vs c.
    application op env s fp vs c =
    if getOpClass op = FunApp then
      case do_opapp vs of
      | NONE => Etype_error (fix_fp_state c fp)
      | SOME (env,e) => Estep (env,s,fp,Exp e,c)
    else if ∃n. op = FFI n then (
      case op of FFI n => (
        case vs of
          [Litv (StrLit conf); Loc b lnum] => (
            case store_lookup lnum s of
              SOME (W8array ws) =>
                if n = "" then Estep (env, s, fp, Val $ Conv NONE [], c)
                else Effi (ExtCall n)
                          (MAP (λc. n2w $ ORD c) (EXPLODE conf))
                          ws lnum env s c
            | _ => Etype_error (fix_fp_state c fp))
        | _ => Etype_error (fix_fp_state c fp))
      | _ => ARB)
    else (case getOpClass op of
    | Icing =>
      (case do_app s op vs of
         NONE => Etype_error (fix_fp_state c fp)
       | SOME (s',r) =>
        let fp_opt =
          (if fp.canOpt = FPScope Opt then
            case (do_fprw r (fp.opts 0) fp.rws) of
            (* if it fails, just use the old value tree *)
              NONE => r
            | SOME r_opt => r_opt
          else r)
        in
        let fpN = (if fp.canOpt = FPScope Opt then shift_fp_state fp else fp) in
        let fp_res =
          (if (isFpBool op)
          then (case fp_opt of
              Rval (FP_BoolTree fv) => Rval (Boolv (compress_bool fv))
            | v => v
            )
          else fp_opt)
        in
          (case fp_res of
              Rraise v => Estep (env,s', fpN, Exn v, c)
            | Rval v => return env s' fpN v c))
    | Reals =>
      if fp.real_sem then
      (case do_app s op vs of
         SOME (s', Rraise v) => Estep (env, s', fp, Exn v, c)
       | SOME (s', Rval v) => return env s' fp v c
       | NONE => Etype_error (fix_fp_state c fp))
      else Etype_error (fix_fp_state c (shift_fp_state fp))
    | Force =>
      (case vs of
         [Loc _ n] => (
           case store_lookup n s of
             SOME (Thunk F v) =>
               return env s fp v c
           | SOME (Thunk T f) =>
               application Opapp env s fp [f; Conv NONE []] ((Cforce n,env)::c)
           | _ =>
               Etype_error (fix_fp_state c fp))
       | _ => Etype_error (fix_fp_state c fp))
    | _ =>
      case do_app s op vs of
      | NONE => Etype_error (fix_fp_state c fp)
      | SOME (v1,Rval v') => return env v1 fp v' c
      | SOME (v1,Rraise v) => Estep (env,v1,fp,Exn v,c))
Proof
  cheat (* works in interactive, doesn't work with Holmake *)
  (*rpt strip_tac >> Cases_on ‘getOpClass op’ >> gs[] >>
  TOP_CASE_TAC >> gs[application_def]
  >- (
    Cases_on ‘op’ >> gs[application_def] >> every_case_tac >> gs[do_app_def] >>
    every_case_tac >> gs[]) >>
  Cases_on ‘op’ >> gs[application_def] >> every_case_tac >> gs[do_app_def] >>
  pop_assum $ mp_tac >>
  rpt (TOP_CASE_TAC >> gvs[SF itree_ss]) >> gs[store_alloc_def] >>
  rpt (FULL_CASE_TAC >> gvs[thunk_op_def, store_alloc_def, store_assign_def])*)
QED

Theorem application_FFI_results:
  (application (FFI s) env st fp vs cs = Etype_error (fix_fp_state cs fp)) ∨
  (application (FFI s) env st fp vs cs = Estep (env, st, fp, Val $ Conv NONE [], cs)) ∨
  ∃conf ws lnum.
    application (FFI s) env st fp vs cs =
    Effi (ExtCall s) conf ws lnum env st cs
Proof
  rw[application_thm] >> every_case_tac >> gvs[]
QED

Theorem application_eq_Effi_fields:
  application op env st fp vs cs = Effi (ExtCall s) conf ws lnum env' st' cs' ⇒
  op = FFI s ∧ env = env' ∧ st = st' ∧ cs' = cs ∧
  ∃conf' b.
    vs = [Litv $ StrLit conf'; Loc b lnum] ∧
    conf = MAP (λc. n2w $ ORD c) (EXPLODE conf')
Proof
  Cases_on `op` >> simp[application_def, SF itree_ss] >>
  every_case_tac >> gvs[] >> rw[]
QED

Theorem application_not_Edone:
  application op env st_ffi fp vs cs ≠ Edone
Proof
  rw[application_thm] >>
  every_case_tac >> gvs[SF itree_ss]
QED

Theorem estep_to_Edone:
  estep (env, st, fp, ev, cs) = Edone ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Exn v ∧ cs = [])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF itree_ss]) >>
  Cases_on `ev` >> gvs[estep_def]
  >- (
    Cases_on `e` >> gvs[estep_def, SF itree_ss] >>
    every_case_tac >> gvs[] >> rw[application_not_Edone]
    ) >>
  Cases_on `cs` >> gvs[SF itree_ss] >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[SF itree_ss] >>
  every_case_tac >> gvs[]
  >- (
    rename1 `Capp _ _ es` >>
    Cases_on `es` >> gvs[SF itree_ss, application_not_Edone]
    )
  >- (
    rename1 `Cmat l _` >> Cases_on `l` >> gvs[SF itree_ss] >>
    PairCases_on `h` >> gvs[SF itree_ss] >> every_case_tac >> gvs[]
    )
  >- (
    rename1 `Ccon _ _ es` >> Cases_on `es` >> gvs[SF itree_ss] >>
    every_case_tac >> gvs[]
    )
QED

Theorem dstep_to_Ddone:
  dstep env dst dev dcs = Ddone ⇔
    ∃e. dev = Env e ∧ dcs = []
Proof
  Cases_on `∃d. dev = Decl d` >> gvs[]
  >- (Cases_on `d` >> gvs[dstep_def] >> every_case_tac >> gvs[]) >>
  Cases_on `∃e. dev = Env e` >> gvs[]
  >- (
    Cases_on `dcs` >> gvs[SF ditree_ss] >>
    Cases_on `h` >> Cases_on `l` >> gvs[SF ditree_ss]
    ) >>
  Cases_on `dev` >> gvs[] >>
  Cases_on `e` >> gvs[dstep_def] >>
  Cases_on `l` >> gvs[dstep_def] >>
  gvs[AllCaseEqs(), estep_to_Edone]
QED

Theorem is_halt_step_n_const:
  ∀n env e. is_halt (step_n env n e) ⇒
    ∀m. n < m ⇒ step_n env n e = step_n env m e
Proof
  Induct >> rw[step_n_def]
  >- (Cases_on `e` >> gvs[is_halt_def]) >>
  Cases_on `e` >> gvs[step_n_def, is_halt_def] >>
  Cases_on `m` >> gvs[step_n_def]
QED

Theorem is_halt_step_n_min:
  ∀n env e. is_halt (step_n env n e) ⇒
  ∃m. m ≤ n ∧ step_n env m e = step_n env n e ∧
      ∀l. l < m ⇒ ¬is_halt (step_n env l e)
Proof
  Induct >> rw[step_n_alt_def] >>
  every_case_tac >> gvs[is_halt_def]
  >- (
    last_x_assum kall_tac >>
    qexists_tac `SUC n` >> simp[step_n_alt_def] >> rw[] >>
    CCONTR_TAC >> gvs[] >>
    Cases_on `l' = n` >> gvs[is_halt_def] >>
    drule is_halt_step_n_const >>
    disch_then $ qspec_then `n` assume_tac >> gvs[is_halt_def]
    ) >>
  last_x_assum $ qspecl_then [`env`,`e`] assume_tac >> gvs[is_halt_def] >>
  qexists_tac `m` >> simp[]
QED

Theorem step_until_halt_take_step:
  ∀dst dev dcs env. ¬ is_halt (Dstep dst dev dcs)
  ⇒ step_until_halt env (Dstep dst dev dcs) =
    step_until_halt env (dstep env dst dev dcs)
Proof
  rw[step_until_halt_def] >>
  DEEP_INTRO_TAC some_intro >> rw[] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    qspecl_then [`x`,`SUC x'`,`env`,`Dstep dst dev dcs`]
      assume_tac is_halt_step_n_eq >>
    gvs[step_n_def]
    )
  >- (Cases_on `x` >> gvs[step_n_def])
  >- (first_x_assum $ qspec_then `SUC x` assume_tac >> gvs[step_n_def])
QED

Theorem cml_itree_unfold_err:
  cml_itree_unfold_err f seed =
    case f seed of
    | Ret' r => Ret r
    | Div' => Div
    | Vis' (s, ws1, ws2) g =>
        Vis (s, ws1, ws2)
          (λa. case a of
                  INL x => Ret $ FinalFFI (s, ws1, ws2) x
                | INR y =>
                    if LENGTH ws2 = LENGTH y then cml_itree_unfold_err f (g y)
                    else Ret $ FinalFFI (s, ws1, ws2) FFI_failed)
Proof
  CASE_TAC >> gvs[cml_itree_unfold_err_def] >>
  simp[Once itree_unfold_err] >>
  PairCases_on `e` >> gvs[]
QED

Theorem interp:
  interp env e =
    case step_until_halt env e of
    | Ret => Ret Termination
    | Err => Ret Error
    | Div => Div
    | Act dst (s,ws1,ws2,n,env',cs) locs p dcs =>
        Vis (s, ws1, ws2)
          (λa. case a of
                | INL x => Ret $ FinalFFI (s, ws1, ws2) x
                | INR y =>
                    if LENGTH ws2 = LENGTH y then
                      interp env $
                        Dstep (dst with refs := LUPDATE (W8array y) n dst.refs)
                          (ExpVal env' (Val $ Conv NONE []) cs locs p) dcs
                    else Ret $ FinalFFI (s, ws1, ws2) FFI_failed)
Proof
  rw[interp_def] >> rw[Once cml_itree_unfold_err] >> simp[] >>
  CASE_TAC >> gvs[] >> rw[FUN_EQ_THM] >> PairCases_on `p` >> gvs[]
QED

Theorem trace_prefix_interp:
  trace_prefix 0 (oracle, ffi_st) (interp env e) = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (interp env e) =
    case step_until_halt env e of
    | Ret => ([], SOME Termination)
    | Err => ([], SOME Error)
    | Div => ([], NONE)
    | Act dst (s,conf,ws,lnum,env',cs) locs pat dcs =>
        case oracle s ffi_st conf ws of
        | Oracle_return ffi_st' ws' =>
            if LENGTH ws ≠ LENGTH ws' ∧ n = 0 then
              ([], NONE)
            else if LENGTH ws ≠ LENGTH ws' then
              ([], SOME $ FinalFFI (s, conf, ws) FFI_failed)
            else let (io, res) =
              trace_prefix n (oracle, ffi_st')
                (interp env $
                  Dstep (dst with refs := LUPDATE (W8array ws') lnum dst.refs)
                    (ExpVal env' (Val $ Conv NONE []) cs locs pat) dcs)
            in ((IO_event s conf (ZIP (ws,ws')))::io, res)
        | Oracle_final outcome =>
            if n = 0 then ([], NONE) else
            ([], SOME $ FinalFFI (s, conf, ws) outcome)
Proof
  rw[trace_prefix_def] >> rw[Once interp] >>
  CASE_TAC >> gvs[trace_prefix_def] >>
  PairCases_on `p` >> gvs[trace_prefix_def] >>
  reverse $ CASE_TAC >> gvs[]
  >- (Cases_on `n` >> gvs[trace_prefix_def]) >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `n` >> gvs[trace_prefix_def]
QED


(****************************************)

val _ = export_theory();
