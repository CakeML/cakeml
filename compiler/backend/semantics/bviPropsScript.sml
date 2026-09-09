(*
  Properties about BVI and its semantics
*)
Theory bviProps
Ancestors
  bviSem bvlProps[qualified] backendProps
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Theorem initial_state_simp[simp]:
   (initial_state f c co cc k).code = c ∧
   (initial_state f c co cc k).ffi = f ∧
   (initial_state f c co cc k).clock = k ∧
   (initial_state f c co cc k).compile = cc ∧
   (initial_state f c co cc k).compile_oracle = co ∧
   (initial_state f c co cc k).refs = FEMPTY ∧
   (initial_state f c co cc k).global = NONE
Proof
   srw_tac[][initial_state_def]
QED

Theorem initial_state_with_simp[simp]:
   initial_state f c co cc k with clock := k1 = initial_state f c co cc k1 ∧
   initial_state f c co cc k with code := c1 = initial_state f c1 co cc k
Proof
  EVAL_TAC
QED

Theorem bvl_to_bvi_id:
   bvl_to_bvi (bvi_to_bvl s) s = s
Proof
  EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
QED

Theorem bvl_to_bvi_with_refs:
   bvl_to_bvi (x with refs := y) z = bvl_to_bvi x z with <| refs := y |>
Proof
  EVAL_TAC
QED

Theorem bvl_to_bvi_with_clock:
   bvl_to_bvi (x with clock := y) z = bvl_to_bvi x z with <| clock := y |>
Proof
  EVAL_TAC
QED

Theorem bvl_to_bvi_with_ffi:
   bvl_to_bvi (x with ffi := y) z = bvl_to_bvi x z with ffi := y
Proof
  EVAL_TAC
QED

Theorem bvl_to_bvi_code[simp]:
   (bvl_to_bvi x y).code = y.code
Proof
  EVAL_TAC
QED

Theorem bvl_to_bvi_clock[simp]:
   (bvl_to_bvi x y).clock = x.clock
Proof
  EVAL_TAC
QED

Theorem bvi_to_bvl_refs[simp]:
   (bvi_to_bvl x).refs = x.refs
Proof
EVAL_TAC
QED

Theorem bvi_to_bvl_code[simp]:
   (bvi_to_bvl x).code = map (K ARB) x.code
Proof
EVAL_TAC
QED

Theorem bvi_to_bvl_clock[simp]:
   (bvi_to_bvl x).clock = x.clock
Proof
EVAL_TAC
QED

Theorem bvi_to_bvl_ffi[simp]:
   (bvi_to_bvl x).ffi = x.ffi
Proof
EVAL_TAC
QED

Theorem bvi_to_bvl_to_bvi_with_ffi:
   bvl_to_bvi (bvi_to_bvl x with ffi := f) x = x with ffi := f
Proof
  EVAL_TAC \\ rw[state_component_equality]
QED

Theorem domain_bvi_to_bvl_code[simp]:
   domain (bvi_to_bvl s).code = domain s.code
Proof
  srw_tac[][bvi_to_bvl_def,domain_map]
QED

val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def };
val result_thms = { nchotomy = semanticPrimitivesTheory.result_nchotomy,
                    case_def = semanticPrimitivesTheory.result_case_def };
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy,
                        case_def = ffiTheory.ffi_result_case_def };

Theorem pair_case_elim[local]:
    pair_CASE p f ⇔ ∃x y. p = (x,y) ∧ f x y
Proof
  Cases_on`p` \\ rw[]
QED

Theorem case_elim_thms =
  List.map prove_case_elim_thm
           [list_thms, option_thms, result_thms, ffi_result_thms]
    |> cons pair_case_elim |> LIST_CONJ

Theorem case_eq_thms =
  LIST_CONJ
  [TypeBase.case_eq_of ``:bvi$exp``,
   TypeBase.case_eq_of ``:bviSem$exn_or_ret``,
   bvlPropsTheory.case_eq_thms]

val evaluate_LENGTH = Q.prove(
  `!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)`,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def,case_elim_thms]
  \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ first_x_assum drule \\ rw [])
  |> SIMP_RULE std_ss [];

Theorem evaluate_LENGTH =
  evaluate_LENGTH

Theorem evaluate_IMP_LENGTH:
   (evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SING_IMP:
   (evaluate ([x],env,s1) = (Rval vs,s2)) ==> ?w. vs = [w]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
QED

Theorem evaluate_CONS:
   evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t
Proof
  Cases_on `xs` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SNOC:
   !xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ full_simp_tac(srw_ss())[LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_APPEND:
   !xs env s ys.
      evaluate (xs ++ ys,env,s) =
      case evaluate (xs,env,s) of
        (Rval vs,s2) =>
          (case evaluate (ys,env,s2) of
             (Rval ws,s1) => (Rval (vs ++ ws),s1)
           | res => res)
      | res => res
Proof
  Induct \\ full_simp_tac(srw_ss())[APPEND,evaluate_def] \\ REPEAT STRIP_TAC
  >- every_case_tac
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
QED

Definition inc_clock_def:
  inc_clock n (s:('c,'ffi) bviSem$state) = s with clock := s.clock + n
End

Theorem inc_clock_ZERO:
   !s. inc_clock 0 s = s
Proof
  full_simp_tac(srw_ss())[inc_clock_def,state_component_equality]
QED

Theorem inc_clock_ADD:
   inc_clock n (inc_clock m s) = inc_clock (n+m) s
Proof
  full_simp_tac(srw_ss())[inc_clock_def,state_component_equality,AC ADD_ASSOC ADD_COMM]
QED

Theorem inc_clock_refs[simp]:
   (inc_clock n s).refs = s.refs
Proof
EVAL_TAC
QED

Theorem inc_clock_code[simp]:
   (inc_clock n s).code = s.code
Proof
EVAL_TAC
QED

Theorem inc_clock_global[simp]:
   (inc_clock n s).global = s.global
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock_ffi[simp]:
   (inc_clock n s).ffi = s.ffi
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock_clock[simp]:
   (inc_clock n s).clock = s.clock + n
Proof
  srw_tac[][inc_clock_def]
QED

Theorem dec_clock_global[simp]:
   (dec_clock n s).global = s.global
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_ffi[simp]:
   (dec_clock n s).ffi = s.ffi
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_refs[simp]:
   (dec_clock n s).refs = s.refs
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_with_code[simp]:
   bviSem$dec_clock n (s with code := c) = dec_clock n s with code := c
Proof
  EVAL_TAC
QED

Theorem dec_clock_code[simp]:
   (dec_clock n s).code = s.code
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_inv_clock:
   ¬(t1.clock < ticks + 1) ==>
    (dec_clock (ticks + 1) (inc_clock c t1) = inc_clock c (dec_clock (ticks + 1) t1))
Proof
  full_simp_tac(srw_ss())[dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC
QED

Theorem dec_clock_inv_clock1:
   t1.clock <> 0 ==>
    (dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1))
Proof
  full_simp_tac(srw_ss())[dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC
QED

Theorem dec_clock0[simp]:
   !n (s:('c,'ffi) bviSem$state). dec_clock 0 s = s
Proof
  simp [dec_clock_def, state_component_equality]
QED

Theorem do_app_inv_clock[local]:
  case do_app op (REVERSE a) s of
    | Rerr e => (do_app op (REVERSE a) (inc_clock n s) = Rerr e)
    | Rval (v,s1) => (do_app op (REVERSE a) (inc_clock n s) = Rval (v,inc_clock n s1))
Proof
  Cases_on `op = Install` THEN1
   (Q.SPEC_TAC(`REVERSE a`,`a`) \\ gen_tac \\ CASE_TAC
    \\ fs [do_app_def,do_install_def,UNCURRY,inc_clock_def] \\ rfs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs [])
  \\ Q.SPEC_TAC(`REVERSE a`,`a`) \\ gen_tac \\ CASE_TAC
  \\ fs[bviSemTheory.do_app_def,case_eq_thms,pair_case_eq,
        inc_clock_def,bvl_to_bvi_def,bvi_to_bvl_def] \\ rw[] \\ rfs []
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[do_app_aux_def,case_eq_thms]
  \\ imp_res_tac bvlPropsTheory.do_app_change_clock
  \\ imp_res_tac bvlPropsTheory.do_app_change_clock_err
  \\ rfs [] \\ fs[state_component_equality] \\ fs[] \\ rw[] \\ fs[]
  \\ fs[bvlSemTheory.state_component_equality] \\ fs[] \\ rw[] \\ fs[]
QED

Theorem do_app_inc_clock_IMP[local]:
  (do_app op vs s = Rval (v,s1) ==>
     do_app op vs (inc_clock n s) = Rval (v,inc_clock n s1)) /\
  (do_app op vs s = Rerr e ==> do_app op vs (inc_clock n s) = Rerr e)
Proof
  rw[] \\ mp_tac (do_app_inv_clock |> Q.INST [`a`|->`REVERSE vs`]) \\ fs[]
QED

Theorem evaluate_inv_clock:
   !xs env t1 res t2 n.
      (evaluate (xs,env,t1) = (res,t2)) /\ res <> Rerr(Rabort Rtimeout_error) ==>
      (evaluate (xs,env,inc_clock n t1) = (res,inc_clock n t2))
Proof
  SIMP_TAC std_ss [] \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ gvs[AllCaseEqs(), dec_clock_inv_clock, dec_clock_inv_clock1]
  \\ rpt (first_x_assum (fn th => mp_tac th \\ impl_tac >- fs[] \\ strip_tac))
  \\ gvs[AllCaseEqs(), dec_clock_inv_clock, dec_clock_inv_clock1]
  \\ imp_res_tac do_app_inc_clock_IMP \\ gvs[]
QED

Theorem do_app_code:
   !op s1 s2. (do_app op a s1 = Rval (x0,s2)) /\ op <> Install ==> (s2.code = s1.code)
Proof
  rw[do_app_def,case_eq_thms,pair_case_eq,bvl_to_bvi_def] \\ rw[] \\
  fs[do_app_aux_def,case_eq_thms] \\ rw[]
QED

Theorem do_app_oracle:
   !op s1 s2. (do_app op a s1 = Rval (x0,s2)) /\ op <> Install ==>
    (s2.compile_oracle = s1.compile_oracle) /\
    (s2.compile = s1.compile)
Proof
  rw[do_app_def,case_eq_thms,pair_case_eq,bvl_to_bvi_def] \\ rw[] \\
  fs[do_app_aux_def,case_eq_thms] \\ rw[]
QED

Theorem GENLIST_add_split[local]:
  !f a b. GENLIST f a ++ GENLIST (\i. f (a + i)) b = GENLIST f (a + b)
Proof
  Induct_on `b` \\ rw[GENLIST, ADD_CLAUSES, SNOC_APPEND]
  \\ simp[GENLIST_APPEND]
QED

Theorem FOLDL_union_GENLIST_split[local]:
  FOLDL union (FOLDL union c (MAP (fromAList o SND) (GENLIST f a)))
              (MAP (fromAList o SND) (GENLIST (\i. f (i + a)) b)) =
  FOLDL union c (MAP (fromAList o SND) (GENLIST f (a + b)))
Proof
  `(\i. f (i + a)) = (\i. f (a + i))` by simp[FUN_EQ_THM, ADD_COMM]
  \\ pop_assum (fn th => rewrite_tac[th])
  \\ rewrite_tac[GSYM GENLIST_add_split, MAP_APPEND, FOLDL_APPEND]
QED

Theorem evaluate_code:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     ∃n.
       s2.compile_oracle = shift_seq n s1.compile_oracle ∧
       s2.code = FOLDL union s1.code (MAP (fromAList o SND)
         (GENLIST s1.compile_oracle n))
Proof
  recInduct evaluate_ind \\ rw [evaluate_def]
  \\ fs[case_eq_thms,pair_case_eq,bool_case_eq,bvlPropsTheory.case_eq_thms]
  \\ rveq \\ fs[shift_seq_def,dec_clock_def] \\ rfs[]
  \\ TRY (qexists_tac`0` \\ srw_tac[ETA_ss][] \\ NO_TAC)
  \\ TRY (qexists_tac`n` \\ srw_tac[ETA_ss][] \\ NO_TAC)
  \\ TRY ( qpat_x_assum`(_,_) = _`(assume_tac o SYM) \\ fs[] )
  \\ TRY(
       qmatch_goalsub_rename_tac`a1 + a2`
    \\ qexists_tac`a1+a2`
    \\ simp[GENLIST_APPEND,FOLDL_APPEND] \\ NO_TAC)
  \\ TRY(
       qmatch_goalsub_rename_tac`a1 + a2`
    \\ qexists_tac`a2+a1`
    \\ simp[GENLIST_APPEND,FOLDL_APPEND] \\ NO_TAC)
  \\ TRY(
       qmatch_goalsub_rename_tac`a1 + (a2 + a3)`
    \\ qexists_tac`a3+a2+a1`
    \\ simp[GENLIST_APPEND,FOLDL_APPEND] \\ NO_TAC)
  >- (
    Cases_on`op=Install`
    >- (
      fs[do_app_def,do_install_def,case_eq_thms,bool_case_eq]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ rveq
      \\ fs[shift_seq_def]
      \\ qexists_tac`1+n` \\ rfs[GENLIST_APPEND,FOLDL_APPEND] )
    \\ imp_res_tac do_app_code \\ rfs[]
    \\ imp_res_tac do_app_oracle \\ rfs[]
    \\ qexists_tac`n` \\ fs[])
  >- (
    gvs [AllCaseEqs()]
    >>~- ([‘s.clock ≠ 0’], qexists ‘n'’ \\ gvs [])
    \\ qexists `0` \\ gvs [FUN_EQ_THM])
  (* Call (exception handler) and LetCall (multi-return body) continuation arms:
     split the exn_or_ret result, apply the continuation IH, compose oracle shifts *)
  \\ gvs[AllCaseEqs()]
  \\ rpt (first_x_assum (dxrule_then strip_assume_tac))
  \\ gvs[shift_seq_def]
  \\ qmatch_goalsub_abbrev_tac `(λi. s1.compile_oracle (i + summ)) = _`
  \\ qexists_tac `summ`
  \\ simp[Abbr`summ`,FOLDL_union_GENLIST_split]
QED

Theorem evaluate_code_mono:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     subspt s1.code s2.code
Proof
  rw[] \\ imp_res_tac evaluate_code
  \\ rw[] \\ metis_tac[subspt_FOLDL_union]
QED

Theorem evaluate_global_mono_lemma[local]:
  ∀xs env s. IS_SOME s.global ⇒ IS_SOME((SND (evaluate (xs,env,s))).global)
Proof
  recInduct evaluate_ind \\ rw[evaluate_def,case_eq_thms,pair_case_eq]
  \\ every_case_tac \\ fs[] \\ rfs[] \\ fs[]
  \\ Cases_on `op = Install`
  \\ fs[do_app_def,case_eq_thms,pair_case_eq] \\ rw[bvl_to_bvi_def]
  \\ fs[do_app_aux_def,case_eq_thms] \\ rw[]
  \\ every_case_tac \\ fs [do_install_def,UNCURRY]
  \\ every_case_tac \\ fs [do_install_def]
  \\ rw [] \\ fs []
QED

Theorem evaluate_global_mono:
   ∀xs env s res t. (evaluate (xs,env,s) = (res,t)) ⇒ IS_SOME s.global ⇒ IS_SOME t.global
Proof
  METIS_TAC[SND,evaluate_global_mono_lemma]
QED

Theorem do_app_err:
   do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw[bviSemTheory.do_app_def,case_eq_thms,pair_case_eq] >>
  imp_res_tac bvlPropsTheory.do_app_err >>
  fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs []
QED

Theorem do_app_aux_const:
   do_app_aux op vs s = SOME (SOME (y,z)) ⇒
   z.clock = s.clock
Proof
  rw[do_app_aux_def,case_eq_thms] >> rw[]
QED

Theorem do_app_with_code:
   bviSem$do_app op vs s = Rval (r,s') ⇒
   domain s.code ⊆ domain c ∧ op ≠ Install ⇒
   do_app op vs (s with code := c) = Rval (r,s' with code := c)
Proof
  rw [do_app_def,do_app_aux_def,case_eq_thms,pair_case_eq]
  >~ [`ThunkOp`] >- gvs[bvlSemTheory.do_app_def, AllCaseEqs(), bvl_to_bvi_def]
  \\ fs[bvl_to_bvi_def,bvi_to_bvl_def,bvlSemTheory.do_app_def,case_eq_thms]
  \\ TRY (pairarg_tac \\ fs [])
  \\ rw[] \\ fs[] \\ rw[] \\ fs[case_eq_thms,pair_case_eq] \\ rw[]
  \\ fs[SUBSET_DEF,EVERY_MEM] \\ rw [] \\ fs []
QED

Theorem do_app_with_code_err:
   bviSem$do_app op vs s = Rerr e ⇒
   (domain c ⊆ domain s.code ∨ e ≠ Rabort Rtype_error) ∧ op ≠ Install ⇒
   do_app op vs (s with code := c) = Rerr e
Proof
  rw [do_app_def,do_app_aux_def,case_eq_thms,pair_case_eq]
  >>~- ([`ThunkOp`], gvs [bvlSemTheory.do_app_def, AllCaseEqs()])
  \\ fs[bvl_to_bvi_def,bvi_to_bvl_def,bvlSemTheory.do_app_def,case_eq_thms]
  \\ TRY (pairarg_tac \\ fs [])
  \\ rw[] \\ fs[] \\ rw[] \\ fs[case_eq_thms,pair_case_eq] \\ rw[]
  \\ fs[SUBSET_DEF] \\ TRY (strip_tac \\ res_tac)
  \\ fs [EXISTS_MEM] \\ metis_tac []
QED

Theorem do_app_aux_with_clock:
   do_app_aux op vs (s with clock := c) =
   OPTION_MAP (OPTION_MAP (λ(x,y). (x,y with clock := c))) (do_app_aux op vs s)
Proof
  Cases_on ‘do_app_aux op vs (s with clock := c)’ \\ fs []
  \\ gvs [do_app_aux_def,AllCaseEqs()]
QED

Theorem do_app_change_clock:
   (do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))
Proof
  rw[do_app_def,do_app_aux_with_clock,case_eq_thms,pair_case_eq,PULL_EXISTS]
  \\ imp_res_tac bvlPropsTheory.do_app_change_clock
  \\ TRY (pairarg_tac \\ fs [])
  \\ fs[bvi_to_bvl_def,bvl_to_bvi_def]
  \\ fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs []
QED

Theorem do_app_change_clock_err:
   bviSem$do_app op vs s = Rerr e ⇒
   do_app op vs (s with clock := c) = Rerr e
Proof
  rw[do_app_def,do_app_aux_with_clock,case_eq_thms,pair_case_eq,PULL_EXISTS]
  \\ imp_res_tac bvlPropsTheory.do_app_change_clock_err
  \\ fs[bvi_to_bvl_def,bvl_to_bvi_def]
  \\ TRY (pairarg_tac \\ fs [])
  \\ fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs []
  \\ fs [state_component_equality]
QED

Theorem evaluate_add_clock:
   !exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2) ∧
    res ≠ Rerr(Rabort Rtimeout_error)
    ⇒
    !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)
Proof
  metis_tac[evaluate_inv_clock]
QED

Theorem do_app_aux_io_events_mono:
   do_app_aux op vs s = SOME (SOME (x,y)) ⇒
   s.ffi.io_events ≼ y.ffi.io_events
Proof
  rw[do_app_aux_def,case_eq_thms] \\ rw[]
QED

Theorem do_app_io_events_mono:
   do_app op vs s1 = Rval (x,s2) ⇒
   s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  rw[do_app_def,case_eq_thms,pair_case_eq]
  \\ fs[bvl_to_bvi_def,bvi_to_bvl_def]
  \\ imp_res_tac bvlPropsTheory.do_app_io_events_mono \\ fs[]
  \\ imp_res_tac do_app_aux_io_events_mono \\ fs[]
  \\ fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs []
  \\ rw [] \\ fs []
QED

Theorem evaluate_io_events_mono:
   !exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  gvs [AllCaseEqs()] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono]
QED

Theorem do_app_inc_clock[local]:
  do_app op vs (inc_clock x y) =
   map_result (λ(v,s). (v,s with clock := x + y.clock)) I (do_app op vs y)
Proof
  Cases_on`do_app op vs y` >>
  imp_res_tac do_app_change_clock_err >>
  TRY(Cases_on`a`>>imp_res_tac do_app_change_clock) >>
  full_simp_tac(srw_ss())[inc_clock_def] >> simp[]
QED

Theorem dec_clock_1_inc_clock[local]:
  x ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock (x-1) s
Proof
  simp[state_component_equality,inc_clock_def,dec_clock_def]
QED

Theorem dec_clock_1_inc_clock2[local]:
  s.clock ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock x (dec_clock 1 s)
Proof
  simp[state_component_equality,inc_clock_def,dec_clock_def]
QED

Theorem dec_clock_inc_clock[local]:
  ¬(s.clock < n) ⇒ dec_clock n (inc_clock x s) = inc_clock x (dec_clock n s)
Proof
  simp[state_component_equality,inc_clock_def,dec_clock_def]
QED

Theorem inc_clock_eq_0[simp]:
   (inc_clock extra s).clock = 0 ⇔ s.clock = 0 ∧ extra = 0
Proof
  srw_tac[][inc_clock_def]
QED

Theorem evaluate_add_to_clock_io_events_mono:
   ∀exps env s extra.
    (SND(evaluate(exps,env,s))).ffi.io_events ≼
    (SND(evaluate(exps,env,inc_clock extra s))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    ntac 4 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    ntac 2 (TRY (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[])) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    TRY(qpat_x_assum`Boolv _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[])) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_1_inc_clock,dec_clock_1_inc_clock2] >>
  imp_res_tac evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(qpat_x_assum`Boolv _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[]) >>
  rev_full_simp_tac(srw_ss())[do_app_inc_clock] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_io_events_mono >>
  TRY(fsrw_tac[ARITH_ss][] >>NO_TAC) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[dec_clock_inc_clock,inc_clock_ZERO] >>
  fsrw_tac[ARITH_ss][dec_clock_inc_clock,inc_clock_ZERO] >>
  full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  (* the bvi Call/LetCall handler now post-processes its result (rejecting an
     escaping Ret); every_case_tac splits that inner case on both clock sides,
     so specialise the add_clock facts at extra to unify them before closing *)
  rpt (qpat_x_assum ‘∀ck. evaluate _ = _’ (assume_tac o Q.SPEC ‘extra’)) >>
  gvs[inc_clock_ffi] >>
  metis_tac[evaluate_io_events_mono,SND,IS_PREFIX_TRANS,PAIR,
            inc_clock_ffi,dec_clock_ffi]
QED

Theorem take_drop_lem[local]:
  !skip env.
    skip < LENGTH env ∧
    skip + SUC n ≤ LENGTH env ∧
    DROP skip env ≠ [] ⇒
    EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)
Proof
  Induct_on `n` >>
  srw_tac[][TAKE1, HD_DROP] >>
  `skip + SUC n ≤ LENGTH env` by decide_tac >>
  res_tac >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by srw_tac[][LENGTH_DROP] >>
  `SUC n < LENGTH (DROP skip env)` by decide_tac >>
  `LENGTH (DROP (1 + skip) env) = LENGTH env - (1 + skip)` by srw_tac[][LENGTH_DROP] >>
  `n < LENGTH (DROP (1 + skip) env)` by decide_tac >>
  srw_tac[][TAKE_EL_SNOC, ADD1] >>
  `n + (1 + skip) < LENGTH env` by decide_tac >>
  `(n+1) + skip < LENGTH env` by decide_tac >>
  srw_tac[][EL_DROP] >>
  srw_tac [ARITH_ss] []
QED

Theorem evaluate_genlist_vars:
   !skip env n (st:('c,'ffi) bviSem$state).
    n + skip ≤ LENGTH env ⇒
    evaluate (GENLIST (λarg. Var (arg + skip)) n, env, st)
    =
    (Rval (TAKE n (DROP skip env)), st)
Proof
  Induct_on `n` >>
  srw_tac[][evaluate_def, DROP_LENGTH_NIL, GSYM ADD1] >>
  srw_tac[][Once GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  first_x_assum (qspecl_then [`skip + 1`, `env`] mp_tac) >>
  srw_tac[][] >>
  `n + (skip + 1) ≤ LENGTH env` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][combinTheory.o_DEF, ADD1, GSYM ADD_ASSOC] >>
  `skip + 1 = 1 + skip ` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by srw_tac[][LENGTH_DROP] >>
  `n < LENGTH env - skip` by decide_tac >>
  `DROP skip env ≠ []`
        by (Cases_on `DROP skip env` >>
            full_simp_tac(srw_ss())[] >>
            decide_tac) >>
  metis_tac [take_drop_lem]
QED

Definition get_code_labels_def:
  (get_code_labels (Var _) = {}) ∧
  (get_code_labels (If e1 e2 e3) = get_code_labels e1 ∪ get_code_labels e2 ∪ get_code_labels e3) ∧
  (get_code_labels (Let es e) = BIGUNION (set (MAP get_code_labels es)) ∪ get_code_labels e) ∧
  (get_code_labels (Raise e) = get_code_labels e) ∧
  (get_code_labels (Tick e) = get_code_labels e) ∧
  (get_code_labels (Force loc v) = {loc}) ∧
  (get_code_labels (Call _ d es h) =
    (case d of NONE => {} | SOME n => {n}) ∪
    (case h of NONE => {} | SOME e => get_code_labels e) ∪
    BIGUNION (set (MAP get_code_labels es))) ∧
  (get_code_labels (Op op es) = closLang$assign_get_code_label op ∪ BIGUNION (set (MAP get_code_labels es))) ∧
  (get_code_labels (Return es) = BIGUNION (set (MAP get_code_labels es))) ∧
  (get_code_labels (LetCall _ _ d es y) =
    {d} ∪ get_code_labels y ∪ BIGUNION (set (MAP get_code_labels es)))
Termination
  wf_rel_tac`measure exp_size`
  \\ simp[bviTheory.exp_size_def]
  \\ rpt conj_tac \\ rpt gen_tac
  \\ Induct_on`es`
  \\ rw[bviTheory.exp_size_def]
  \\ simp[] \\ res_tac \\ simp[]
End

Theorem get_code_labels_def[simp,compute,allow_rebind] =
  get_code_labels_def |> SIMP_RULE (srw_ss()++ETA_ss)[]

Definition good_code_labels_def:
  good_code_labels p elabs ⇔
    BIGUNION (set (MAP (get_code_labels o SND o SND) p)) ⊆ set (MAP FST p) ∪ elabs
End

(* --- switching a compiler pass off --------------------------------------

   A pass that is configured off compiles with CURRY I, i.e. the identity.
   It still wraps the incremental compiler with state_cc/state_co, which
   moves one configuration component between the oracle's state and its
   config.  adj_orac below performs that move on a state; it is the BVI
   analogue of closProps' adj_orac_rel.                                    *)

Definition adj_orac_def:
  adj_orac cc f (s:('a,'ffi) bviSem$state) : ('b,'ffi) bviSem$state =
    <| refs := s.refs; clock := s.clock; global := s.global;
       code := s.code; ffi := s.ffi; compile := cc;
       compile_oracle := (f ## I) o s.compile_oracle |>
End

Definition adj_orac_ok_def:
  adj_orac_ok cc f (s:('a,'ffi) bviSem$state) ⇔
    ∀n x y. s.compile_oracle n = (x,y) ⇒
      OPTION_MAP (I ## (I ## f)) (s.compile x y) = cc (f x) y
End

Theorem adj_orac_simps[local]:
  (adj_orac cc f s).clock = s.clock ∧
  (adj_orac cc f s).code = s.code ∧
  (adj_orac cc f s).refs = s.refs ∧
  (adj_orac cc f s).global = s.global ∧
  (adj_orac cc f s).ffi = s.ffi ∧
  dec_clock n (adj_orac cc f s) = adj_orac cc f (dec_clock n s) ∧
  ((adj_orac cc f s) with clock := k) = adj_orac cc f (s with clock := k) ∧
  (adj_orac_ok cc f (dec_clock n s) ⇔ adj_orac_ok cc f s) ∧
  (adj_orac_ok cc f (s with clock := k) ⇔ adj_orac_ok cc f s)
Proof
  rw [adj_orac_def, adj_orac_ok_def, dec_clock_def, state_component_equality]
QED

Definition adj_orac_rel_def:
  adj_orac_rel cc f (s1:('a,'ffi) bviSem$state) (s2:('b,'ffi) bviSem$state) ⇔
    adj_orac_ok cc f s1 ∧ s2 = adj_orac cc f s1
End

Theorem do_app_cfg_swap[local]:
  op ≠ Install ⇒
    ((do_app op args s = Rval (value,s1) ∧
      domain s.code ⊆ domain t.code ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rval
        (value,
         t with <| refs := s1.refs; clock := s1.clock;
                   global := s1.global; ffi := s1.ffi |>)) ∧
     (do_app op args s = Rerr error ∧
      (domain t.code ⊆ domain s.code ∨
       error ≠ Rabort Rtype_error) ⇒
      do_app op args
        (t with <| refs := s.refs; clock := s.clock;
                   global := s.global; ffi := s.ffi |>) =
      Rerr error))
Proof
  strip_tac
  \\ Cases_on `op`
  \\ gvs [do_app_def, bviSemTheory.do_app_aux_def, bvi_to_bvl_def,
          bvl_to_bvi_def, bvlSemTheory.do_app_def, AllCaseEqs(),
          state_component_equality, SUBSET_DEF, pairTheory.ELIM_UNCURRY]
  \\ rpt strip_tac
  \\ gvs []
  >- metis_tac []
  \\ qmatch_asmsub_rename_tac
       `s.refs |+ (global_ptr,
                   ValueArray (LUPDATE new_value set_index global_values)) =
        s1.refs`
  \\ qexists_tac
       `SOME (Unit,
              t with
                <| refs := s.refs |+ (global_ptr,
                     ValueArray (LUPDATE new_value set_index global_values));
                   clock := s1.clock; global := s1.global; ffi := s1.ffi |>)`
  \\ conj_tac
  >- (qexists_tac `global_ptr` \\ gvs [])
  \\ disj2_tac
  \\ gvs []
QED

Theorem do_app_cfg_swap_Rval[local]:
  ∀op args (s:('a,'ffi) bviSem$state) (s1:('a,'ffi) bviSem$state)
      (t:('b,'ffi) bviSem$state) value.
    op ≠ Install ∧ domain s.code = domain t.code ∧
    do_app op args s = Rval (value,s1) ⇒
    do_app op args
      (t with <| refs := s.refs; clock := s.clock;
                 global := s.global; ffi := s.ffi |>) =
    Rval (value, t with <| refs := s1.refs; clock := s1.clock;
                           global := s1.global; ffi := s1.ffi |>)
Proof
  metis_tac [do_app_cfg_swap, SUBSET_REFL]
QED

Theorem do_app_cfg_swap_Rerr[local]:
  ∀op args (s:('a,'ffi) bviSem$state) (t:('b,'ffi) bviSem$state) error.
    op ≠ Install ∧ domain s.code = domain t.code ∧
    do_app op args s = Rerr error ⇒
    do_app op args
      (t with <| refs := s.refs; clock := s.clock;
                 global := s.global; ffi := s.ffi |>) = Rerr error
Proof
  metis_tac [do_app_cfg_swap, SUBSET_REFL]
QED

Theorem do_install_Rerr_type[local]:
  do_install args s = Rerr e ⇒ e = Rabort Rtype_error
Proof
  rw [do_install_def] \\ gvs [AllCaseEqs(), UNCURRY]
QED

Theorem do_install_adj_orac[local]:
  ∀args (s:('a,'ffi) bviSem$state) v t cc (f:'a -> 'b).
    adj_orac_ok cc f s ∧
    (do_install args s :
       (bvlSem$v # ('a,'ffi) bviSem$state, bviSem$exn_or_ret) result) =
      Rval (v,t) ⇒
    (do_install args (adj_orac cc f s) :
       (bvlSem$v # ('b,'ffi) bviSem$state, bviSem$exn_or_ret) result) =
      Rval (v, adj_orac cc f t) ∧
    adj_orac_ok cc f t
Proof
  rpt gen_tac
  \\ rw [do_install_def]
  \\ gvs [AllCaseEqs(), UNCURRY]
  \\ `∃cfg progs. s.compile_oracle 0 = (cfg,progs)` by metis_tac [PAIR]
  \\ gvs [adj_orac_def, adj_orac_ok_def, shift_seq_def, o_DEF]
  \\ first_assum drule
  \\ gvs []
  \\ strip_tac
  \\ gvs [AllCaseEqs(), FUN_EQ_THM, state_component_equality]
  \\ metis_tac []
QED

Theorem do_app_adj_orac[local]:
  adj_orac_ok cc f s ⇒
    (∀v t. do_app op args s = Rval (v,t) ⇒
       do_app op args (adj_orac cc f s) = Rval (v, adj_orac cc f t) ∧
       adj_orac_ok cc f t) ∧
    (∀e. do_app op args s = Rerr e ∧ e ≠ Rabort Rtype_error ⇒
       do_app op args (adj_orac cc f s) = Rerr e)
Proof
  strip_tac
  \\ reverse (Cases_on `op = Install`)
  >-
   (`(adj_orac cc f s) with <| refs := s.refs; clock := s.clock;
        global := s.global; ffi := s.ffi |> = adj_orac cc f s`
       by gvs [adj_orac_def, state_component_equality]
    \\ `domain s.code = domain (adj_orac cc f s).code` by gvs [adj_orac_def]
    \\ conj_tac \\ rpt gen_tac \\ strip_tac
    >-
     (drule_all do_app_cfg_swap_Rval
      \\ gvs []
      \\ strip_tac
      \\ imp_res_tac do_app_code
      \\ imp_res_tac do_app_oracle
      \\ gvs [adj_orac_def, adj_orac_ok_def, state_component_equality]
      \\ metis_tac [])
    \\ drule_all do_app_cfg_swap_Rerr
    \\ gvs [])
  \\ gvs [do_app_def]
  \\ conj_tac \\ rpt gen_tac \\ strip_tac
  >- (drule_all do_install_adj_orac \\ simp [])
  \\ imp_res_tac do_install_Rerr_type \\ gvs []
QED

Theorem evaluate_adj_orac_rel[local]:
  ∀xs env (s:('a,'ffi) bviSem$state).
    ∀res t1 cc f (s2:('b,'ffi) bviSem$state).
      evaluate (xs,env,s) = (res,t1) ∧
      res ≠ Rerr (Rabort Rtype_error) ∧
      adj_orac_rel cc f s s2 ⇒
      ∃t2. evaluate (xs,env,s2) = (res,t2) ∧ adj_orac_rel cc f t1 t2
Proof
  recInduct evaluate_ind
  \\ rw [evaluate_def]
  \\ gvs [AllCaseEqs()]
  \\ gvs [adj_orac_rel_def, adj_orac_simps]
  \\ res_tac \\ gvs [adj_orac_simps]
  (* only the Op case is left; there the compiler oracle can be touched *)
  \\ first_x_assum (qspecl_then [`cc`,`f`] strip_assume_tac) \\ gvs []
  \\ drule_all do_app_adj_orac \\ strip_tac \\ res_tac \\ gvs []
QED

Theorem evaluate_adj_orac:
  evaluate (xs,env,(s:('a,'ffi) bviSem$state)) = (res,t1) ∧
  res ≠ Rerr (Rabort Rtype_error) ∧
  adj_orac_ok cc (f:'a -> 'b) s ⇒
  evaluate (xs,env,adj_orac cc f s) = (res, adj_orac cc f t1) ∧
  adj_orac_ok cc f t1
Proof
  strip_tac
  \\ `∃t2. evaluate (xs,env,adj_orac cc f s) = (res,t2) ∧
            adj_orac_rel cc f t1 t2` by
       (irule evaluate_adj_orac_rel \\ gvs [adj_orac_rel_def] \\ metis_tac [])
  \\ gvs [adj_orac_rel_def]
QED

Theorem adj_orac_initial_state[local]:
  adj_orac cc SND (initial_state ffi code co (state_cc (CURRY I) cc) k) =
  initial_state ffi code (state_co (CURRY I) co) cc k
Proof
  rw [adj_orac_def, initial_state_def, state_component_equality,
      state_co_def, FUN_EQ_THM]
  \\ Cases_on `co x` \\ Cases_on `q` \\ gvs []
QED

Theorem adj_orac_ok_initial_state[local]:
  adj_orac_ok cc SND (initial_state ffi code co (state_cc (CURRY I) cc) k)
Proof
  rw [adj_orac_ok_def, initial_state_def, state_cc_def]
  \\ PairCases_on `x` \\ gvs []
  \\ CASE_TAC \\ gvs []
  \\ PairCases_on `x` \\ gvs []
QED

Theorem evaluate_CURRY_I[local]:
  evaluate (es,env,initial_state ffi code co (state_cc (CURRY I) cc) k) = (r,s) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃s2.
    evaluate (es,env,initial_state ffi code (state_co (CURRY I) co) cc k) =
      (r,s2) ∧ s2.ffi = s.ffi
Proof
  strip_tac
  \\ `adj_orac_ok cc SND (initial_state ffi code co (state_cc (CURRY I) cc) k)`
        by simp [adj_orac_ok_initial_state]
  \\ drule_all evaluate_adj_orac
  \\ strip_tac
  \\ gvs [adj_orac_initial_state, adj_orac_simps]
QED

Theorem semantics_CURRY_I:
  semantics ffi code co (state_cc (CURRY I) cc) start ≠ ffi$Fail ⇒
  semantics ffi code co (state_cc (CURRY I) cc) start =
  semantics ffi code (state_co (CURRY I) co) cc start
Proof
  strip_tac
  \\ simp [Ntimes semantics_def 2]
  \\ IF_CASES_TAC \\ fs []
  >- (qpat_x_assum `_ ≠ Fail` mp_tac \\ simp [semantics_def] \\ metis_tac [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ IF_CASES_TAC \\ fs []
    >-
     (qpat_x_assum `_ = (r,s)` kall_tac
      \\ first_assum (qspec_then `k'` mp_tac)
      \\ disch_then (subterm (fn tm => Cases_on `^(assert(has_pair_type)tm)`) o concl)
      \\ drule (GEN_ALL evaluate_CURRY_I)
      \\ first_x_assum (qspec_then `k'` strip_assume_tac)
      \\ rfs [] \\ CCONTR_TAC \\ fs [] \\ rfs [] \\ fs [] \\ rfs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qmatch_assum_abbrev_tac `evaluate (opts,[],sopt) = _`
      \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = (r,s)`
      \\ qspecl_then [`opts`,`[]`,`sopt`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps`,`[]`,`st`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ simp [inc_clock_def, Abbr`sopt`, Abbr`st`]
      \\ ntac 2 strip_tac
      \\ qpat_x_assum `evaluate _ = (r',s')` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k` mp_tac)
      \\ impl_tac >- (rpt (PURE_FULL_CASE_TAC \\ fs []))
      \\ qpat_x_assum `evaluate _ = (r,s)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k'` mp_tac)
      \\ impl_tac >- (rpt (PURE_FULL_CASE_TAC \\ fs []))
      \\ simp [inc_clock_def] \\ ntac 2 strip_tac
      \\ drule (GEN_ALL evaluate_CURRY_I)
      \\ impl_tac >- (rpt (PURE_FULL_CASE_TAC \\ fs []))
      \\ strip_tac
      \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
      \\ gvs [])
    \\ drule (GEN_ALL evaluate_CURRY_I)
    \\ impl_tac
    >-
     (spose_not_then assume_tac
      \\ rpt (last_x_assum (qspec_then `k` mp_tac)) \\ fs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs [])
  \\ strip_tac \\ IF_CASES_TAC \\ fs []
  >-
   (Cases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
                        initial_state ffi code co (state_cc (CURRY I) cc) k)`
    \\ drule (GEN_ALL evaluate_CURRY_I)
    \\ impl_tac
    >- (qpat_x_assum `∀k e. FST (evaluate (_,_,initial_state _ _ co _ _)) ≠ _ ∨ _`
          (qspecl_then [`k`,`Rabort Rtype_error`] mp_tac) \\ fs [])
    \\ strip_tac \\ gvs []
    \\ qpat_x_assum `∀k e. FST _ ≠ _ ∨ _` (qspecl_then [`k`,`e`] mp_tac) \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (spose_not_then assume_tac \\ rw []
    \\ Cases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
                           initial_state ffi code co (state_cc (CURRY I) cc) k)`
    \\ drule (GEN_ALL evaluate_CURRY_I)
    \\ impl_tac
    >- (qpat_x_assum `∀k e. FST (evaluate (_,_,initial_state _ _ co _ _)) ≠ _ ∨ _`
          (qspecl_then [`k`,`Rabort Rtype_error`] mp_tac) \\ fs [])
    \\ strip_tac \\ gvs []
    \\ metis_tac [])
  \\ strip_tac
  \\ qmatch_abbrev_tac `lprefix_lub$build_lprefix_lub l1 =
                        lprefix_lub$build_lprefix_lub l2`
  \\ `(lprefix_lub$lprefix_chain l1 ∧ lprefix_lub$lprefix_chain l2) ∧
      lprefix_lub$equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm, lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
   (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [LESS_EQ_EXISTS, initial_state_with_simp,
                  evaluate_add_to_clock_io_events_mono
                    |> CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s"]))
                    |> Q.SPEC `s with clock := k`
                    |> SIMP_RULE (srw_ss()) [inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ ntac 2 (pop_assum kall_tac)
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac \\ rveq
  \\ Cases_on `evaluate ([Call 0 (SOME start) [] NONE],[],
                         initial_state ffi code co (state_cc (CURRY I) cc) k)`
  \\ drule (GEN_ALL evaluate_CURRY_I)
  \\ impl_tac
  >- (qpat_x_assum `∀k e. FST (evaluate (_,_,initial_state _ _ co _ _)) ≠ _ ∨ _`
        (qspecl_then [`k`,`Rabort Rtype_error`] mp_tac) \\ fs [])
  \\ strip_tac
  \\ conj_tac \\ rw []
  \\ qexists_tac `k` \\ fs []
QED
