(*
  Properties about BVI and its semantics
*)
open preamble bviSemTheory;
local open bvlPropsTheory in end;

val _ = new_theory"bviProps";

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

val pair_case_elim = prove(
  ``pair_CASE p f ⇔ ∃x y. p = (x,y) ∧ f x y``,
  Cases_on`p` \\ rw[]);

val elims = List.map prove_case_elim_thm [
  list_thms, option_thms, result_thms, ffi_result_thms ]
  |> cons pair_case_elim |> LIST_CONJ
  |> curry save_thm "case_elim_thms";
val case_elim_thms = elims;

val case_eq_thms =
  CONJ
  (prove_case_eq_thm {nchotomy = bviTheory.exp_nchotomy, case_def = bviTheory.exp_case_def})
  bvlPropsTheory.case_eq_thms
  |> curry save_thm "case_eq_thms";

val evaluate_LENGTH = Q.prove(
  `!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)`,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def,elims]
  \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[])
  |> SIMP_RULE std_ss [];

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

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

val inc_clock_def = Define `
  inc_clock n (s:('c,'ffi) bviSem$state) = s with clock := s.clock + n`;

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

val do_app_inv_clock = Q.prove(
  `case do_app op (REVERSE a) s of
    | Rerr e => (do_app op (REVERSE a) (inc_clock n s) = Rerr e)
    | Rval (v,s1) => (do_app op (REVERSE a) (inc_clock n s) = Rval (v,inc_clock n s1))`,
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
  \\ fs[bvlSemTheory.state_component_equality] \\ fs[] \\ rw[] \\ fs[]);

Theorem evaluate_inv_clock:
   !xs env t1 res t2 n.
      (evaluate (xs,env,t1) = (res,t2)) /\ res <> Rerr(Rabort Rtimeout_error) ==>
      (evaluate (xs,env,inc_clock n t1) = (res,inc_clock n t2))
Proof
  SIMP_TAC std_ss [] \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (`?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `res6` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [])
  \\ TRY (`?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
  THEN1 (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
  \\ TRY (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[]
    \\ `(inc_clock n s).clock <> 0` by (EVAL_TAC \\ DECIDE_TAC)
    \\ full_simp_tac(srw_ss())[dec_clock_inv_clock1] \\ NO_TAC)
  THEN1
   (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ MP_TAC (do_app_inv_clock |> Q.INST [`s`|->`s5`])
    \\ Cases_on `do_app op (REVERSE a) s5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `a'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [])
  THEN1
   (Cases_on `dest = NONE /\ IS_SOME handler` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `evaluate (xs,env,s1)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    \\ `(inc_clock n r).code = r.code` by SRW_TAC [] [inc_clock_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest a r.code` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC dec_clock_inv_clock
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ Cases_on `evaluate ([r'],q,dec_clock (ticks + 1) r)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY(Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ Cases_on`a'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
    \\ RES_TAC \\ TRY (full_simp_tac(srw_ss())[inc_clock_def] \\ decide_tac)
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
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
  \\ Cases_on`op=Install`
  >- (
    fs[do_app_def,do_install_def,case_eq_thms,bool_case_eq]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ rveq
    \\ fs[shift_seq_def]
    \\ qexists_tac`1+n` \\ rfs[GENLIST_APPEND,FOLDL_APPEND] )
  \\ imp_res_tac do_app_code \\ rfs[]
  \\ imp_res_tac do_app_oracle \\ rfs[]
  \\ qexists_tac`n` \\ fs[]
QED

Theorem evaluate_code_mono:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     subspt s1.code s2.code
Proof
  rw[] \\ imp_res_tac evaluate_code
  \\ rw[] \\ metis_tac[subspt_FOLDL_union]
QED

val evaluate_global_mono_lemma = Q.prove(
  `∀xs env s. IS_SOME s.global ⇒ IS_SOME((SND (evaluate (xs,env,s))).global)`,
  recInduct evaluate_ind \\ rw[evaluate_def,case_eq_thms,pair_case_eq]
  \\ every_case_tac \\ fs[] \\ rfs[] \\ fs[]
  \\ Cases_on `op = Install`
  \\ fs[do_app_def,case_eq_thms,pair_case_eq] \\ rw[bvl_to_bvi_def]
  \\ fs[do_app_aux_def,case_eq_thms] \\ rw[]
  \\ every_case_tac \\ fs [do_install_def,UNCURRY]
  \\ every_case_tac \\ fs [do_install_def]
  \\ rw [] \\ fs []);

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
  \\ fs[bvl_to_bvi_def,bvi_to_bvl_def,bvlSemTheory.do_app_def,case_eq_thms]
  \\ rw[] \\ fs[] \\ rw[] \\ fs[case_eq_thms,pair_case_eq] \\ rw[]
  \\ fs[SUBSET_DEF]
QED

Theorem do_app_with_code_err:
   bviSem$do_app op vs s = Rerr e ⇒
   (domain c ⊆ domain s.code ∨ e ≠ Rabort Rtype_error) ∧ op ≠ Install ⇒
   do_app op vs (s with code := c) = Rerr e
Proof
  rw [do_app_def,do_app_aux_def,case_eq_thms,pair_case_eq]
  \\ fs[bvl_to_bvi_def,bvi_to_bvl_def,bvlSemTheory.do_app_def,case_eq_thms]
  \\ rw[] \\ fs[] \\ rw[] \\ fs[case_eq_thms,pair_case_eq] \\ rw[]
  \\ fs[SUBSET_DEF] \\ strip_tac \\ res_tac
QED

(*
Theorem find_code_add_code:
   bvlSem$find_code dest a (fromAList code) = SOME x ⇒
   find_code dest a (fromAList (code ++ extra)) = SOME x
Proof
  Cases_on`dest`>>srw_tac[][bvlSemTheory.find_code_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[lookup_fromAList,ALOOKUP_APPEND] >> srw_tac[][]
QED

Theorem evaluate_add_code:
   ∀xs env s r s'.
    evaluate (xs,env,s) = (r,s') ∧ r ≠ Rerr (Rabort Rtype_error) ∧
    s.code = fromAList code
    ⇒
    evaluate (xs,env,s with code := fromAList (code ++ extra)) =
      (r,s' with code := fromAList (code ++ extra))
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY (
    rename1`Boolv T = HD _` >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    rpt(IF_CASES_TAC >> full_simp_tac(srw_ss())[]) >>
    TRY(qpat_x_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    (qpat_x_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[] ) >>
  TRY (
    rename1`bviSem$do_app` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >>
    imp_res_tac do_app_code >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    TRY (
      drule (GEN_ALL do_app_with_code) >>
      disch_then(qspec_then`fromAList (code ++ extra)`mp_tac) >>
      simp[domain_fromAList] >> NO_TAC) >>
    drule (GEN_ALL do_app_with_code_err) >>
    disch_then(qspec_then`fromAList (code++extra)`mp_tac) >>
    simp[] >> NO_TAC) >>
  TRY (
    rename1`bvlSem$find_code` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac find_code_add_code >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> NO_TAC) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
QED
*)

Theorem do_app_aux_with_clock:
   do_app_aux op vs (s with clock := c) =
   OPTION_MAP (OPTION_MAP (λ(x,y). (x,y with clock := c))) (do_app_aux op vs s)
Proof
  srw_tac[][do_app_aux_def] >>
  every_case_tac >> fs[]
QED

Theorem do_app_change_clock:
   (do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))
Proof
  rw[do_app_def,do_app_aux_with_clock,case_eq_thms,pair_case_eq,PULL_EXISTS]
  \\ imp_res_tac bvlPropsTheory.do_app_change_clock
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
  \\ fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs []
QED

Theorem evaluate_add_clock:
   !exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2) ∧
    res ≠ Rerr(Rabort Rtimeout_error)
    ⇒
    !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def]
  >- (Cases_on `evaluate ([x], env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      Cases_on `evaluate (y::xs,env,r)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      srw_tac[][inc_clock_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac do_app_const >>
      imp_res_tac do_app_change_clock >>
      imp_res_tac do_app_change_clock_err >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- (srw_tac[][] >>
      full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      srw_tac[][] >>
      `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
      metis_tac [])
  >- (Cases_on `evaluate (xs,env,s1)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      rev_full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      fsrw_tac[ARITH_ss][] >>
      `ck + r.clock - (ticks + 1) = r.clock - (ticks + 1) + ck` by srw_tac [ARITH_ss] [ADD1] >>
      full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`ck`mp_tac))>> srw_tac[][])
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
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono]
QED

val do_app_inc_clock = Q.prove(
  `do_app op vs (inc_clock x y) =
   map_result (λ(v,s). (v,s with clock := x + y.clock)) I (do_app op vs y)`,
  Cases_on`do_app op vs y` >>
  imp_res_tac do_app_change_clock_err >>
  TRY(Cases_on`a`>>imp_res_tac do_app_change_clock) >>
  full_simp_tac(srw_ss())[inc_clock_def] >> simp[])

val dec_clock_1_inc_clock = Q.prove(
  `x ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock (x-1) s`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_1_inc_clock2 = Q.prove(
  `s.clock ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock x (dec_clock 1 s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_inc_clock = Q.prove(
  `¬(s.clock < n) ⇒ dec_clock n (inc_clock x s) = inc_clock x (dec_clock n s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

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
  metis_tac[evaluate_io_events_mono,SND,IS_PREFIX_TRANS,PAIR,
            inc_clock_ffi,dec_clock_ffi]
QED

val take_drop_lem = Q.prove (
  `!skip env.
    skip < LENGTH env ∧
    skip + SUC n ≤ LENGTH env ∧
    DROP skip env ≠ [] ⇒
    EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)`,
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
  srw_tac [ARITH_ss] []);

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

val get_code_labels_def = tDefine"get_code_labels"
  `(get_code_labels (Var _) = {}) ∧
   (get_code_labels (If e1 e2 e3) = get_code_labels e1 ∪ get_code_labels e2 ∪ get_code_labels e3) ∧
   (get_code_labels (Let es e) = BIGUNION (set (MAP get_code_labels es)) ∪ get_code_labels e) ∧
   (get_code_labels (Raise e) = get_code_labels e) ∧
   (get_code_labels (Tick e) = get_code_labels e) ∧
   (get_code_labels (Call _ d es h) =
     (case d of NONE => {} | SOME n => {n}) ∪
     (case h of NONE => {} | SOME e => get_code_labels e) ∪
     BIGUNION (set (MAP get_code_labels es))) ∧
   (get_code_labels (Op op es) = closLang$assign_get_code_label op ∪ BIGUNION (set (MAP get_code_labels es)))`
  (wf_rel_tac`measure exp_size`
   \\ simp[bviTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw[bviTheory.exp_size_def]
   \\ simp[] \\ res_tac \\ simp[]);
val get_code_labels_def = get_code_labels_def |> SIMP_RULE (srw_ss()++ETA_ss)[] |> curry save_thm "get_code_labels_def[simp,compute]"

val good_code_labels_def = Define`
  good_code_labels p ⇔
    BIGUNION (set (MAP (get_code_labels o SND o SND) p)) ⊆ set (MAP FST p)`;

val _ = export_theory();
