(*
  Correctness proof for flat_to_pat
*)
open preamble
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     flatLangTheory flat_to_patTheory backendPropsTheory
     patLangTheory patPropsTheory

val _ = new_theory"flat_to_patProof"

val _ = temp_bring_to_front_overload"pure_op"{Name="pure_op",Thy="flat_to_pat"};
val _ = temp_bring_to_front_overload"Loc"{Name="Loc",Thy="patSem"};

val _ = set_grammar_ancestry ["misc","ffi","bag","flatProps","patProps",
                              "flat_to_pat","backendProps","backend_common"];
val _ = Parse.hide"U";

val pmatch_flat_def = flatSemTheory.pmatch_def

val NoRun_def = tDefine "NoRun" `
  (NoRun (Raise t e)      <=> NoRun e) /\
  (NoRun (Handle t e1 e2) <=> NoRun e1 /\ NoRun e2) /\
  (NoRun (Con t n es)     <=> EVERY NoRun es) /\
  (NoRun (Fun t e)        <=> NoRun e) /\
  (NoRun (App t op es)    <=> op <> Run /\ EVERY NoRun es) /\
  (NoRun (If t e1 e2 e3)  <=> NoRun e1 /\ NoRun e2 /\ NoRun e3) /\
  (NoRun (Let t e1 e2)    <=> NoRun e1 /\ NoRun e2) /\
  (NoRun (Seq t e1 e2)    <=> NoRun e1 /\ NoRun e2) /\
  (NoRun (Letrec t es e)  <=> EVERY NoRun es /\ NoRun e) /\
  (NoRun expr             <=> T)`
  (WF_REL_TAC `measure exp_size` \\ rw []
   \\ imp_res_tac exp_size_MEM \\ fs [])

Theorem sLet_NoRun:
   !e1 e2.
     NoRun e1 /\ NoRun e2
     ==>
     !t. NoRun (sLet t e1 e2)
Proof
  recInduct (theorem"NoRun_ind") \\ rw [NoRun_def]
  \\ simp [sLet_def]
  \\ every_case_tac \\ fs [NoRun_def]
QED

Theorem sIf_NoRun:
   !e1 e2 e3.
     NoRun e1 /\ NoRun e2 /\ NoRun e3
     ==>
     !t. NoRun (sIf t e1 e2 e3)
Proof
  recInduct (theorem"NoRun_ind") \\ rw [NoRun_def]
  \\ simp [sIf_def]
  \\ every_case_tac \\ fs [NoRun_def]
QED

Theorem compile_row_NoRun:
   (!t bvs p ns n f e.
      NoRun e /\
      compile_row t bvs p = (ns, n, f)
      ==>
      NoRun (f e)) /\
   (!t bvs n1 n2 ps ns n f e.
      NoRun e /\
      compile_cols t bvs n1 n2 ps = (ns, n, f)
      ==>
      NoRun (f e))
Proof
   ho_match_mp_tac compile_row_ind \\ rw [compile_row_def] \\ fs []
   \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
   \\ irule sLet_NoRun \\ fs [NoRun_def]
QED

Theorem Let_Els_NoRun:
   !t n m e. NoRun e ==> NoRun (Let_Els t n m e)
Proof
  recInduct Let_Els_ind \\ rw [NoRun_def] \\ fs [Let_Els_def]
  \\ irule sLet_NoRun \\ fs [NoRun_def]
QED

Theorem compile_pat_NoRun:
   (!t p. NoRun (compile_pat t p)) /\
   (!t n ps. NoRun (compile_pats t n ps))
Proof
  ho_match_mp_tac compile_pat_ind \\ rw [compile_pat_def] \\ fs [NoRun_def]
  \\ TRY (irule sIf_NoRun) \\ fs [NoRun_def]
  \\ TRY (irule sLet_NoRun) \\ fs [NoRun_def]
  \\ TRY (irule Let_Els_NoRun) \\ fs []
QED

Theorem compile_exp_NoRun:
   (!bvs x. NoRun (compile_exp bvs x)) /\
   (!bvs xs. EVERY NoRun (compile_exps bvs xs)) /\
   (!bvs xs. EVERY NoRun (compile_funs bvs xs)) /\
   (!tr bvs xs. NoRun (compile_pes tr bvs xs))
Proof
  ho_match_mp_tac compile_exp_ind \\ rw [NoRun_def] \\ fs [ETA_AX]
  \\ rpt CASE_TAC \\ fs [NoRun_def]
  \\ TRY (metis_tac [sLet_NoRun, compile_row_NoRun])
  \\ metis_tac [compile_row_NoRun, sIf_NoRun, compile_pat_NoRun]
QED

Theorem compile_NoRun:
   ∀decs. EVERY NoRun (compile decs)
Proof
  Induct \\ simp[compile_def]
  \\ Cases \\ rw[compile_def, compile_exp_NoRun]
QED

val v_size_MEM = Q.prove (
  `!vs (v: patSem$v). MEM v vs ==> v_size v < v1_size vs`,
  Induct \\ rw [patSemTheory.v_size_def]
  \\ res_tac \\ fs []);

(* Closure and Recclosure are tricky when used with v_rel *)
val NoRun_v_def = tDefine "NoRun_v" `
  (NoRun_v (Conv _ vs)          <=> EVERY NoRun_v vs) /\
  (NoRun_v (Closure vs e)       <=> NoRun e /\ EVERY NoRun_v vs) /\
  (NoRun_v (Recclosure vs es _) <=> EVERY NoRun_v vs /\ EVERY NoRun es) /\
  (NoRun_v (Vectorv vs)         <=> EVERY NoRun_v vs) /\
  (NoRun_v v                    <=> T)`
  (WF_REL_TAC `measure v_size` \\ rw []
  \\ imp_res_tac v_size_MEM \\ fs []);

val NoRun_store_v_def = Define `
  (NoRun_store_v (Refv v)    <=> NoRun_v v) /\
  (NoRun_store_v (Varray vs) <=> EVERY NoRun_v vs) /\
  (NoRun_store_v _           <=> T)`

val NoRun_state_def = Define `
  NoRun_state st <=>
    EVERY NoRun_store_v st.refs /\
    EVERY (\g. !x. g = SOME x ==> NoRun_v x) st.globals`

Theorem NoRun_state_dec_clock:
   NoRun_state s <=> NoRun_state (dec_clock s)
Proof
  rw [NoRun_state_def, patSemTheory.dec_clock_def]
QED

Theorem build_rec_env_NoRun:
   !funs cl_env.
     EVERY NoRun_v cl_env /\
     EVERY NoRun funs
     ==>
     EVERY NoRun_v (build_rec_env funs cl_env)
Proof
   gen_tac
   \\ Induct_on `LENGTH funs` \\ rw []
   >- simp [patSemTheory.build_rec_env_def]
   \\ Cases_on `funs` \\ fs []
   \\ first_x_assum (qspec_then `t` mp_tac) \\ fs []
   \\ disch_then drule
   \\ simp [patSemTheory.build_rec_env_def, EVERY_GENLIST]
   \\ rw [] \\ fs [NoRun_v_def, ETA_AX]
QED

Theorem do_opapp_NoRun:
   EVERY NoRun_v vs /\
   do_opapp vs = SOME (env, e)
   ==>
   EVERY NoRun_v env /\
   NoRun e
Proof
   simp [patSemTheory.do_opapp_def]
   \\ rpt (PURE_CASE_TAC \\ fs [NoRun_v_def])
   \\ rw [] \\ fs [ETA_AX, build_rec_env_NoRun, EVERY_EL]
QED

Theorem store_assign_NoRun:
   !n r x t.
     NoRun_v x /\
     EVERY NoRun_store_v r /\
     store_assign n (Refv x) r = SOME t
     ==>
     EVERY NoRun_store_v t
Proof
  Induct \\ rw [store_assign_def]
  \\ Cases_on `r` \\ fs [LUPDATE_def, NoRun_store_v_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp [store_assign_def]
QED

Theorem v_to_list_NoRun:
   !x xs.
     NoRun_v x /\
     v_to_list x = SOME xs
     ==>
     EVERY NoRun_v xs
Proof
  recInduct patSemTheory.v_to_list_ind \\ rw []
  \\ fs [patSemTheory.v_to_list_def] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs []
  \\ rw [] \\ fs [NoRun_v_def]
QED

Theorem NoRun_list_to_v:
   !xs.
     EVERY NoRun_v xs
     ==>
     NoRun_v (list_to_v xs)
Proof
   Induct \\ rw [patSemTheory.list_to_v_def, NoRun_v_def]
QED

Theorem do_app_NoRun:
   do_app s op vs = SOME (t, res) /\
   EVERY NoRun_v vs /\
   op <> Run /\
   NoRun_state s
   ==>
   NoRun_state t /\
   case res of
     Rval v => NoRun_v v
   | Rerr (Rraise e) => NoRun_v e
   | _ => T
Proof
  simp [patSemTheory.do_app_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ rw [] \\ fs [patSemTheory.prim_exn_def, NoRun_v_def, patSemTheory.Boolv_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ TRY (imp_res_tac store_assign_NoRun \\ fs [NoRun_state_def] \\ NO_TAC)
  \\ fs [store_alloc_def, store_lookup_def, store_assign_def, NoRun_state_def] \\ rveq
  \\ fs [NoRun_store_v_def, NoRun_v_def]
  \\ TRY (fs [EVERY_EL] \\ metis_tac [NoRun_store_v_def])
  \\ TRY
   (irule IMP_EVERY_LUPDATE \\ fs [NoRun_store_v_def]
    \\ fs [EVERY_EL]
    \\ `NoRun_store_v (Varray l)` by (res_tac \\ fs [EQ_SYM_EQ])
    \\ fs [NoRun_store_v_def]
    \\ rw [] \\ fs []
    \\ fs [EL_LUPDATE]
    \\ rw [] \\ fs [EVERY_EL]
    \\ NO_TAC)
  \\ imp_res_tac v_to_list_NoRun \\ fs [ETA_AX]
  \\ fs [EVERY_REPLICATE]
  \\ TRY (fs [EVERY_EL, IS_SOME_EXISTS] \\ res_tac \\ NO_TAC)
  \\ TRY
   (fs [EVERY_EL, NoRun_store_v_def]
    \\ `NoRun_store_v (Varray l)` by (res_tac \\ fs [EQ_SYM_EQ])
    \\ fs [NoRun_store_v_def, EVERY_EL]
    \\ NO_TAC)
  \\ irule NoRun_list_to_v \\ fs []
QED

Theorem do_if_NoRun:
   do_if v x y = SOME z /\
   NoRun_v v /\ NoRun x /\ NoRun y ==> NoRun z
Proof
  rw [patSemTheory.do_if_def] \\ fs []
QED

Theorem evaluate_NoRun:
   !env s es t res.
     evaluate env s es = (t, res) /\
     EVERY NoRun es /\
     EVERY NoRun_v env /\
     NoRun_state s
     ==>
     NoRun_state t /\
     case res of
       Rval vs => EVERY NoRun_v vs
     | Rerr (Rraise e) => NoRun_v e
     | _ => T
Proof
  recInduct patSemTheory.evaluate_ind
  \\ rpt conj_tac
  >- (rw [patSemTheory.evaluate_def] \\ fs [patSemTheory.do_opapp_def])
  >-
   (rw [] \\ qhdtm_x_assum `evaluate` mp_tac \\ once_rewrite_tac [evaluate_cons]
    \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw [] \\ fs [])
  >- (rw [patSemTheory.evaluate_def] \\ fs [NoRun_v_def])
  \\ rw [] \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [patSemTheory.evaluate_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw [] \\ fs []
  \\ fs [NoRun_def]
  \\ imp_res_tac evaluate_sing \\ fs []
  \\ TRY
   (fs [ETA_AX, EVERY_REVERSE, NoRun_v_def, EVERY_EL]
    \\ fs [NoRun_state_def, EVERY_EL, IS_SOME_EXISTS]
    \\ res_tac \\ fs []
    \\ NO_TAC)
  \\ TRY (* do_if *) (drule (GEN_ALL do_if_NoRun) \\ rw [])
  \\ TRY (* do_app *)
   (imp_res_tac do_opapp_NoRun \\ fs []
    \\ fs [ETA_AX, EVERY_REVERSE, NoRun_v_def]
    \\ every_case_tac \\ fs []
    \\ TRY (imp_res_tac NoRun_state_dec_clock \\ fs [] \\ NO_TAC)
    \\ drule (GEN_ALL do_app_NoRun) \\ fs [EVERY_REVERSE])
  \\ every_case_tac \\ fs [ETA_AX]
  \\ imp_res_tac build_rec_env_NoRun \\ fs []
  \\ fs [NoRun_state_def, EVERY_GENLIST, NoRun_v_def]
QED

(* value translation *)

val compile_tag_def = Define`
  compile_tag (SOME (tag,_)) = tag ∧
  compile_tag NONE = backend_common$tuple_tag`;
val _ = export_rewrites["compile_tag_def"];

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv l) = Litv l) ∧
  (compile_v (Conv tag vs) = Conv (compile_tag tag) (compile_vs vs)) ∧
  (compile_v (Closure env x e) =
    Closure
      (MAP compile_v (MAP SND env))
      (compile_exp (SOME x :: MAP (SOME o FST) env) e)) ∧
  (compile_v (Recclosure env funs f) =
    Recclosure
      (MAP compile_v (MAP SND env))
      (compile_funs (MAP (SOME o FST) funs ++ MAP (SOME o FST) env) funs)
      (the (LENGTH funs) (find_index f (MAP FST funs) 0))) ∧
  (compile_v (Loc n) = Loc n) ∧
  (compile_v (Vectorv vs) = Vectorv (compile_vs vs)) ∧
  (compile_vs [] = []) ∧
  (compile_vs (v::vs) = compile_v v :: compile_vs vs)`
(WF_REL_TAC`inv_image $< (\x. case x of INL v => v_size v
                                      | INR vs => v3_size vs)` >>
 simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[] >>
 Cases >> simp[flatSemTheory.v_size_def] >> srw_tac[][] >> res_tac >> simp[])
val compile_v_def = save_thm("compile_v_def[compute]",
  compile_v_def |> SIMP_RULE (srw_ss()++ETA_ss) [MAP_MAP_o])
val _ = export_rewrites["compile_v_def"]

Theorem compile_vs_map:
   ∀vs. compile_vs vs = MAP compile_v vs
Proof
  Induct >> simp[]
QED
val _ = export_rewrites["compile_vs_map"]

Theorem map_result_compile_vs_list_result[simp]:
   map_result compile_vs f (list_result r) = list_result (map_result compile_v f r)
Proof
  Cases_on`r`>>simp[]
QED

Theorem compile_v_NoRun_v:
   (!v. NoRun_v (compile_v v)) /\
   (!vs. EVERY NoRun_v (compile_vs vs))
Proof
  ho_match_mp_tac (theorem"compile_v_ind") \\ rw []
  \\ rw [NoRun_v_def] \\ fs [ETA_AX, compile_exp_NoRun]
  \\ rw [EVERY_MEM] \\ fs [MEM_MAP] \\ rw []
  \\ res_tac \\ fs []
QED

val compile_state_def = Define`
  compile_state co cc (s:'ffi flatSem$state) :('c,'ffi) patSem$state =
    <| clock := s.clock;
       refs := MAP (map_sv compile_v) s.refs;
       ffi := s.ffi;
       globals := MAP (OPTION_MAP compile_v) s.globals;
       compile := cc;
       compile_oracle := pure_co compile o co (* s.compile_oracle *)
     |>`;

val compile_state_dec_clock = Q.prove(
  `compile_state co cc (dec_clock s) = dec_clock (compile_state co cc s)`,
  EVAL_TAC)

val compile_state_with_clock = Q.prove(
  `compile_state co cc (s with clock := k) = compile_state co cc s with clock := k`,
  EVAL_TAC)

Theorem compile_state_NoRun:
   NoRun_state (compile_state co cc s)
Proof
  rw [compile_state_def, NoRun_state_def, EVERY_MEM]
  \\ fs [MEM_MAP] \\ rw [] \\ fs [compile_v_NoRun_v]
  \\ Cases_on `y` \\ fs [NoRun_store_v_def, compile_v_NoRun_v, EVERY_MAP,
                         EVERY_MEM, compile_v_NoRun_v]
QED

(* semantic functions obey translation *)

val do_eq = Q.prove(
  `(∀v1 v2. do_eq v1 v2 ≠ Eq_type_error ⇒ do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2)) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 ≠ Eq_type_error ⇒ do_eq_list vs1 vs2 = do_eq_list (compile_vs vs1) (compile_vs vs2))`,
  ho_match_mp_tac flatSemTheory.do_eq_ind >>
  simp[flatSemTheory.do_eq_def,patSemTheory.do_eq_def] >>
  srw_tac[][] >>
  TRY (BasicProvers.CASE_TAC >> srw_tac[][])
  \\ fs[] \\ rfs[]
  \\ TRY (qpat_x_assum`Eq_val _ = X`(assume_tac o SYM) \\ fs[])
  \\ Cases_on`cn1` \\ Cases_on`cn2`
  \\ TRY (Cases_on`x`) \\ TRY (Cases_on`x'`)
  \\ fs[flatSemTheory.ctor_same_type_def]);

val do_opapp = Q.prove(
  `∀vs env exp.
    do_opapp vs = SOME (env,exp) ⇒
    do_opapp (compile_vs vs) =
      SOME (MAP (compile_v o SND) env, compile_exp (MAP (SOME o FST) env) exp)`,
  rpt gen_tac >> simp[flatSemTheory.do_opapp_def] >>
  BasicProvers.CASE_TAC >>
  Cases_on`t`>>simp[]>>
  Cases_on`t'`>>simp[]>>
  Cases_on`h`>>simp[patSemTheory.do_opapp_def]>>
  TRY(srw_tac[][] >> srw_tac[][]>>NO_TAC) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  full_simp_tac(srw_ss())[find_recfun_ALOOKUP,compile_funs_map,patSemTheory.build_rec_env_def,flatPropsTheory.build_rec_env_merge,FST_triple] >>
  imp_res_tac ALOOKUP_find_index_SOME >>
  simp[EL_MAP,UNCURRY,LIST_EQ_REWRITE,compile_funs_map,libTheory.the_def] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  `∃x y z. EL i l0 = (x,y,z)` by metis_tac[PAIR]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac find_index_ALL_DISTINCT_EL >>
  full_simp_tac(srw_ss())[EL_MAP,libTheory.the_def])

val v_to_list = Q.prove (
  `!v1 v2 vs1.
    compile_v v1 = v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      compile_vs vs1 = vs2`,
  ho_match_mp_tac flatSemTheory.v_to_list_ind >>
  srw_tac[][flatSemTheory.v_to_list_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[compile_v_def, patSemTheory.v_to_list_def] >>
  srw_tac[][]);

val v_to_char_list = Q.prove (
  `!v1 v2 vs1.
    compile_v v1 = v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ho_match_mp_tac flatSemTheory.v_to_char_list_ind >>
  srw_tac[][flatSemTheory.v_to_char_list_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[compile_v_def, patSemTheory.v_to_char_list_def]);

val vs_to_string = Q.prove(
  `∀v. vs_to_string (MAP compile_v v) = vs_to_string v`,
  ho_match_mp_tac flatSemTheory.vs_to_string_ind
  \\ rw[flatSemTheory.vs_to_string_def,patSemTheory.vs_to_string_def]);

Theorem list_to_v_compile:
   !x xs.
   v_to_list x = SOME xs /\
   v_to_list (compile_v x) = SOME (MAP compile_v xs) ==>
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs)
Proof
  ho_match_mp_tac flatSemTheory.v_to_list_ind
  \\ rw [flatSemTheory.v_to_list_def] \\ fs []
  \\ fs [patSemTheory.list_to_v_def, flatSemTheory.list_to_v_def]
  \\ PURE_FULL_CASE_TAC \\ fs [] \\ rveq
  \\ fs [patSemTheory.list_to_v_def, flatSemTheory.list_to_v_def,
         patSemTheory.v_to_list_def, flatSemTheory.v_to_list_def]
  \\ PURE_FULL_CASE_TAC \\ fs [] \\ rveq
QED

Theorem list_to_v_compile_APPEND:
   !xs ys.
     list_to_v (MAP compile_v xs) = compile_v (list_to_v xs) /\
     list_to_v (MAP compile_v ys) = compile_v (list_to_v ys) ==>
       list_to_v (MAP compile_v (xs ++ ys)) =
       compile_v (list_to_v (xs ++ ys))
Proof
  Induct \\ rw [patSemTheory.list_to_v_def]
  \\ fs [flatSemTheory.list_to_v_def, patSemTheory.list_to_v_def]
QED

val do_app = Q.prove(
  `∀cc co op vs s0 s res.
     do_app b s0 op vs = SOME (s,res)
     ⇒
     do_app (compile_state co cc s0) (Op op) (compile_vs vs) =
       SOME (compile_state co cc s,map_result compile_v compile_v res)`,
  srw_tac[][compile_state_def] >>
  fs[flatSemTheory.do_app_cases] >> rw[] >>
  rw[patSemTheory.do_app_def,
     patSemTheory.prim_exn_def,
     flatSemTheory.div_exn_v_def,
     flatSemTheory.subscript_exn_v_def,
     flatSemTheory.chr_exn_v_def,
     patSemTheory.Boolv_def, flatSemTheory.Boolv_def,
     GSYM do_eq ] >>
  rfs [store_assign_def, store_lookup_def, store_alloc_def, LET_THM, EL_MAP, LUPDATE_MAP] >>
  rveq >>
  rfs [store_v_same_type_def, LUPDATE_MAP,map_replicate] >>
  imp_res_tac v_to_list >>
  imp_res_tac v_to_char_list >>
  fs[vs_to_string, IS_SOME_EXISTS, flatSemTheory.Unitv_def] >>
  TRY (last_x_assum mp_tac) >>
  TRY TOP_CASE_TAC \\ fs[]
  \\ rw[flatSemTheory.Boolv_def,flatSemTheory.Boolv_def, backend_commonTheory.tuple_tag_def]
  \\ metis_tac [list_to_v_compile, list_to_v_compile_APPEND, MAP_APPEND]);

(* pattern compiler correctness *)

Theorem sIf_correct:
   ∀env s e1 e2 e3 res.
    evaluate env s [If t e1 e2 e3] = res ∧
    (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
    evaluate env s [sIf t e1 e2 e3] = res
Proof
  rpt gen_tac >>
  Cases_on`isBool T e2 ∧ isBool F e3` >- (
    simp[sIf_def] >>
    simp[patSemTheory.evaluate_def,patSemTheory.do_if_def] >>
    fs[isBool_def] >>
    every_case_tac >> fs[] >> rw[] >>
    full_simp_tac(srw_ss())[evaluate_Con_nil] >>
    imp_res_tac evaluate_sing >> fs[] >>
    EVAL_TAC) >>
  simp[sIf_def] >>
  Cases_on`e1`>>simp[]>>
  Cases_on`l`>>simp[]>>
  simp[patSemTheory.evaluate_def] >>
  simp[patSemTheory.do_if_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[evaluate_Con_nil] >>
  full_simp_tac(srw_ss())[patSemTheory.Boolv_def,backend_commonTheory.true_tag_def,backend_commonTheory.false_tag_def]
QED

Theorem sIf_intro:
   P (evaluate env s [If t e1 e2 e3]) ∧
   SND (evaluate env s [If t e1 e2 e3]) ≠ Rerr (Rabort Rtype_error) ⇒
   P (evaluate env s [sIf t e1 e2 e3])
Proof
  metis_tac[sIf_correct]
QED

val v_to_list_no_closures = Q.prove (
  `!v vs.
    v_to_list v = SOME vs ∧
    no_closures v
    ⇒
    EVERY no_closures vs`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  srw_tac[][patSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[compile_v_def, patSemTheory.v_to_list_def] >>
  srw_tac[][]);

val s = mk_var("s",
  ``patSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha|->gamma,beta|->``:'ffi``])

val lemmas =
  [PAIR_EQ,
   semanticPrimitivesTheory.result_distinct,
   semanticPrimitivesTheory.result_11,
   semanticPrimitivesTheory.error_result_distinct,
   semanticPrimitivesTheory.error_result_11,
   semanticPrimitivesTheory.abort_distinct]

Theorem pure_correct:
   (∀e. pure e ⇒
        ∀env ^s. (∃v. evaluate env s [e] = (s,Rval v)) ∨
                 (evaluate env s [e] = (s,Rerr(Rabort Rtype_error)))) ∧
   (∀es. pure_list es ⇒
        ∀env ^s. ((∃vs. evaluate env s es = (s,Rval vs)) ∨
                  (evaluate env s es = (s,Rerr(Rabort Rtype_error)))) ∧
                 ((∃vs. evaluate env s (REVERSE es) = (s,Rval vs)) ∨
                  (evaluate env s (REVERSE es) = (s,Rerr(Rabort Rtype_error)))))
Proof
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[pure_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  srw_tac[][patSemTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  TRY (
    rename1`op ≠ (Op Opapp)` >>
    fs[patSemTheory.do_app_cases] >> rw[] >>
    rev_full_simp_tac(srw_ss())[]>>srw_tac[][] >>
    first_x_assum(qspecl_then[`env`,`s`]mp_tac)>>srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    NO_TAC) >>
  TRY (
    rename1`do_if (HD vs) e1 e2 = SOME ee` >>
    full_simp_tac(srw_ss())[patSemTheory.do_if_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    metis_tac lemmas) >>
  TRY (
    rename1`evaluate env s (e::es)` >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    REWRITE_TAC[evaluate_append_Rval_iff,evaluate_append_Rerr] >>
    metis_tac lemmas ) >>
  REWRITE_TAC[evaluate_append_Rval_iff,evaluate_append_Rerr] >>
  metis_tac lemmas
QED

Theorem ground_correct:
   (∀e n. ground n e ⇒
      (∀env1 env2 ^s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ∧
          evaluate env1 s [e] = res ⇒
          evaluate env2 s [e] = res)) ∧
    (∀es n. ground_list n es ⇒
      (∀env1 env2 ^s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ⇒
          (evaluate env1 s es = res ⇒
           evaluate env2 s es = res) ∧
          (evaluate env1 s (REVERSE es) = res ⇒
           evaluate env2 s (REVERSE es) = res)))
Proof
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  srw_tac[][patSemTheory.evaluate_def] >>
  res_tac >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY (
    rename1`n1:num < n2` >>
    full_simp_tac(srw_ss())[LIST_EQ_REWRITE] >>
    rev_full_simp_tac(srw_ss())[rich_listTheory.EL_TAKE] >>
    NO_TAC) >>
  TRY (
    rpt(AP_TERM_TAC >> srw_tac[][FUN_EQ_THM]) >>
    AP_THM_TAC >> AP_TERM_TAC >> srw_tac[][FUN_EQ_THM]) >>
  srw_tac[][patSemTheory.do_if_def] >>
  TRY (
    REWRITE_TAC[evaluate_append] >>
    simp[] >> NO_TAC) >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[evaluate_append] >>
  simp[]
QED

Theorem sLet_correct:
   ∀env ^s e1 e2 res.
    evaluate env s [Let t e1 e2] = res ∧
    SND res ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate env s [sLet t e1 e2] = res
Proof
  rw[] \\
  Cases_on`∃tr. e2 = Var_local tr 0` >- (
    fs[sLet_def,patSemTheory.evaluate_def] \\
    CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] \\
    imp_res_tac evaluate_sing \\ fs[] ) \\
  `sLet t e1 e2 = if ground 0 e2 then if pure e1 then e2 else Seq t e1 e2 else Let t e1 e2`
  by (
    fs[sLet_def] \\ Cases_on`e2` \\ fs[] \\
    CASE_TAC \\ fs[] ) \\ fs[] \\
  rw[] >- (
    imp_res_tac pure_correct >>
    first_x_assum(qspecl_then[`s`,`env`]strip_assume_tac) >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def] >>
    qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_correct) >>
    srw_tac[][]) >>
  full_simp_tac(srw_ss())[patSemTheory.evaluate_def] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_correct) >> srw_tac[][]
QED

Theorem sLet_intro:
   P (evaluate env s [Let t e1 e2]) ∧
   SND (evaluate env s [Let t e1 e2]) ≠ Rerr (Rabort Rtype_error)
   ⇒ P (evaluate env s [sLet t e1 e2])
Proof
  metis_tac[sLet_correct]
QED

val Let_Els_correct = Q.prove(
  `∀t n k e tag vs env ^s res us.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate (TAKE k vs ++ us ++ (Conv tag vs::env)) s [e] = res ∧
    SND res ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate (us ++ (Conv tag vs::env)) s [Let_Els t n k e] = res`,
  ho_match_mp_tac Let_Els_ind >> srw_tac[][Let_Els_def] >>
  match_mp_tac sLet_correct >>
  srw_tac[][patSemTheory.evaluate_def] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  simp[patSemTheory.do_app_def] >>
  qmatch_assum_rename_tac`SUC k ≤ LENGTH vs` >>
  first_x_assum(qspecl_then[`tag`,`vs`,`env`,`s`,`EL k vs::us`]mp_tac) >>
  simp[] >>
  `k < LENGTH vs` by simp[] >>
  impl_tac >- (
    full_simp_tac(srw_ss())[arithmeticTheory.ADD1] >>
    full_simp_tac(srw_ss())[rich_listTheory.TAKE_EL_SNOC] >>
    full_simp_tac(srw_ss())[SNOC_APPEND] >>
    metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  srw_tac[][] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[] >>
  metis_tac[SNOC_APPEND,SNOC_EL_TAKE])
val Let_Els_correct = Q.prove(
  `∀t n k e tag vs env ^s res us enve.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate (TAKE k vs ++ us ++ (Conv tag vs::env)) s [e] = res ∧
    (enve = us ++ (Conv tag vs::env)) ∧ SND res ≠ Rerr (Rabort Rtype_error)
    ⇒
    evaluate enve s [Let_Els t n k e] = res`,
  metis_tac[Let_Els_correct]);

val s = mk_var("s",
  ``flatSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``])

val compile_pat_correct = Q.prove(
  `(∀t p v cenv ^s env res env4.
       pmatch cenv s.refs p v env = res ∧ ¬cenv.check_ctor ∧ res ≠ Match_type_error ⇒
       evaluate
         (compile_v v::env4)
         (compile_state co cc s)
         [compile_pat t p] =
         (compile_state co cc s
         ,Rval [Boolv (∃env'. res = Match env')])) ∧
    (∀t n ps qs vs cenv ^s env env' res env4.
       pmatch_list cenv s.refs qs (TAKE n vs) env = Match env' ∧
       pmatch_list cenv s.refs ps (DROP n vs) env = res ∧ ¬cenv.check_ctor ∧ res ≠ Match_type_error ∧
       (n = LENGTH qs) ∧ n ≤ LENGTH vs ⇒
       evaluate
         (compile_vs vs ++ env4)
         (compile_state co cc s)
         [compile_pats t n ps] =
         (compile_state co cc s
         ,Rval [Boolv (∃env'. res = Match env')]))`,
  ho_match_mp_tac compile_pat_ind >>
  srw_tac[][flatSemTheory.pmatch_def,compile_pat_def] >>
  srw_tac[][patSemTheory.evaluate_def]
  >- srw_tac[][patSemTheory.Boolv_def]
  >- srw_tac[][patSemTheory.Boolv_def]
  >- (
    (Cases_on`v`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def]>>pop_assum mp_tac >> srw_tac[][]) >>
    srw_tac[][compile_state_def,patSemTheory.do_app_def,EXISTS_PROD] >>
    srw_tac[][patSemTheory.do_eq_def] >>
    metis_tac[lit_same_type_sym])
  >- (
    Cases_on`v` \\ fs[flatSemTheory.pmatch_def]
    \\ rename1`Conv cn l`
    \\ Cases_on`cn` \\ fs[flatSemTheory.pmatch_def]
    \\ fs[patSemTheory.Boolv_def] )
  >- (
    Cases_on`v`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def]>>pop_assum mp_tac >> srw_tac[][LENGTH_NIL_SYM] >>
    srw_tac[][patSemTheory.do_app_def,compile_state_def] >>
    srw_tac[][patSemTheory.do_eq_def] >>
    simp[flatSemTheory.pmatch_def] >>
    full_simp_tac(srw_ss())[LENGTH_NIL]
    \\ rename1`Conv cn l`
    \\ Cases_on`cn` \\ fs[flatSemTheory.pmatch_def]
    \\ Cases_on`x` \\ fs[flatSemTheory.same_ctor_def]
    \\ rw[] \\ fs[])
  >- (
    match_mp_tac sIf_correct >>
    srw_tac[][patSemTheory.evaluate_def] >>
    full_simp_tac(srw_ss())[LENGTH_NIL_SYM,flatSemTheory.pmatch_def] >>
    full_simp_tac(srw_ss())[patSemTheory.do_app_def,compile_state_def] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def]>>
    simp[patSemTheory.do_if_def] >>
    rename1`Conv cn l` \\ Cases_on`cn` \\ fs[flatSemTheory.pmatch_def] \\ rfs[]
    \\ Cases_on`x` \\ fs[flatSemTheory.same_ctor_def]
    \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    TRY ( simp[evaluate_Con_nil,patSemTheory.Boolv_def] >> rw[] \\ fs[]
          \\ rfs[] \\ NO_TAC) >>
    match_mp_tac Let_Els_correct >>
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt])
  >- (
    match_mp_tac sLet_correct >> simp[] >>
    srw_tac[][patSemTheory.evaluate_def] >>
    srw_tac[][patSemTheory.do_app_def,compile_state_def] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def]>>
    full_simp_tac(srw_ss())[store_lookup_def] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> simp[EL_MAP] >>
    Cases_on`EL n s.refs`>>
    full_simp_tac(srw_ss())[compile_state_def])
  >- (
    simp[patSemTheory.Boolv_def] >> srw_tac[][] >>
    Cases_on`DROP (LENGTH qs) vs`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def]) >>
  match_mp_tac sIf_correct >> simp[] >>
  srw_tac[][patSemTheory.evaluate_def] >>
  qpat_abbrev_tac`xx = evaluate _ _ [sLet _ _ _]` >>
  qho_match_abbrev_tac`P xx` >> qunabbrev_tac`xx` >>
  qmatch_abbrev_tac`P (evaluate B C [sLet tt D E])` >>
  qsuff_tac`P (evaluate B C [Let tt D E])` >- (
    simp[Abbr`P`] >>
    ntac 2 BasicProvers.CASE_TAC >>
    imp_res_tac sLet_correct >> full_simp_tac(srw_ss())[]) >>
  unabbrev_all_tac >>
  srw_tac[][patSemTheory.evaluate_def] >>
  (Cases_on`LENGTH qs = LENGTH vs` >- (
     full_simp_tac(srw_ss())[rich_listTheory.DROP_LENGTH_NIL_rwt,flatSemTheory.pmatch_def] )) >>
  simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
  imp_res_tac flatPropsTheory.pmatch_list_pairwise >>
  Cases_on`DROP (LENGTH qs) vs` >> full_simp_tac(srw_ss())[flatSemTheory.pmatch_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws` >>
  Q.PAT_ABBREV_TAC`env5 = X ++ env4` >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  full_simp_tac(srw_ss())[rich_listTheory.DROP_EL_CONS] >>
  first_x_assum(qspecl_then[`v`,`cenv`,`s`,`env`,`env5`]mp_tac) >>
  Cases_on`pmatch cenv s.refs p v env`>>full_simp_tac(srw_ss())[] >- (
    strip_tac >>
    simp[patSemTheory.do_if_def,patPropsTheory.Boolv_disjoint] >>
    simp[patSemTheory.Boolv_def,patSemTheory.evaluate_def]) >>
  strip_tac >>
  simp[patSemTheory.do_if_def] >>
  simp[Abbr`env5`] >>
  first_x_assum(qspecl_then[`qs++[p]`,`vs`,`cenv`,`s`,`env`]mp_tac) >>
  simp[] >>
  simp[rich_listTheory.TAKE_EL_SNOC,GSYM SNOC_APPEND] >>
  simp[flatPropsTheory.pmatch_list_snoc] >>
  imp_res_tac flatPropsTheory.pmatch_any_match >>
  qmatch_assum_rename_tac`pmatch_list cenv s.refs qs _ env = Match env2` >>
  last_x_assum(qspec_then`env2`strip_assume_tac)>>simp[]>>
  qmatch_assum_rename_tac`pmatch cenv s.refs p v env = Match env3`>>
  Cases_on`pmatch_list cenv s.refs ps ws env`>>simp[]>>
  Cases_on`pmatch_list cenv s.refs ps ws env3`>>full_simp_tac(srw_ss())[]>>
  metis_tac[flatPropsTheory.pmatch_any_match_error
           ,flatPropsTheory.pmatch_any_match
           ,flatPropsTheory.pmatch_any_no_match
           ,match_result_distinct])

val compile_row_correct = Q.prove(
  `(∀t Nbvs0 p bvs0 cenv ^s v menv bvs1 n f.
      (Nbvs0 = NONE::bvs0) ∧
      (pmatch cenv s.refs p v [] = Match menv) ∧
      ¬cenv.check_ctor ∧
      (compile_row t Nbvs0 p = (bvs1,n,f))
    ⇒ ∃menv4 bvs.
       EVERY NoRun_v menv4 /\
       (bvs1 = bvs ++ bvs0) ∧
       (LENGTH bvs = SUC n) ∧
       (LENGTH menv4 = SUC n) ∧
       (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
        MAP (λ(x,v). (SOME x, compile_v v)) menv) ∧
       ∀env count genv e res.
         evaluate (menv4++env)
           ((<| clock := count; refs := MAP (map_sv compile_v) s.refs;
                ffi := s.ffi; globals := genv;
                compile := any_cc;
                compile_oracle := any_co
                |>):('c,'ffi) patSem$state)
         [e] = res ∧
         SND res ≠ Rerr (Rabort Rtype_error) ⇒
         evaluate (compile_v v::env)
           <| clock := count; refs := MAP (map_sv compile_v) s.refs;
              ffi := s.ffi; globals := genv;
              compile := any_cc;
              compile_oracle := any_co
              |> [f e] = res) ∧
   (∀t bvsk0 nk k ps tag cenv ^s qs vs menvk menv4k menv bvsk bvs0 bvs1 n1 f.
     (pmatch_list cenv s.refs qs (TAKE k vs) [] = Match menvk) ∧
     (pmatch_list cenv s.refs ps (DROP k vs) [] = Match menv) ∧
      ¬cenv.check_ctor ∧
     (compile_cols t bvsk0 nk k ps = (bvs1,n1,f)) ∧
     (bvsk0 = bvsk ++ NONE::bvs0) ∧
     (k = LENGTH qs) ∧ k ≤ LENGTH vs ∧ (LENGTH bvsk = nk) ∧
     (LENGTH menv4k = LENGTH bvsk) ∧
     (FILTER (IS_SOME o FST) (ZIP(bvsk,menv4k)) =
      MAP (λ(x,v). (SOME x, compile_v v)) menvk)
   ⇒ ∃menv4 bvs.
       EVERY NoRun_v menv4 /\
       (bvs1 = bvs ++ bvsk ++ NONE::bvs0) ∧
       (LENGTH bvs = n1) ∧ (LENGTH menv4 = n1) ∧
       (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
        MAP (λ(x,v). (SOME x, compile_v v)) menv) ∧
       ∀env count genv e res.
         evaluate (menv4++menv4k++(Conv tag (MAP compile_v vs))::env)
           ((<| clock := count; refs := MAP (map_sv compile_v) s.refs;
                ffi := s.ffi; globals := genv;
                compile := any_cc; compile_oracle := any_co |>): ('c,'ffi) patSem$state)
         [e] = res ∧
         SND res ≠ Rerr (Rabort Rtype_error) ⇒
         evaluate (menv4k++(Conv tag (MAP compile_v vs))::env)
           <| clock := count; refs := MAP (map_sv compile_v) s.refs;
              ffi := s.ffi; globals := genv;
              compile := any_cc; compile_oracle := any_co |> [f e] = res)`,
  ho_match_mp_tac compile_row_ind >>
  strip_tac >- (
    srw_tac[][flatSemTheory.pmatch_def,compile_row_def] >> srw_tac[][] >>
    qexists_tac`[compile_v v]` >> srw_tac[][] >>
    fs [compile_v_NoRun_v]) >>
  strip_tac >- (
    srw_tac[][flatSemTheory.pmatch_def,compile_row_def] >> srw_tac[][] >>
    qexists_tac`[compile_v v]` >> srw_tac[][] >>
    fs [compile_v_NoRun_v]) >>
  strip_tac >- (
    srw_tac[][pmatch_flat_def,compile_row_def] >> srw_tac[][] >>
    qexists_tac`[compile_v v]` >> srw_tac[][] >>
    fs [compile_v_NoRun_v] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[flatSemTheory.pmatch_def] >>
    rpt(pop_assum mp_tac) >> srw_tac[][] ) >>
  strip_tac >- (
    srw_tac[][pmatch_flat_def,compile_row_def] >> full_simp_tac(srw_ss())[] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[pmatch_flat_def] >>
    qpat_x_assum`X = Match menv`mp_tac >> srw_tac[][] >>
    rename1`pmatch _ _ (Pcon xx _) (Conv yy _) [] = _`
    \\ Cases_on`xx` \\ Cases_on`yy` \\ rfs[pmatch_flat_def]
    \\ pop_assum mp_tac \\ rw[] >>
    qmatch_assum_rename_tac`pmatch_list cenv s.refs ps vs [] = Match menv` >>
    full_simp_tac(srw_ss())[LENGTH_NIL,pmatch_flat_def,LENGTH_NIL_SYM] >>
    Q.PAT_ABBREV_TAC`w = Conv X Y` >>
    qmatch_assum_rename_tac`Abbrev(w = Conv tag (MAP compile_v vs))` >>
    first_x_assum(qspecl_then[`tag`,`cenv`,`s`,`vs`]mp_tac) >> srw_tac[][] >> srw_tac[][] >>
    simp[] >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    conj_tac >- fs [Abbr`w`, compile_v_NoRun_v, NoRun_v_def, ETA_AX, EVERY_MAP] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC),Once(GSYM rich_listTheory.CONS_APPEND)] >>
    rpt strip_tac >> res_tac >> full_simp_tac(srw_ss())[] >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[]) >>
  strip_tac >- (
    srw_tac[][compile_row_def] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[pmatch_flat_def] >>
    qpat_x_assum`X = Match menv`mp_tac >> BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    srw_tac[][] >> full_simp_tac(srw_ss())[UNCURRY,LET_THM] >> srw_tac[][] >>
    qmatch_assum_rename_tac`pmatch cenv s.refs p v [] = Match menv` >>
    first_x_assum(qspecl_then[`cenv`,`s`,`v`]mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`tt = compile_row _ X Y` >>
    `∃bvs1 n f. tt = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    qunabbrev_tac`tt` >> simp[] >> srw_tac[][] >> simp[] >>
    Q.PAT_ABBREV_TAC`w = patSem$Loc _` >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    conj_tac >- fs [Abbr`w`, compile_v_NoRun_v, NoRun_v_def, ETA_AX, EVERY_MAP] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
    rpt strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rev_full_simp_tac(srw_ss())[] >>
    match_mp_tac sLet_correct >>
    simp[patSemTheory.evaluate_def] >>
    simp[patSemTheory.do_app_def] >> simp[Abbr`w`] >>
    full_simp_tac(srw_ss())[store_lookup_def] >>
    simp[EL_MAP] ) >>
  strip_tac >- srw_tac[][] >>
  strip_tac >- srw_tac[][] >>
  strip_tac >- (
    srw_tac[][compile_row_def] >>
    imp_res_tac flatPropsTheory.pmatch_list_pairwise >>
    imp_res_tac EVERY2_LENGTH >>
    full_simp_tac(srw_ss())[LENGTH_NIL,pmatch_flat_def] ) >>
  srw_tac[][compile_row_def] >>
  `∃bvsk1 nk1 f1. compile_row (t § 1) (NONE::(bvsk++[NONE]++bvs0)) p = (bvsk1,nk1,f1)` by
    simp[GSYM EXISTS_PROD] >> full_simp_tac(srw_ss())[LET_THM] >>
  `∃bvs n fs. compile_cols (t § 2) bvsk1 (LENGTH bvsk + 1 + nk1) (LENGTH qs + 1) ps = (bvs,n,fs)` by
    simp[GSYM EXISTS_PROD] >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  Cases_on`DROP (LENGTH qs) vs`>>full_simp_tac(srw_ss())[pmatch_flat_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws` >>
  Cases_on`pmatch cenv s.refs p v []`>>full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`cenv`,`s`,`v`]mp_tac) >> simp[] >>
  strip_tac >> srw_tac[][] >>
  first_x_assum(qspecl_then[`tag`,`cenv`,`s`,`qs++[p]`,`vs`]mp_tac) >>
  Cases_on`LENGTH vs = LENGTH qs`>>full_simp_tac(srw_ss())[rich_listTheory.DROP_LENGTH_NIL_rwt] >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  full_simp_tac(srw_ss())[rich_listTheory.DROP_EL_CONS] >>
  simp[rich_listTheory.TAKE_EL_SNOC,Once(GSYM SNOC_APPEND)] >>
  simp[flatPropsTheory.pmatch_list_snoc] >>
  imp_res_tac (CONJUNCT1 flatPropsTheory.pmatch_any_match) >>
  pop_assum(qspec_then`menvk`strip_assume_tac) >> simp[] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac (CONJUNCT2 flatPropsTheory.pmatch_any_match) >>
  rpt(pop_assum(qspec_then`[]`mp_tac)) >>
  ntac 2 strip_tac >> simp[] >>
  disch_then(qspec_then`bvs0`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
  simp[] >>
  qmatch_assum_rename_tac`FILTER _ (ZIP(bvs2,menv4)) = MAP _ env2` >>
  disch_then(qspec_then`menv4 ++ menv4k`mp_tac) >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  impl_tac >- (
    qpat_x_assum`pmatch cenv s.refs p v menvk = X`mp_tac >>
    simp[Once (CONJUNCT1 flatPropsTheory.pmatch_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  srw_tac[][] >> srw_tac[][] >> simp[] >>
  qmatch_assum_rename_tac`LENGTH bvs3 = LENGTH menv3` >>
  qexists_tac`menv3 ++ menv4` >> simp[] >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  conj_tac >- (
    qpat_x_assum`pmatch_list cenv s.refs ps ww env2 = X`mp_tac >>
    simp[Once (CONJUNCT2 flatPropsTheory.pmatch_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  srw_tac[][] >>
  match_mp_tac sLet_correct >>
  simp[patSemTheory.evaluate_def] >>
  simp[patSemTheory.do_app_def] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  simp[EL_MAP])

(* value relation *)

val bind_def = Define`
  (bind V 0 0 ⇔ T) ∧
  (bind V (SUC n1) (SUC n2) ⇔ V n1 n2) ∧
  (bind V _ _ ⇔ F)`

Theorem bind_mono:
   (∀x y. V1 x y ⇒ V2 x y) ⇒ bind V1 x y ⇒ bind V2 x y
Proof
  Cases_on`x`>>Cases_on`y`>>srw_tac[][bind_def]
QED
val _ = export_mono"bind_mono"

val bindn_def = Define`bindn = FUNPOW bind`

Theorem bind_thm:
   ∀V x y. bind V x y =
      if x = 0 then y = 0 else
      if y = 0 then x = 0 else
      V (x-1) (y-1)
Proof
  gen_tac >> Cases >> Cases >> srw_tac[][bind_def]
QED

Theorem bindn_mono:
   (∀x y. R1 x y ⇒ R2 x y) ⇒
    bindn n R1 x y ⇒ bindn n R2 x y
Proof
  srw_tac[][bindn_def] >>
  match_mp_tac (MP_CANON FUNPOW_mono) >>
  simp[] >> metis_tac[bind_mono]
QED
val _ = export_mono"bindn_mono"

Theorem bindn_thm:
   ∀n k1 k2.
    bindn n R k1 k2 ⇔
    if k1 < n ∧ k2 < n then k1 = k2
    else n ≤ k1 ∧ n ≤ k2 ∧ R (k1-n) (k2-n)
Proof
  Induct>>simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  Cases>>Cases>>simp[bind_def,GSYM bindn_def]
QED

val (exp_rel_rules,exp_rel_ind,exp_rel_cases) = Hol_reln`
  (exp_rel z1 z2 V e1 e2
   ⇒ exp_rel z1 z2 V (Raise t e1) (Raise t e2)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel (z1+1) (z2+1) (bind V) e12 e22
   ⇒ exp_rel z1 z2 V (Handle t e11 e12) (Handle t e21 e22)) ∧
  (exp_rel z1 z2 V (Lit t l) (Lit t l)) ∧
  (LIST_REL (exp_rel z1 z2 V) es1 es2
   ⇒ exp_rel z1 z2 V (Con t tag es1) (Con t tag es2)) ∧
  ((k1 < z1 ∧ k2 < z2 ∧ V k1 k2) ∨ (z1 ≤ k1 ∧ z2 ≤ k2 ∧ (k1 = k2))
   ⇒ exp_rel z1 z2 V (Var_local t k1) (Var_local t k2)) ∧
  (exp_rel (z1+1) (z2+1) (bind V) e1 e2
   ⇒ exp_rel z1 z2 V (Fun t e1) (Fun t e2)) ∧
  (LIST_REL (exp_rel z1 z2 V) es1 es2
   ⇒ exp_rel z1 z2 V (App t op es1) (App t op es2)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel z1 z2 V e12 e22 ∧ exp_rel z1 z2 V e13 e23
   ⇒ exp_rel z1 z2 V (If t e11 e12 e13) (If t e21 e22 e23)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel (z1+1) (z2+1) (bind V) e12 e22
   ⇒ exp_rel z1 z2 V (Let t e11 e12) (Let t e21 e22)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel z1 z2 V e12 e22
   ⇒ exp_rel z1 z2 V (Seq t e11 e12) (Seq t e21 e22)) ∧
  (LIST_REL (exp_rel (z1+(SUC(LENGTH es1))) (z2+(SUC(LENGTH es2))) (bindn (SUC (LENGTH es1)) V)) es1 es2 ∧
   exp_rel (z1+(LENGTH es1)) (z2+(LENGTH es2)) (bindn (LENGTH es1) V) e1 e2
   ⇒ exp_rel z1 z2 V (Letrec t es1 e1) (Letrec t es2 e2))`;

Theorem exp_rel_refl:
   (∀e z V. (∀k. k < z ⇒ V k k) ⇒ exp_rel z z V e e) ∧
    (∀es z V. (∀k. k < z ⇒ V k k) ⇒ LIST_REL (exp_rel z z V) es es)
Proof
  ho_match_mp_tac(TypeBase.induction_of``:patLang$exp``) >> srw_tac[][] >>
  TRY (first_x_assum match_mp_tac) >>
  srw_tac[][Once exp_rel_cases] >>
  TRY (first_x_assum match_mp_tac) >>
  TRY (metis_tac[]) >>
  TRY (Cases>>simp[bind_def]>>NO_TAC) >>
  TRY (Cases_on`n < z` >>simp[] >> NO_TAC) >>
  srw_tac[][bindn_thm] >>
  Cases_on`k < SUC (LENGTH es)` >> simp[] >>
  Cases_on`k < LENGTH es` >> simp[]
QED

Theorem exp_rel_mono:
   (∀x y. V1 x y ⇒ V2 x y) ⇒
    exp_rel z1 z2 V1 e1 e2 ⇒
    exp_rel z1 z2 V2 e1 e2
Proof
  strip_tac >> strip_tac >> last_x_assum mp_tac >>
  qid_spec_tac`V2` >> pop_assum mp_tac >>
  map_every qid_spec_tac[`e2`,`e1`,`V1`,`z2`,`z1`] >>
  ho_match_mp_tac exp_rel_ind >>
  strip_tac >- ( srw_tac[][] >> srw_tac[][Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >>
    srw_tac[][Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> srw_tac[][] ) >>
  strip_tac >- ( srw_tac[][] >> srw_tac[][Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> srw_tac[][Once exp_rel_cases] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- ( srw_tac[][] >> srw_tac[][Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> srw_tac[][Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> srw_tac[][] ) >>
  strip_tac >- (
    srw_tac[][] >> srw_tac[][Once exp_rel_cases] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- ( srw_tac[][] >> srw_tac[][Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> srw_tac[][Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> srw_tac[][] ) >>
  strip_tac >- ( srw_tac[][] >> srw_tac[][Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> srw_tac[][Once exp_rel_cases] >> TRY (
      match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      HINT_EXISTS_TAC >> simp[] >> srw_tac[][] >>
      first_x_assum match_mp_tac >>
      match_mp_tac bindn_mono >>
      simp[] ) >>
    first_x_assum match_mp_tac >>
    match_mp_tac bindn_mono >>
    simp[] )
QED
val _ = export_mono"exp_rel_mono";

Theorem exp_rel_lit:
   (exp_rel z1 z2 V (Lit t l) e2 ⇔ (e2 = Lit t l)) ∧
    (exp_rel z1 z2 V e1 (Lit t l) ⇔ (e1 = Lit t l)) ∧
    (exp_rel z1 z2 V (Bool t b) e2 ⇔ (e2 = Bool t b)) ∧
    (exp_rel z1 z2 V e1 (Bool t b) ⇔ (e1 = Bool t b))
Proof
  srw_tac[][Once exp_rel_cases] >>
  srw_tac[][Once exp_rel_cases,Bool_def]
QED
val _ = export_rewrites["exp_rel_lit"];

Theorem bind_O:
   ∀R1 R2. bind (R2 O R1) = bind R2 O bind R1
Proof
  srw_tac[][] >> simp[FUN_EQ_THM] >>
  simp[relationTheory.O_DEF] >>
  srw_tac[][bind_thm,relationTheory.O_DEF,EQ_IMP_THM] >> rev_full_simp_tac(srw_ss())[] >- (
    qexists_tac`SUC y` >> simp[] ) >>
  qexists_tac`y-1` >> simp[]
QED
val _ = export_rewrites["bind_O"];

Theorem bindn_O:
   ∀R1 R2 n. bindn n (R2 O R1) = bindn n R2 O bindn n R1
Proof
  srw_tac[][FUN_EQ_THM,bindn_thm,relationTheory.O_DEF] >>
  srw_tac[][EQ_IMP_THM] >> simp[] >> fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>fsrw_tac[ARITH_ss][]
  >- (qexists_tac`y+n` >> simp[]) >>
  (qexists_tac`y-n` >> simp[])
QED
val _ = export_rewrites["bindn_O"];

val exp_rel_trans = Q.prove(
  `∀z1 z2 V1 e1 e2. exp_rel z1 z2 V1 e1 e2 ⇒
      ∀z3 V2 e3. exp_rel z2 z3 V2 e2 e3 ⇒ exp_rel z1 z3 (V2 O V1) e1 e3`,
   ho_match_mp_tac (theorem"exp_rel_strongind") >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- (
     srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) >>
     rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
     full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- (
     srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) >>
     simp[relationTheory.O_DEF] >> metis_tac[]) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- (
     srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) >>
     rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
     full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- ( srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) ) >>
   strip_tac >- (
     srw_tac[][] >> pop_assum mp_tac >> ntac 2 (srw_tac[][Once exp_rel_cases]) >>
     rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
     full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL] ) )
Theorem exp_rel_trans:
   ∀z1 z2 z3 V1 V2 V3 e1 e2 e3.
      exp_rel z1 z2 V1 e1 e2 ∧
      exp_rel z2 z3 V2 e2 e3 ∧
      (V3 = V2 O V1) ⇒
      exp_rel z1 z3 V3 e1 e3
Proof
  metis_tac[exp_rel_trans]
QED

val env_rel_def = Define`
  env_rel R env1 env2 k1 k2 ⇔
    k1 < LENGTH env1 ∧ k2 < LENGTH env2 ∧ R (EL k1 env1) (EL k2 env2)`

Theorem env_rel_mono:
   (∀x y. R1 x y ⇒ R2 x y) ⇒
    env_rel R1 env1 env2 k1 k2 ⇒
    env_rel R2 env1 env2 k1 k2
Proof
  srw_tac[][env_rel_def]
QED
val _ = export_mono"env_rel_mono";

val env_rel_cons = Q.prove(
  `R v1 v2 ∧
    bind (env_rel R env1 env2) k1 k2
    ⇒ env_rel R (v1::env1) (v2::env2) k1 k2`,
  Cases_on`k1`>>Cases_on`k2`>>srw_tac[][env_rel_def,bind_def])

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln`
  (v_rel (Litv l) (Litv l)) ∧
  (LIST_REL v_rel vs1 vs2
   ⇒ v_rel (Conv tag vs1) (Conv tag vs2)) ∧
  (exp_rel (SUC(LENGTH env1)) (SUC(LENGTH env2))
    (bind (env_rel v_rel env1 env2)) exp1 exp2 /\
    (EVERY NoRun_v env1 <=> EVERY NoRun_v env2)
   ⇒ v_rel (Closure env1 exp1) (Closure env2 exp2)) ∧
  (LIST_REL (exp_rel (SUC(LENGTH funs1)+LENGTH env1) (SUC(LENGTH funs2)+LENGTH env2)
              (bindn (SUC (LENGTH funs1)) (env_rel v_rel env1 env2)))
            funs1 funs2 /\
   (EVERY NoRun_v env1 <=> EVERY NoRun_v env2)
   ⇒ v_rel (Recclosure env1 funs1 n) (Recclosure env2 funs2 n)) ∧
  (v_rel (Loc n) (Loc n)) ∧
  (LIST_REL v_rel vs1 vs2
   ⇒ v_rel (Vectorv vs1) (Vectorv vs2))`;

Theorem v_rel_lit:
   (v_rel (Litv l) v2 ⇔ (v2 = Litv l)) ∧
    (v_rel v1 (Litv l) ⇔ (v1 = Litv l)) ∧
    (v_rel (Boolv b) v2 ⇔ (v2 = Boolv b)) ∧
    (v_rel v1 (Boolv b) ⇔ (v1 = Boolv b))
Proof
  srw_tac[][Once v_rel_cases] >> srw_tac[][Once v_rel_cases,patSemTheory.Boolv_def]
QED
val _ = export_rewrites["v_rel_lit"]

Theorem v_rel_loc:
   (v_rel (Loc l) v2 ⇔ (v2 = Loc l)) ∧
    (v_rel v1 (Loc l) ⇔ (v1 = Loc l))
Proof
  srw_tac[][Once v_rel_cases] >> srw_tac[][Once v_rel_cases]
QED
val _ = export_rewrites["v_rel_loc"]

Theorem v_rel_refl:
   ∀v. v_rel v v
Proof
  qsuff_tac`(∀v. v_rel v v) ∧ (∀vs. LIST_REL v_rel vs vs)`>-srw_tac[][]>>
  ho_match_mp_tac(TypeBase.induction_of``:patSem$v``)>>
  srw_tac[][] >> srw_tac[][Once v_rel_cases] >>
  TRY (
    match_mp_tac (CONJUNCT1 exp_rel_refl) >>
    Cases>>simp[bind_def,env_rel_def]>>
    full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] ) >>
  match_mp_tac (CONJUNCT2 exp_rel_refl) >>
  simp[bindn_thm] >> srw_tac[][env_rel_def] >>
  qmatch_assum_rename_tac`k < LENGTH vs + SUC (LENGTH ls)` >>
  Cases_on`k < SUC (LENGTH ls)`>>simp[] >>
  full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
  simp[]
QED
val _ = export_rewrites["v_rel_refl"]

Theorem v_rel_trans:
   ∀v1 v2. v_rel v1 v2 ⇒ ∀v3. v_rel v2 v3 ⇒ v_rel v1 v3
Proof
  ho_match_mp_tac (theorem"v_rel_strongind") >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    match_mp_tac LIST_REL_trans >>
    qexists_tac`vs2` >> simp[] >>
    rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
    full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >> srw_tac[][] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`exp_rel z1 z2 V1 exp1 exp2` >>
    qmatch_assum_abbrev_tac`exp_rel z2 z3 V2 exp2 exp3` >>
    match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
    qexists_tac`V2 O V1` >>
    conj_tac >- (
      simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
      simp[bind_thm,env_rel_def] >>
      srw_tac[][] >> fsrw_tac[ARITH_ss][] >> rev_full_simp_tac(srw_ss())[] ) >>
    match_mp_tac exp_rel_trans >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >> srw_tac[][] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
    full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL] >> srw_tac[][] >>
    res_tac >>
    qmatch_assum_abbrev_tac`exp_rel z1 z2 V1 exp1 exp2` >>
    qmatch_assum_abbrev_tac`exp_rel z2 z3 V2 exp2 exp3` >>
    match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
    qexists_tac`V2 O V1` >>
    conj_tac >- (
      simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
      simp[bindn_thm,env_rel_def] >>
      simp[arithmeticTheory.ADD1] >>
      srw_tac[][] >> fsrw_tac[ARITH_ss][] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
      fsrw_tac[ARITH_ss][] ) >>
    metis_tac[exp_rel_trans]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once v_rel_cases,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  simp[Once v_rel_cases,PULL_EXISTS] >>
  match_mp_tac LIST_REL_trans >>
  qexists_tac`vs2` >> simp[] >>
  rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
  full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,MEM_EL]
QED

Theorem bind_inv:
   ∀V. bind (inv V) = inv (bind V)
Proof
  srw_tac[][FUN_EQ_THM,bind_thm,relationTheory.inv_DEF] >>
  srw_tac[][]
QED
val _ = export_rewrites["bind_inv"]

Theorem bindn_inv:
   ∀V n. bindn n (inv V) = inv (bindn n V)
Proof
  srw_tac[][FUN_EQ_THM,bindn_thm,relationTheory.inv_DEF] >>
  srw_tac[][] >> simp[] >> full_simp_tac(srw_ss())[] >> simp[]
QED
val _ = export_rewrites["bindn_inv"]

Theorem exp_rel_sym:
   ∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒ exp_rel z2 z1 (inv V) e2 e1
Proof
  ho_match_mp_tac exp_rel_ind >> srw_tac[][] >>
  simp[Once exp_rel_cases] >>
  rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
  full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,relationTheory.inv_DEF]
QED

Theorem v_rel_sym:
   ∀v1 v2. v_rel v1 v2 ⇒ v_rel v2 v1
Proof
  ho_match_mp_tac v_rel_ind >> srw_tac[][] >>
  simp[Once v_rel_cases] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  TRY(first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))) >>
  first_x_assum (strip_assume_tac o MATCH_MP exp_rel_sym) >>
  match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
  fsrw_tac[ARITH_ss][] >>
  HINT_EXISTS_TAC >>
  simp[relationTheory.inv_DEF,bind_thm,bindn_thm] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][env_rel_def]
QED

val state_rel_def = Define`
  state_rel (s1: ('c,'ffi) patSem$state) (s2: ('c,'ffi) patSem$state) ⇔
    s1.clock = s2.clock ∧
    LIST_REL (sv_rel v_rel) s1.refs s2.refs ∧
    s1.ffi = s2.ffi ∧
    LIST_REL (OPTREL v_rel) s1.globals s2.globals`;

val state_rel_clock = Q.prove(
  `state_rel s1 s2 ⇒ s1.clock = s2.clock`,
  srw_tac[][state_rel_def])

val state_rel_dec_clock = Q.prove(
  `state_rel s s2 ⇒ state_rel (dec_clock s) (dec_clock s2)`,
  srw_tac[][state_rel_def,patSemTheory.dec_clock_def])

Theorem state_rel_refl[simp]:
   state_rel s s
Proof
  srw_tac[][state_rel_def] >> match_mp_tac EVERY2_refl >> srw_tac[][]
QED

val result_rel_v_v_rel_trans =
  result_rel_trans
  |> Q.GENL[`R1`,`R2`]
  |> Q.ISPECL[`v_rel`,`v_rel`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[v_rel_trans])

val LIST_REL_v_rel_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_rel`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_rel_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l1`,`l2`,`l3`]

val LIST_REL_OPTREL_v_rel_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`OPTREL v_rel`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[OPTREL_trans,v_rel_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l1`,`l2`,`l3`]

val LIST_REL_sv_rel_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`sv_rel v_rel`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[sv_rel_trans,v_rel_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l1`,`l2`,`l3`]

val result_rel_LIST_v_v_rel_trans =
  result_rel_trans
  |> Q.GENL[`R1`,`R2`]
  |> Q.ISPECL[`LIST_REL v_rel`,`v_rel`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[LIST_REL_v_rel_trans,v_rel_trans])

val exc_rel_v_rel_trans =
  exc_rel_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_rel`
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_rel_trans])

val state_rel_trans = Q.prove(
  `state_rel s1 s2 ∧ state_rel s2 s3 ⇒ state_rel s1 s3`,
  srw_tac[][state_rel_def] >>
  metis_tac[LIST_REL_sv_rel_trans,LIST_REL_OPTREL_v_rel_trans]);

(* semantic functions respect relation *)

val do_eq_def = patSemTheory.do_eq_def

Theorem do_eq_v_rel:
   ∀v1 v2. v_rel v1 v2 ⇒ ∀v3 v4. v_rel v3 v4 ⇒ do_eq v1 v3 = do_eq v2 v4
Proof
  ho_match_mp_tac v_rel_ind >>
  simp[do_eq_def] >> srw_tac[][] >>
  Cases_on`v3`>>Cases_on`v4`>>full_simp_tac(srw_ss())[do_eq_def] >>
  pop_assum mp_tac >> simp[Once v_rel_cases] >> srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  ntac 2 (pop_assum kall_tac) >>
  qmatch_assum_rename_tac`LIST_REL v_rel l1 l2` >>
  ntac 3 (pop_assum mp_tac) >>
  map_every qid_spec_tac[`l2`,`l1`,`vs2`,`vs1`] >>
  Induct >> simp[PULL_EXISTS] >>
  Cases_on`l1`>>Cases_on`l2`>>simp[do_eq_def] >>
  srw_tac[][] >>
  BasicProvers.CASE_TAC >> srw_tac[][] >>
  BasicProvers.CASE_TAC >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[]
QED

Theorem do_eq_list_v_rel:
   ∀v1 v2 v3 v4. LIST_REL v_rel v1 v2 ∧ LIST_REL v_rel v3 v4 ⇒ do_eq_list v1 v3 = do_eq_list v2 v4
Proof
  Induct \\ simp[do_eq_def] \\ Cases_on`v3` \\ simp[do_eq_def,PULL_EXISTS] \\ rw[]
  \\ imp_res_tac do_eq_v_rel \\ fs[]
  \\ CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[]
QED

Theorem do_opapp_v_rel:
   ∀vs vs'.
    LIST_REL v_rel vs vs' ⇒
    OPTION_REL
      (λ(env1,e1) (env2,e2).
        exp_rel (LENGTH env1) (LENGTH env2) (env_rel v_rel env1 env2) e1 e2)
      (do_opapp vs)
      (do_opapp vs')
Proof
  srw_tac[][patSemTheory.do_opapp_def] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def] >> srw_tac[][] >>
  Cases_on`t`>>full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def] >> srw_tac[][] >>
  Cases_on`t'`>>full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def] >> srw_tac[][] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def] >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> srw_tac[][] >>
  srw_tac[][quotient_optionTheory.OPTION_REL_def] >>
  TRY (imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
  full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
  match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
  simp[patSemTheory.build_rec_env_def] >> res_tac >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  qmatch_assum_abbrev_tac`exp_rel z1 z2 V e1 e2` >>
  qexists_tac`V` >>
  simp[Abbr`V`,bindn_thm,bind_thm,env_rel_def] >>
  TRY (
    Cases >> Cases >> simp[] >>
    unabbrev_all_tac >> simp[] >> NO_TAC) >>
  Cases >> Cases >> srw_tac[][env_rel_def] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[Once v_rel_cases] >>
  rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
  full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS,arithmeticTheory.ADD1,Abbr`z1`,Abbr`z2`] >>
  simp[]
QED

val v_to_list_SOME = Q.prove(
  `∀v ls.
    v_to_list v = SOME ls ⇒
         (v = Conv nil_tag []) ∨
         (∃v1 v2 t.
           v = Conv cons_tag [v1;v2] ∧
           v_to_list v2 = SOME t ∧
           ls = v1::t)`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def] >> srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[])

val v_to_list_v_rel = Q.prove(
  `∀l1 l2 l3.
    v_rel l1 l2 ∧ v_to_list l1 = SOME l3 ⇒
    ∃l4. v_to_list l2 = SOME l4 ∧
         LIST_REL v_rel l3 l4`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def] >> srw_tac[][] >- (
    full_simp_tac(srw_ss())[Once v_rel_cases]>>
    simp[patSemTheory.v_to_list_def] ) >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> srw_tac[][] >>
  simp[patSemTheory.v_to_list_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> srw_tac[][] >>
  res_tac >> simp[])

val v_to_list_v_rel_none = Q.prove(
  `∀l1 l2.
    v_rel l1 l2 ∧ v_to_list l1 = NONE ⇒
    v_to_list l2 = NONE`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def] >> srw_tac[][] >>
  qpat_x_assum`v_rel _ _`mp_tac >>
  simp[Once v_rel_cases,patSemTheory.v_to_list_def] >>
  strip_tac \\ fs[patSemTheory.v_to_list_def] >>
  rw[] >> every_case_tac >> fs[] >>
  res_tac >> fs[]);

val v_to_char_list_v_rel = Q.prove(
  `∀l1 l2 l3.
    v_rel l1 l2 ∧ v_to_char_list l1 = SOME l3 ⇒
    v_to_char_list l2 = SOME l3`,
  ho_match_mp_tac patSemTheory.v_to_char_list_ind >>
  simp[patSemTheory.v_to_char_list_def] >> srw_tac[][] >- (
    full_simp_tac(srw_ss())[Once v_rel_cases]>>
    simp[patSemTheory.v_to_char_list_def] ) >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> srw_tac[][] >>
  simp[patSemTheory.v_to_char_list_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> srw_tac[][] >>
  res_tac >> simp[])

val v_to_char_list_v_rel_none = Q.prove(
  `∀l1 l2.
    v_rel l1 l2 ∧ v_to_char_list l1 = NONE ⇒
    v_to_char_list l2 = NONE`,
  ho_match_mp_tac patSemTheory.v_to_char_list_ind >>
  simp[patSemTheory.v_to_char_list_def] >> srw_tac[][] >>
  qpat_x_assum`v_rel _ _`mp_tac >>
  simp[Once v_rel_cases,patSemTheory.v_to_char_list_def] >>
  strip_tac \\ fs[patSemTheory.v_to_char_list_def] >>
  rw[] >> every_case_tac >> fs[] >>
  res_tac >> fs[] >> fs[Once v_rel_cases] >>
  fs[patSemTheory.v_to_char_list_def]);

val vs_to_string_v_rel = Q.prove(
  `∀l1 l2.
    LIST_REL v_rel l1 l2 ⇒
    vs_to_string l2 = vs_to_string l1`,
  ho_match_mp_tac patSemTheory.vs_to_string_ind
  \\ rw[patSemTheory.vs_to_string_def,flatSemTheory.vs_to_string_def]
  \\ fs[v_rel_cases]
  \\ rw[patSemTheory.vs_to_string_def,flatSemTheory.vs_to_string_def]);

val do_app_def = patSemTheory.do_app_def

local
  val ty =
    ``patSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
    |> type_subst[alpha|->gamma,beta|->``:'ffi``]
in
  val s1 = mk_var("s1",ty)
  val s = mk_var("s",ty)
end

Theorem list_to_v_v_rel:
   !xs ys. LIST_REL v_rel xs ys ==> v_rel (list_to_v xs) (list_to_v ys)
Proof
  Induct \\ rw [] \\ fs [patSemTheory.list_to_v_def, v_rel_rules]
QED

Theorem list_to_v_APPEND:
   !x1 y1 x2 y2.
     v_rel (list_to_v x1) (list_to_v x2) /\
     v_rel (list_to_v y1) (list_to_v y2) ==>
       v_rel (list_to_v (x1 ++ y1)) (list_to_v (x2 ++ y2))
Proof
  Induct \\ Induct_on `x2`
  \\ TRY (rw [v_rel_cases, patSemTheory.list_to_v_def] \\ NO_TAC)
  \\ rw []
  \\ fs [patSemTheory.list_to_v_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp [Once v_rel_cases] \\ rw []
  \\ simp [Once v_rel_cases]
QED

Theorem do_app_v_rel:
   ∀^s op s' vs vs'.
      LIST_REL v_rel vs vs' ⇒
      state_rel s s' ⇒
      OPTION_REL
        (λ(s1,res1) (s2,res2).
          state_rel s1 s2 ∧
          result_rel v_rel v_rel res1 res2)
        (do_app s op vs)
        (do_app s' op vs')
Proof
  srw_tac[][] >>
  srw_tac[][optionTheory.OPTREL_def] >>
  Cases_on`do_app s op vs`>>srw_tac[][]>-(
    Cases_on `op = (Op ListAppend)`
    >-
     (fs [] \\ rveq
     \\ pop_assum mp_tac
     \\ fs [patSemTheory.do_app_def]
     \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
     \\ imp_res_tac v_to_list_v_rel_none
     \\ imp_res_tac v_to_list_v_rel \\ rfs [])
    \\ qpat_x_assum `do_app _ _ _ = _` (strip_assume_tac o SIMP_RULE std_ss [patSemTheory.do_app_cases_none]) >>
    rw[] >> fs[v_rel_cases] >>
    rw[patSemTheory.do_app_def] >>
    fs[store_alloc_def, store_lookup_def, store_assign_def, state_rel_def, OPTREL_def, do_eq_def] >>
    imp_res_tac LIST_REL_LENGTH >> fs[] >>
    fs [patSemTheory.v_to_list_def, patSemTheory.v_to_char_list_def] \\ fs[] >>
    TRY (
      fs[LIST_REL_EL_EQN,OPTREL_def]
      \\ res_tac \\ fs[sv_rel_cases] \\ fs[]
      \\ NO_TAC ) >>
    TRY (
      rename1`v_to_list (Conv tag vs1) = NONE`
      \\ Cases_on`vs1` \\ fs[patSemTheory.v_to_list_def]
      \\ rename1`v_to_list (Conv tag (_::vs1))`
      \\ Cases_on`vs1` \\ fs[patSemTheory.v_to_list_def]
      \\ rename1`v_to_list (Conv tag (_::_::vs1))`
      \\ Cases_on`vs1` \\ fs[patSemTheory.v_to_list_def]
      \\ rveq \\ fs[patSemTheory.v_to_list_def]
      \\ IF_CASES_TAC \\ fs[]
      \\ qpat_x_assum`_ = NONE`mp_tac
      \\ CASE_TAC \\ fs[]
      \\ imp_res_tac v_to_list_v_rel_none \\ fs[] >> NO_TAC) >>
    TRY (
      rename1`v_to_list (Conv tag vs1) = SOME _` >>
      `v_rel (Conv tag vs1) (Conv tag vs2)`
      by ( simp[Once v_rel_cases] ) >>
      imp_res_tac v_to_list_v_rel >> fs[] >>
      imp_res_tac vs_to_string_v_rel >> fs[] >> NO_TAC) >>
    TRY (
      rename1`v_to_list (Conv tag vs1) = SOME _` >>
      `v_rel (Conv tag vs1) (Conv tag vs2)`
      by ( simp[Once v_rel_cases] ) >>
      imp_res_tac v_to_list_v_rel >> fs[] >>
      imp_res_tac vs_to_string_v_rel >> fs[] >> NO_TAC) >>
    TRY (
      rename1`v_to_char_list (Conv tag vs1) = NONE`
      \\ Cases_on`vs1` \\ fs[patSemTheory.v_to_char_list_def]
      \\ rename1`v_to_char_list (Conv tag (c::vs1)) = NONE`
      \\ Cases_on`c` \\ fs[Once v_rel_cases,patSemTheory.v_to_char_list_def]
      \\ rename1`v_to_char_list (Conv tag (Litv l::vs1))`
      \\ Cases_on`l` \\ fs[patSemTheory.v_to_char_list_def]
      \\ Cases_on`vs1` \\ rfs[patSemTheory.v_to_char_list_def]
      \\ rename1`v_to_char_list (Conv tag (_::_::vs1))`
      \\ Cases_on`vs1` \\ fs[patSemTheory.v_to_char_list_def]
      \\ rveq \\ fs[patSemTheory.v_to_char_list_def]
      \\ IF_CASES_TAC \\ fs[]
      \\ qpat_x_assum`_ = NONE`mp_tac
      \\ CASE_TAC \\ fs[]
      \\ imp_res_tac v_to_char_list_v_rel_none
      \\ fs[] >> NO_TAC) >>
    rw[] \\ fs[] \\ rfs[]
    \\ imp_res_tac do_eq_list_v_rel \\ fs[]
    \\ TRY CASE_TAC \\ fs[]
    \\ fs[LIST_REL_EL_EQN,OPTREL_def]
    \\ res_tac \\ fs[store_v_same_type_def,sv_rel_cases] \\ fs[]
    \\ metis_tac[NOT_SOME_NONE]) >>
  Cases_on `op = (Op ListAppend)`
  >-
   (fs [] \\ rveq
    \\ pop_assum mp_tac
    \\ fs [patSemTheory.do_app_def]
    \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac v_to_list_v_rel_none
    \\ imp_res_tac v_to_list_v_rel \\ rfs [] \\ rw []
    \\ metis_tac [list_to_v_APPEND, list_to_v_v_rel])
  \\ qpat_x_assum `do_app _ _ _ = _` (strip_assume_tac o SIMP_RULE std_ss [patSemTheory.do_app_cases]) >>
  rw[patSemTheory.do_app_def] >>
  rfs[] >>
  fs[store_alloc_def,store_lookup_def,store_assign_def] >> rw[] >>
  fs[state_rel_def] >>
  TRY (
    fs[LIST_REL_EL_EQN,OPTREL_def]
    \\ res_tac \\ fs[sv_rel_cases] \\ fs[] \\ rw[]
    \\ NO_TAC ) >>
  TRY (
    rename1`patSem$v_to_list v1 = SOME _` >>
    imp_res_tac v_to_list_v_rel >> fs[] >>
    imp_res_tac vs_to_string_v_rel >> fs[] >>
    fs[LIST_REL_EL_EQN] >>
    simp[Once v_rel_cases,LIST_REL_EL_EQN] >> NO_TAC) >>
  TRY (
    rename1`v_to_char_list v1 = SOME _` >>
    imp_res_tac v_to_char_list_v_rel >> fs[] >> NO_TAC ) >>
  TRY (
    qpat_x_assum`v_rel _ _`mp_tac
    \\ simp[Once v_rel_cases] \\ strip_tac \\ fs[]
    \\ fs[LIST_REL_EL_EQN] \\ NO_TAC ) >>
  TRY (
    rename1`patSem$do_eq _ _`
    \\ imp_res_tac do_eq_v_rel \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rw[] \\ NO_TAC ) >>
  fs[LIST_REL_EL_EQN,OPTREL_def,EL_LUPDATE,LENGTH_REPLICATE,EL_REPLICATE] >>
  res_tac >> fs[sv_rel_cases] >> rfs[] >> fs[LIST_REL_EL_EQN,EL_LUPDATE,store_v_same_type_def] >>
  rw[EL_LUPDATE] \\ rw[EL_LUPDATE,EL_APPEND_EQN,EL_REPLICATE] >> rw[]
  \\ metis_tac[]
QED

(* some NoRun things for exp_rel, v_rel, state_rel etc *)

Theorem exp_rel_NoRun:
   !a b R x y.
     exp_rel a b R x y ==> NoRun x ==> NoRun y
Proof
  ho_match_mp_tac exp_rel_ind \\ rw [NoRun_def, EVERY_EL, LIST_REL_EL_EQN]
QED

Theorem LIST_REL_exp_rel_NoRun:
   !es1 es2 a b R.
     LIST_REL (exp_rel a b R) es1 es2 /\ EVERY NoRun es1
     ==>
     EVERY NoRun es2
Proof
  Induct \\ rw [] \\ fs [EVERY_DEF] \\ metis_tac [exp_rel_NoRun]
QED

Theorem env_rel_NoRun_v:
   !env1 env2 R k1 k2.
     env_rel R env1 env2 (LENGTH env1) (LENGTH env2) /\
     EVERY NoRun_v env1
     ==>
     EVERY NoRun_v env2
Proof
   Induct \\ rw [] \\ fs [env_rel_def]
QED

Theorem v_rel_NoRun_v:
   !x y. v_rel x y ==> (NoRun_v x ==> NoRun_v y)
Proof
  ho_match_mp_tac v_rel_ind \\ rw [v_rel_cases]
  \\ TRY (fs [NoRun_v_def, LIST_REL_EL_EQN, EVERY_EL] \\ NO_TAC)
  \\ metis_tac [NoRun_v_def, ETA_AX, exp_rel_NoRun, LIST_REL_exp_rel_NoRun]
QED

val sv_rel_NoRun_store_v = Q.prove (
  `!R x y.
   sv_rel R x y ==>
   (!x y. R x y ==> NoRun_v x ==> NoRun_v y) ==>
   NoRun_store_v x ==> NoRun_store_v y`,
  ho_match_mp_tac sv_rel_ind \\ rw [] \\ fs []
  \\ fs [NoRun_store_v_def, LIST_REL_EL_EQN, EVERY_EL] \\ rw []
  \\ metis_tac []);

Theorem sv_rel_v_rel_NoRun:
   sv_rel v_rel x y ==> NoRun_store_v x ==> NoRun_store_v y
Proof
  metis_tac [sv_rel_NoRun_store_v, v_rel_NoRun_v]
QED

Theorem sv_rel_sym:
   !R x y. (!x y. R x y ==> R y x) ==> sv_rel R x y ==> sv_rel R y x
Proof
  ho_match_mp_tac sv_rel_ind
  \\ rw [sv_rel_cases,LIST_REL_EL_EQN]
QED

Theorem state_rel_NoRun:
   state_rel s1 s2 ==> (NoRun_state s1 <=> NoRun_state s2)
Proof
  rw [state_rel_def, NoRun_state_def]
  \\ eq_tac \\ rw [] \\ fs []
  \\ TRY
   (fs [EVERY_EL, LIST_REL_EL_EQN] \\ rw []
    \\ rpt (first_x_assum (qspec_then `n` mp_tac))
    \\ fs [OPTREL_def] \\ rw []
    \\ imp_res_tac v_rel_sym
    \\ imp_res_tac v_rel_NoRun_v \\ fs []
    \\ NO_TAC)
  \\ pop_assum kall_tac
  \\ qhdtm_x_assum `LIST_REL` kall_tac
  \\ rpt (qpat_x_assum `_ = _` kall_tac)
  \\ fs [LIST_REL_EL_EQN, EVERY_EL] \\ rw []
  \\ rpt (first_x_assum (qspec_then `n` mp_tac)) \\ rw [] \\ fs []
  \\ metis_tac [sv_rel_v_rel_NoRun, sv_rel_sym, v_rel_sym]
QED

Theorem evaluate_exp_rel:
   (∀env1 ^s1 es1 s'1 r1.
     evaluate env1 s1 es1 = (s'1,r1) /\
     EVERY NoRun es1 /\ EVERY NoRun_v env1 /\ NoRun_state s1
     ==>
     ∀env2 s2 es2.
       LIST_REL (exp_rel (LENGTH env1) (LENGTH env2) (env_rel v_rel env1 env2)) es1 es2 /\
       EVERY NoRun_v env2 /\
       state_rel s1 s2 ⇒
       ∃s'2 r2.
         evaluate env2 s2 es2 = (s'2,r2) ∧
         state_rel s'1 s'2 ∧
         result_rel (LIST_REL v_rel) v_rel r1 r2)
Proof
  ho_match_mp_tac patSemTheory.evaluate_ind >> fs [NoRun_def] >>
  strip_tac >- ( srw_tac[][patSemTheory.evaluate_def] >> srw_tac[][]) >>
  strip_tac >- (
    rw [patSemTheory.evaluate_def,PULL_EXISTS]
    \\ rfs [] \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac evaluate_sing  \\ rw [] \\ fs []
    \\ qmatch_asmsub_rename_tac `evaluate env1 s3 (e2::es)`
    \\ `NoRun_state s3` by (drule (GEN_ALL evaluate_NoRun) \\ fs []) \\ fs []
    \\ TRY
     (first_x_assum drule \\ fs []
      \\ rpt (disch_then drule) \\ rw [] \\ fs []
      \\ res_tac \\ fs [] \\ rw [] \\ fs [])
    \\ asm_exists_tac \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ res_tac \\ fs [] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_sing >>
    metis_tac[HD,LIST_REL_def]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    every_case_tac >> full_simp_tac(srw_ss())[PULL_EXISTS] >> rpt var_eq_tac >> simp[] >> rev_full_simp_tac(srw_ss())[] >>
    res_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`v_rel v1 v2` >>
    qmatch_assum_rename_tac`exp_rel _ _ _ e12 e22` >>
    qmatch_assum_abbrev_tac`state_rel s3 s4` >> rev_full_simp_tac(srw_ss())[] >>
    sg `NoRun_v v1 /\ NoRun_state s3` >- (imp_res_tac evaluate_NoRun \\ fs []) >> fs [] >>
    first_x_assum(qspecl_then[`v2::env2`,`s4`,`e22`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    impl_tac >- ( metis_tac[exp_rel_mono,env_rel_cons, v_rel_NoRun_v]) >>
    srw_tac[][] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS,pair_case_eq] >> fs[] >>
    fs [EVERY_REVERSE, ETA_AX] >>
    imp_res_tac EVERY2_REVERSE >>
    first_x_assum drule \\ disch_then drule \\ strip_tac \\ fs[] \\
    every_case_tac \\ fs[] \\ rveq \\ fs[v_rel_cases] >>
    res_tac \\ fs [] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[env_rel_def] >>
    fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def] >>
    srw_tac[][v_rel_cases,ADD1] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    fs [EVERY_REVERSE, ETA_AX] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th) o MATCH_MP EVERY2_REVERSE)) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> full_simp_tac(srw_ss())[] >>
    rveq >>
    qmatch_assum_rename_tac`evaluate env1 s1 _ = (_,r)` >>
    res_tac >> fs [] >> rw [] >> fs [] >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[] >- srw_tac[][] >>
    imp_res_tac LIST_REL_exp_rel_NoRun >>
    reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> fs [] >> rfs [] >>
    imp_res_tac EVERY2_REVERSE
    >- (
      imp_res_tac do_app_v_rel >>
      last_x_assum(qspec_then`op`mp_tac) >>
      srw_tac[][OPTREL_def] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
    imp_res_tac do_opapp_v_rel >>
    pop_assum kall_tac >> pop_assum mp_tac >>
    srw_tac[][OPTREL_def] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    first_assum(split_uncurry_arg_tac o rator o concl) >> full_simp_tac(srw_ss())[] >>
    first_assum(split_uncurry_arg_tac o concl) >> full_simp_tac(srw_ss())[] >>
    imp_res_tac state_rel_clock >> full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
    last_x_assum mp_tac >>
    impl_tac >- (
      imp_res_tac do_opapp_NoRun >> fs [EVERY_REVERSE] >> rfs [] >>
      sg `EVERY NoRun_v a` >- (
        rw [EVERY_EL] >> fs [LIST_REL_EL_EQN] >>
        last_x_assum (qspec_then `n` mp_tac) >>
        fs [] >> rw [] >>
        irule v_rel_NoRun_v >> fs [] >>
        qexists_tac `EL n a` >> fs [] >>
        qpat_x_assum `_ = (_, Rval a)` assume_tac >>
        drule (GEN_ALL evaluate_NoRun) >>
        fs [EVERY_REVERSE] >>
        pop_assum mp_tac >>
        drule (GEN_ALL evaluate_NoRun) >>
        fs [EVERY_REVERSE] >>
        imp_res_tac state_rel_NoRun >> fs [] >>
        rw [EVERY_EL] ) >>
      fs [] >>
      drule (GEN_ALL evaluate_NoRun) >>
      fs [EVERY_REVERSE] >>
      pop_assum mp_tac >>
      drule (GEN_ALL evaluate_NoRun) >>
      fs [EVERY_REVERSE] >>
      imp_res_tac state_rel_NoRun >> fs [] >>
      rw [] >>
      metis_tac [NoRun_state_dec_clock] ) >>
    strip_tac >>
    pop_assum match_mp_tac >>
    imp_res_tac state_rel_dec_clock >>
    srw_tac[][] >>
    qpat_x_assum `_ = (_, Rval a)` assume_tac >>
    drule (GEN_ALL evaluate_NoRun) >>
    fs [EVERY_REVERSE] >>
    pop_assum mp_tac >>
    drule (GEN_ALL evaluate_NoRun) >>
    fs [EVERY_REVERSE] >>
    rw [] >>
    sg `NoRun_state s2` >- metis_tac [state_rel_NoRun] >> fs [] >>
    metis_tac [do_opapp_NoRun, EVERY_REVERSE] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> full_simp_tac(srw_ss())[] >>
    res_tac >> fs [] >> rw [] >> fs [] >>
    qmatch_assum_rename_tac`evaluate env1 s1 _ = (_,r)` >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>> srw_tac[][] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[patSemTheory.do_if_def] >>
    qpat_x_assum `evaluate env1 _ _ = _` assume_tac >>
    drule (GEN_ALL evaluate_NoRun) >> fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    IF_CASES_TAC >>full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >>full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> full_simp_tac(srw_ss())[] >>
    res_tac >> fs [] >> rw [] >>
    qmatch_assum_rename_tac`evaluate env1 s1 _ = (_,r)` >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>> srw_tac[][] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[] >>
    qpat_x_assum `evaluate env1 _ _ = _` assume_tac >>
    drule (GEN_ALL evaluate_NoRun) >> fs [] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    first_x_assum match_mp_tac >> fs [] >>
    simp[ADD1] >> metis_tac[exp_rel_mono,env_rel_cons, v_rel_NoRun_v]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> full_simp_tac(srw_ss())[] >>
    res_tac >> fs [] >> rw [] >> fs [] >>
    qmatch_assum_rename_tac`evaluate env1 s1 _ = (_,r)` >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>> srw_tac[][] >>
    res_tac >> fs [] >> rw [] >> fs [] >>
    qpat_x_assum `evaluate env1 _ _ = _` assume_tac >>
    drule (GEN_ALL evaluate_NoRun) >> fs []) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    srw_tac[][Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[patSemTheory.evaluate_def,PULL_EXISTS] >>
    last_x_assum mp_tac >>
    impl_tac >- (irule build_rec_env_NoRun >> fs [ETA_AX] ) >>
    strip_tac >>
    pop_assum match_mp_tac >> simp[] >>
    reverse conj_tac >- (
      irule build_rec_env_NoRun >> fs [ETA_AX] >>
      imp_res_tac LIST_REL_exp_rel_NoRun ) >>
    match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
    simp[env_rel_def,patSemTheory.build_rec_env_def] >> fs[] >>
    HINT_EXISTS_TAC >> simp[bindn_thm,GSYM bindn_def] >>
    imp_res_tac EVERY2_LENGTH >>
    srw_tac[][] >> simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
    fsrw_tac[ARITH_ss][env_rel_def] >>
    simp[Once v_rel_cases])
QED

val bvs_V_def = Define`
  bvs_V bvs1 bvs2 V ⇔
  ∀x k1 k2.
      find_index (SOME x) bvs1 0 = SOME k1 ∧
      find_index (SOME x) bvs2 0 = SOME k2
      ⇒ V k1 k2`

val bind_bvs_V_NONE = Q.prove(
  `∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (NONE::bvs1) (NONE::bvs2) (bind V)`,
  srw_tac[][bvs_V_def,bind_thm] >>
  imp_res_tac find_index_is_MEM >>
  imp_res_tac find_index_MEM >>
  ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
  simp[] >>
  Cases_on`k1=0`>>simp[]>>
  Cases_on`k2=0`>>simp[]>>
  rpt strip_tac >>
  first_x_assum match_mp_tac >>
  full_simp_tac(srw_ss())[find_index_def] >>
  full_simp_tac(srw_ss())[Once find_index_shift_0] >>
  metis_tac[])

val bind_bvs_V_SOME = Q.prove(
  `∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (SOME x::bvs1) (SOME x::bvs2) (bind V)`,
  srw_tac[][bvs_V_def,bind_thm] >>
  imp_res_tac find_index_is_MEM >>
  imp_res_tac find_index_MEM >>
  ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
  simp[] >>
  Cases_on`k1=0`>>simp[]>>
  Cases_on`k2=0`>>simp[]>>
  srw_tac[][] >> TRY (
    spose_not_then strip_assume_tac >>
    full_simp_tac(srw_ss())[find_index_def] >> NO_TAC) >>
  first_x_assum match_mp_tac >>
  full_simp_tac(srw_ss())[find_index_def] >> full_simp_tac(srw_ss())[] >>
  last_x_assum mp_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[Once find_index_shift_0] >>
  metis_tac[])

Theorem bind_bvs_V:
   ∀x bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (x::bvs1) (x::bvs2) (bind V)
Proof
  Cases >> metis_tac[bind_bvs_V_NONE,bind_bvs_V_SOME]
QED

Theorem bindn_bvs_V:
   ∀ls n bvs1 bvs2 V.
     bvs_V bvs1 bvs2 V ∧ n = LENGTH ls ⇒
     bvs_V (ls++bvs1) (ls++bvs2) (bindn n V)
Proof
  Induct >> simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  metis_tac[bind_bvs_V,bindn_def]
QED

val exp_rel_Con =
  SIMP_RULE(srw_ss())[](Q.SPECL[`z1`,`z2`,`V`,`Con _ X Y`]exp_rel_cases)

Theorem exp_rel_isBool:
   exp_rel z1 z2 V e e' ⇒ (isBool b e ⇔ isBool b e')
Proof
  rw[Once exp_rel_cases] \\ fs[] \\
  CASE_TAC \\ fs[] \\ fs[]
QED

Theorem exp_rel_sIf:
   exp_rel z1 z2 V (If t e1 e2 e3) (If t f1 f2 f3) ⇒
    exp_rel z1 z2 V (sIf t e1 e2 e3) (sIf t f1 f2 f3)
Proof
  simp[Once exp_rel_cases] \\ strip_tac \\
  simp_tac std_ss [sIf_def] \\
  simp_tac std_ss [Q.SPECL[`e2`,`f2`](Q.GENL[`e`,`e'`]exp_rel_isBool) |> UNDISCH] \\
  simp_tac std_ss [Q.SPECL[`e3`,`f3`](Q.GENL[`e`,`e'`]exp_rel_isBool) |> UNDISCH] \\
  IF_CASES_TAC \\ simp[] \\
  Cases_on`∃tr t. e1 = Con tr t []` >- (
    pop_assum strip_assume_tac \\
    last_x_assum mp_tac \\
    simp[Once exp_rel_cases] \\
    rw[] ) \\
  qmatch_abbrev_tac`exp_rel z1 z2 V ea eb` >>
  `ea = If t e1 e2 e3` by (
    Cases_on`e1`>>fs[Abbr`ea`]>>
    BasicProvers.CASE_TAC>>fs[] \\
    BasicProvers.CASE_TAC>>fs[]) >>
  `eb = If t f1 f2 f3` by (
    Cases_on`f1`>>fs[Abbr`eb`]>>
    BasicProvers.CASE_TAC>>srw_tac[][] >>
    TRY(BasicProvers.CASE_TAC>>srw_tac[][]) >>
    pop_assum mp_tac >> simp[Once exp_rel_cases]) >>
  simp[Once exp_rel_cases]
QED

Theorem exp_rel_pure:
   ∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
    (pure e1 ⇔ pure e2)
Proof
  ho_match_mp_tac (theorem"exp_rel_strongind") >>
  simp[pure_def] >>
  srw_tac[][EVERY_MEM,EVERY2_EVERY,EQ_IMP_THM] >>
  rev_full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
  rev_full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] >>
  full_simp_tac(srw_ss())[] >> srw_tac[][] >> metis_tac[]
QED

Theorem exp_rel_imp_ground:
   ∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
      ∀n. (∀k1 k2. k1 ≤ n ⇒ (V k1 k2 ⇔ (k1 = k2))) ∧ ground n e1 ⇒ ground n e2
Proof
  ho_match_mp_tac exp_rel_ind >>
  simp[] >> srw_tac[][] >>
  TRY (
    first_x_assum match_mp_tac >>
    simp[bind_thm] >>
    srw_tac[][] >> simp[] >> NO_TAC) >>
  TRY (DECIDE_TAC) >>
  rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
  full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
  rev_full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] >>
  full_simp_tac(srw_ss())[arithmeticTheory.LESS_OR_EQ] >>
  res_tac >> srw_tac[][]
QED

Theorem bindn_0:
   ∀V. bindn 0 V = V
Proof
  srw_tac[][bindn_def]
QED
val _ = export_rewrites["bindn_0"]

Theorem bind_bindn:
   (bind (bindn n V) = bindn (SUC n) V) ∧
    (bindn n (bind V) = bindn (SUC n) V)
Proof
  conj_tac >- simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  simp[bindn_def,arithmeticTheory.FUNPOW]
QED
val _ = export_rewrites["bind_bindn"]

Theorem exp_rel_unbind:
   ∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
      ∀k n m U.
        V = bindn n U ∧ n ≤ z1 ∧ n ≤ z2 ∧
        ground k e1 ∧ ground k e2 ∧
        k ≤ n-m ∧ m ≤ n
        ⇒
        exp_rel (z1-m) (z2-m) (bindn (n-m) U) e1 e2
Proof
  ho_match_mp_tac exp_rel_ind >>
  simp[] >> srw_tac[][] >>
  simp[Once exp_rel_cases] >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  TRY (
      simp[arithmeticTheory.ADD1] >>
      first_x_assum match_mp_tac >>
      simp[arithmeticTheory.ADD1] >>
      metis_tac[]) >>
  TRY (
    first_x_assum(qspecl_then[`k+1`,`SUC n`,`m`,`U`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    NO_TAC) >>
  TRY (
    rev_full_simp_tac(srw_ss())[EVERY2_EVERY,EVERY_MEM] >>
    full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
    rev_full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] >>
    metis_tac[]) >>
  qpat_x_assum`bindn n _ k1 k2`mp_tac >>
  simp[bindn_thm] >> srw_tac[][]
QED

Theorem exp_rel_sLet:
   exp_rel z1 z2 V (Let t e1 e2) (Let t f1 f2) ⇒
    exp_rel z1 z2 V (sLet t e1 e2) (sLet t f1 f2)
Proof
  simp[Once exp_rel_cases] \\ strip_tac \\
  Cases_on`∃t. e2 = Var_local t 0` >- (
    pop_assum strip_assume_tac \\
    qhdtm_x_assum`exp_rel`mp_tac \\
    simp[Once exp_rel_cases] \\ strip_tac \\
    simp[sLet_def] \\
    CASE_TAC \\ simp[] \\
    fs[bind_thm] ) \\
  `∀t. f2 ≠ Var_local t 0` by (
    spose_not_then strip_assume_tac \\ fs[] \\
    qhdtm_x_assum`exp_rel`mp_tac \\
    simp[Once exp_rel_cases] \\
    spose_not_then strip_assume_tac \\ fs[] \\
    fs[bind_thm] ) \\
  `sLet t e1 e2 = if ground 0 e2 then if pure e1 then e2 else Seq t e1 e2 else Let t e1 e2`
   by (simp[sLet_def] \\ Cases_on`e2` \\ fs[] \\ CASE_TAC \\ fs[] ) \\
  `sLet t f1 f2 = if ground 0 f2 then if pure f1 then f2 else Seq t f1 f2 else Let t f1 f2`
   by (simp[sLet_def] \\ Cases_on`f2` \\ fs[] \\ CASE_TAC \\ fs[] ) \\
  Cases_on`ground 0 e2` >- (
    `ground 0 f2` by (
      match_mp_tac(MP_CANON exp_rel_imp_ground) \\
      asm_exists_tac \\ simp[] \\
      simp[bind_thm] ) \\
    fs[] \\
    `exp_rel z1 z2 V e2 f2` by (
      qspecl_then[`z1+1`,`z2+1`,`bind V`,`e2`,`f2`]mp_tac exp_rel_unbind >> simp[] >>
      disch_then(qspecl_then[`0`,`1`,`1`,`V`]mp_tac) >>
      simp[bindn_def] ) \\
    imp_res_tac exp_rel_pure \\
    IF_CASES_TAC \\ fs[] \\
    simp[Once exp_rel_cases] ) \\
  `¬ground 0 f2` by (
    strip_tac \\
    qpat_x_assum`¬_`mp_tac \\
    simp[] \\
    match_mp_tac(MP_CANON exp_rel_imp_ground) \\
    imp_res_tac exp_rel_sym \\
    asm_exists_tac \\ simp[] \\
    simp[bind_thm,relationTheory.inv_DEF] ) \\
  fs[] \\
  simp[Once exp_rel_cases]
QED

Theorem ground_sIf:
   ground n (If t e1 e2 e3) ⇒
    ground n (sIf t e1 e2 e3)
Proof
  srw_tac[][sIf_def] >>
  Cases_on`e1`>> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem ground_inc:
   (∀e n. ground n e ⇒ ∀m. n ≤ m ⇒ ground m e) ∧
    (∀es n. ground_list n es ⇒ ∀m. n ≤ m ⇒ ground_list m es)
Proof
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[] >> srw_tac[][] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[arithmeticTheory.LE_ADD_RCANCEL]
QED

Theorem ground_sLet:
   ground n (Let t e1 e2) ⇒
    ground n (sLet t e1 e2)
Proof
  simp[sLet_def] \\ strip_tac \\
  Cases_on`∃t. e2 = Var_local t 0` >- fs[] \\
  qsuff_tac`ground n (if ground 0 e2 then if pure e1 then e2 else Seq t e1 e2 else Let t e1 e2)`
  >- ( Cases_on`e2` \\ fs[] \\ CASE_TAC \\ fs[] ) \\ rw[] \\
  match_mp_tac(MP_CANON(CONJUNCT1 ground_inc))>>
  qexists_tac`0`>>simp[]
QED

Theorem ground_Let_Els:
   ∀k m n t e.
    ground (n+k) e ∧ m < n ⇒
    ground n (Let_Els t m k e)
Proof
  Induct >> simp[Let_Els_def] >>
  srw_tac[][] >>
  match_mp_tac ground_sLet >>
  simp[] >>
  first_x_assum match_mp_tac >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]
QED

Theorem compile_pat_ground:
   (∀t p. ground 1 (compile_pat t p)) ∧
    (∀t n ps. ground (n + LENGTH ps) (compile_pats t n ps))
Proof
  ho_match_mp_tac compile_pat_ind >>
  simp[compile_pat_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_sIf >>
    simp[] >>
    match_mp_tac ground_Let_Els >>
    simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
    HINT_EXISTS_TAC >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_sLet >> simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
    qexists_tac`1`>>simp[] ) >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac ground_sIf >> simp[] >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  match_mp_tac ground_sLet >> simp[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
  HINT_EXISTS_TAC >> simp[]
QED

Theorem ground_exp_rel_refl:
   (∀e n. ground n e ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ exp_rel z1 z2 (bindn n V) e e) ∧
    (∀es n. ground_list n es ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ EVERY2 (exp_rel z1 z2 (bindn n V)) es es)
Proof
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[] >> srw_tac[][] >>
  simp[Once exp_rel_cases] >> TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[arithmeticTheory.ADD1] >>
    NO_TAC) >>
  simp[bindn_thm]
QED

Theorem compile_row_acc:
   (∀t Nbvs p bvs1 N. Nbvs = N::bvs1 ⇒
       ∀bvs2 r1 n1 f1 r2 n2 f2.
         compile_row t (N::bvs1) p = (r1,n1,f1) ∧
         compile_row t (N::bvs2) p = (r2,n2,f2) ⇒
         n1 = n2 ∧ f1 = f2 ∧
         ∃ls. r1 = ls ++ bvs1 ∧
              r2 = ls ++ bvs2 ∧
              LENGTH ls = SUC n1) ∧
    (∀t bvsk0 n k ps bvsk N bvs1.
        bvsk0 = bvsk ++ (N::bvs1) ∧ LENGTH bvsk = n ⇒
      ∀bvs2 r1 n1 f1 r2 n2 f2.
        compile_cols t (bvsk++(N::bvs1)) n k ps = (r1,n1,f1) ∧
        compile_cols t (bvsk++(N::bvs2)) n k ps = (r2,n2,f2) ⇒
        n1 = n2 ∧ f1 = f2 ∧
        ∃ls. r1 = ls ++ bvsk ++ (N::bvs1) ∧
             r2 = ls ++ bvsk ++ (N::bvs2) ∧
             LENGTH ls = n1)
Proof
  ho_match_mp_tac compile_row_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> full_simp_tac(srw_ss())[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    srw_tac[][compile_row_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> full_simp_tac(srw_ss())[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    srw_tac[][compile_row_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> full_simp_tac(srw_ss())[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    srw_tac[][compile_row_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> simp[LENGTH_NIL] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac(srw_ss())[] >>
    simp_tac std_ss [compile_row_def] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac`ls++[N]` >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac(srw_ss())[] >>
    simp_tac std_ss [compile_row_def] >>
    simp[] >>
    `∃r1 n1 f1. compile_row (t§1) (NONE::N::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    full_simp_tac(srw_ss())[] >> rpt gen_tac >>
    `∃r2 n2 f2. compile_row (t§1) (NONE::N::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    full_simp_tac(srw_ss())[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum(qspec_then`N::bvs2`mp_tac) >>
    simp[] >> srw_tac[][] >> simp[] ) >>
  strip_tac >- srw_tac[][] >>
  strip_tac >- (
    rpt gen_tac >> simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[compile_row_def] ) >>
  strip_tac >- simp[compile_row_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >>
  simp_tac std_ss [compile_row_def] >>
  `∃r01 n01 f01. compile_row (t§1) (NONE::(bvsk ++ (N::bvs1))) p = (r01,n01,f01)` by simp[GSYM EXISTS_PROD] >>
  `∃r02 n02 f02. compile_row (t§1) (NONE::(bvsk ++ (N::bvs2))) p = (r02,n02,f02)` by simp[GSYM EXISTS_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  `∃r11 n11 f11. compile_cols (t§2) r01 (LENGTH bvsk + 1 + n01) (k+1) ps = (r11,n11,f11)` by simp[GSYM EXISTS_PROD] >>
  `∃r12 n12 f12. compile_cols (t§2) r02 (LENGTH bvsk + 1 + n02) (k+1) ps = (r12,n12,f12)` by simp[GSYM EXISTS_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  ntac 5 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum`∀X. Y`mp_tac >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 2 strip_tac >>
  disch_then(qspec_then`bvsk ++ N::bvs2`mp_tac) >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 3 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum`∀X. Y`mp_tac >>
  ntac 3 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 3 strip_tac >>
  disch_then(qspec_then`ls ++ bvsk`mp_tac) >>
  pop_assum mp_tac >>
  simp_tac (std_ss++listSimps.LIST_ss++ARITH_ss) [arithmeticTheory.ADD1] >>
  strip_tac >>
  disch_then(qspec_then`bvs2`mp_tac) >>
  ntac 2 (last_x_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss++ARITH_ss) [arithmeticTheory.ADD1] >>
  ntac 3 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[]
QED

Theorem compile_row_shift:
   (∀t bvs p bvs1 n1 f z1 z2 V e1 e2.
       compile_row t bvs p = (bvs1,n1,f) ∧ 0 < z1 ∧ 0 < z2 ∧ V 0 0 ∧ bvs ≠ [] ∧
       exp_rel (z1 + n1) (z2 + n1) (bindn n1 V) e1 e2
       ⇒
       exp_rel z1 z2 V (f e1) (f e2)) ∧
    (∀t bvs n k ps bvs1 n1 f z1 z2 V e1 e2.
       compile_cols t bvs n k ps = (bvs1,n1,f) ∧ bvs ≠ [] ∧ ps ≠ [] ∧
       n < z1 ∧ n < z2 ∧ V n n ∧
       exp_rel (z1 + n1) (z2 + n1) (bindn (n1) V) e1 e2
       ⇒
       exp_rel z1 z2 V (f e1) (f e2))
Proof
  ho_match_mp_tac compile_row_ind >>
  simp[compile_row_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rename1`compile_cols t bvs 0 0 ps` \\
    `∃bvs1 n1 f. compile_cols t bvs 0 0 ps = (bvs1,n1,f)` by simp[GSYM EXISTS_PROD] >>
    Cases_on`ps`>>full_simp_tac(srw_ss())[compile_row_def] >> srw_tac[][] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    `∃bvs1 n f. compile_row (t§1) (NONE::bvs) p = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    full_simp_tac(srw_ss())[] >>
    rpt gen_tac >> strip_tac >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    simp[Once exp_rel_cases] >>
    simp[Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    simp[bind_thm] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `∃bvs0 n0 f0. compile_row (t§1) (NONE::bvs) p = (bvs0,n0,f0)` by simp[GSYM EXISTS_PROD] >>
  full_simp_tac(srw_ss())[] >>
  `∃bvs2 n2 f2. compile_cols (t§2) bvs0 (n0+n+1) (k+1) ps = (bvs2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
  fsrw_tac[ARITH_ss][] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  match_mp_tac exp_rel_sLet >>
  simp[Once exp_rel_cases] >>
  simp[Once exp_rel_cases] >>
  simp[Once exp_rel_cases] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[bind_thm] >>
  Cases_on`ps=[]`>>full_simp_tac(srw_ss())[compile_row_def] >- (
    srw_tac[][] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] ) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  qspecl_then[`t§1`,`NONE::bvs`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >>
  simp[] >> disch_then(qspec_then`bvs`mp_tac) >> simp[] >>
  strip_tac >> Cases_on`bvs0`>>full_simp_tac(srw_ss())[] >>
  conj_tac >- simp[bindn_thm,arithmeticTheory.ADD1] >>
  full_simp_tac(srw_ss())[bindn_def,GSYM arithmeticTheory.FUNPOW_ADD,arithmeticTheory.ADD1] >>
  fsrw_tac[ARITH_ss][]
QED

Theorem compile_exp_shift:
   (∀bvs1 e z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_rel z1 z2 V (compile_exp bvs1 e) (compile_exp bvs2 e)) ∧
    (∀bvs1 es z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_rel z1 z2 V) (compile_exps bvs1 es) (compile_exps bvs2 es)) ∧
    (∀bvs1 funs z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧
       (z2 = SUC(LENGTH bvs2)) ∧
       (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_rel z1 z2 (bind V))
         (compile_funs bvs1 funs) (compile_funs bvs2 funs)) ∧
    (∀t Nbvs1 pes bvs1 z1 z2 bvs2 V.
       (Nbvs1 = NONE::bvs1) ∧
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧ (z2 = SUC(LENGTH bvs2)) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_rel z1 z2 (bind V) (compile_pes t (NONE::bvs1) pes) (compile_pes t (NONE::bvs2) pes))
Proof
  ho_match_mp_tac compile_exp_ind >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_bvs_V] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >>
    match_mp_tac exp_rel_sIf >>
    simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >> simp[Once exp_rel_cases] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[][] >> simp[Once exp_rel_cases] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[][] >>
    BasicProvers.CASE_TAC >- (
      full_simp_tac(srw_ss())[GSYM find_index_NOT_MEM] >>
      `¬MEM (SOME x) bvs2` by (
        full_simp_tac(srw_ss())[Once pred_setTheory.EXTENSION,MEM_FILTER] >>
        spose_not_then strip_assume_tac >>
        res_tac >> full_simp_tac(srw_ss())[] ) >>
      imp_res_tac find_index_NOT_MEM >>
      ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
      simp[] >>
      simp[Once exp_rel_cases] ) >>
    imp_res_tac find_index_is_MEM >>
    full_simp_tac(srw_ss())[Once pred_setTheory.EXTENSION,MEM_FILTER] >>
    res_tac >> full_simp_tac(srw_ss())[] >>
    imp_res_tac find_index_MEM >>
    ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
    srw_tac[][] >> simp[] >>
    simp[Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[bvs_V_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    srw_tac[][] >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`(SOME x)::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    full_simp_tac(srw_ss())[bvs_V_def] >>
    simp[find_index_def] >>
    srw_tac[][] >> srw_tac[][bind_def] >>
    imp_res_tac find_index_LESS_LENGTH >>
    Cases_on`k1`>>Cases_on`k2`>>full_simp_tac(srw_ss())[]>>
    simp[bind_def] >>
    full_simp_tac(srw_ss())[Once find_index_shift_0] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_bvs_V] ) >>
  strip_tac >- (
    srw_tac[][] >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`SOME x::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    match_mp_tac bind_bvs_V >> srw_tac[][] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >>
    simp[Once exp_rel_cases] >>
    full_simp_tac(srw_ss())[compile_funs_map] >>
    reverse conj_tac >- (
      qmatch_abbrev_tac`exp_rel z1 z2 V1 (compile_exp bvs10 e) (compile_exp bvs20 e)` >>
      last_x_assum (qspecl_then[`bvs20`,`V1`]mp_tac) >>
      unabbrev_all_tac >> simp[] >>
      disch_then match_mp_tac >>
      conj_tac >- (
        full_simp_tac(srw_ss())[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
        metis_tac[] ) >>
      match_mp_tac bindn_bvs_V >>
      simp[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(bvs20 = MAP f funs ++ bvs2)` >>
    qmatch_assum_abbrev_tac`Abbrev(bvs10 = MAP f funs ++ bvs1)` >>
    first_x_assum(qspecl_then[`bvs20`,`bindn (LENGTH funs) V`]mp_tac) >>
    unabbrev_all_tac >> simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    conj_tac >- (
      full_simp_tac(srw_ss())[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    match_mp_tac bindn_bvs_V >>
    simp[] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- ( srw_tac[][] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    srw_tac[][] >>
    last_x_assum(qspecl_then[`SOME x::bvs2`,`bind V`]mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    match_mp_tac bind_bvs_V >> srw_tac[][] ) >>
  strip_tac >- (
    srw_tac[][] >>
    qspecl_then[`t`,`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    `∃r1 n1 f1. compile_row t (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. compile_row t (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    simp[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspecl_then[`ls++bvs2`,`bindn (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`t`,`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
  strip_tac >- (
    srw_tac[][] >>
    match_mp_tac exp_rel_sIf >>
    simp[Once exp_rel_cases] >>
    conj_tac >- (
      qspecl_then[`compile_pat (t§2) p`,`1`]mp_tac(CONJUNCT1 ground_exp_rel_refl) >>
      simp[compile_pat_ground,bindn_def] ) >>
    `∃r1 n1 f1. compile_row (t§3) (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. compile_row (t§3) (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    qspecl_then[`t§3`,`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspecl_then[`ls++bvs2`,`bindn (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`t§3`,`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
   srw_tac[][]
QED

val lookup_find_index_SOME = Q.prove(
  `∀env. ALOOKUP env n = SOME v ⇒
      ∀m. ∃i. (find_index (SOME n) (MAP (SOME o FST) env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >> srw_tac[][find_index_def] >-
    (qexists_tac`0`>>simp[]) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[]);

val s = mk_var("s",
  ``flatSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``])

val pair_lemma = Q.prove(
  `(∀x y. p = (x,y) ⇒ Q x y) ⇔ (λ(x,y). Q x y) p`,
  srw_tac[][EQ_IMP_THM,UNCURRY]>>full_simp_tac(srw_ss())[])

val evaluate_flat_def = flatSemTheory.evaluate_def;
val evaluate_flat_cons = flatPropsTheory.evaluate_cons;
val evaluate_flat_sing = flatPropsTheory.evaluate_sing;
val evaluate_cons = patPropsTheory.evaluate_cons;
val evaluate_sing = patPropsTheory.evaluate_sing;

val compile_env_aux = Q.prove (
  `EVERY NoRun_v (MAP (compile_v o SND) env)`,
  rw [EVERY_MAP] \\ fs [compile_v_NoRun_v]);

Theorem compile_exp_evaluate:
   (∀env ^s exps ress. flatSem$evaluate env s exps = ress ⇒
    ¬env.check_ctor ∧ env.exh_pat ∧
    (SND ress ≠ Rerr (Rabort Rtype_error)) ⇒
    ∃ress4.
      evaluate
        (MAP (compile_v o SND) env.v)
        (compile_state (co: num -> 'c # dec list) cc s)
        (compile_exps (MAP (SOME o FST) env.v) exps) = ress4 ∧
      state_rel (compile_state co cc (FST ress)) (FST ress4) ∧
      result_rel (LIST_REL v_rel) v_rel (map_result compile_vs compile_v (SND ress)) (SND ress4)) ∧
   (∀env ^s v pes err_v res t. evaluate_match env s v pes err_v = res ⇒
    ¬env.check_ctor ∧ env.exh_pat ∧
    (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
    ∃res4.
      patSem$evaluate
        (compile_v v::(MAP (compile_v o SND) env.v))
        (compile_state co cc s)
        [compile_pes t (NONE::(MAP (SOME o FST) env.v)) pes] = res4 ∧
      state_rel (compile_state co cc (FST res)) (FST res4) ∧
      result_rel (LIST_REL v_rel) v_rel (map_result (MAP compile_v) compile_v (SND res)) (SND res4))
Proof
  ho_match_mp_tac flatSemTheory.evaluate_ind >>
  (* nil *)
  strip_tac >- ( srw_tac[][evaluate_flat_def] >> simp[patSemTheory.evaluate_def] ) >>
  (* cons *)
  strip_tac >- (
    rpt gen_tac >> simp[PULL_EXISTS] >>
    ntac 2 strip_tac >>
    Q.ISPECL_THEN[`e1`,`e2::es`,`s`]assume_tac(Q.GENL[`e`,`es`,`s`]evaluate_flat_cons) >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>-(
      strip_tac >> full_simp_tac(srw_ss())[] >>
      simp[Once evaluate_cons] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      simp[Once evaluate_cons] ) >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    Cases_on`r = Rerr (Rabort Rtype_error)`>>full_simp_tac(srw_ss())[] >>
    qpat_x_assum`flatSem$evaluate _ _ (_::_::_) = _`kall_tac >>
    simp[Once evaluate_cons] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    var_eq_tac >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    simp[Once evaluate_cons] >>
    qhdtm_x_assum`result_rel`mp_tac >>
    specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
    simp [compile_exp_NoRun, compile_state_NoRun, compile_env_aux] >>
    simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
    full_simp_tac(srw_ss())[PULL_EXISTS] >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    qmatch_assum_abbrev_tac`evaluate env5 s5 (e5::e6) = res5` >>
    qmatch_assum_abbrev_tac`state_rel s5 s6` >>
    disch_then(qspecl_then[`env5`,`s6`,`e5`,`e6`]mp_tac) >>
    simp[] >>
    impl_tac >- simp[Abbr`env5`,exp_rel_refl,env_rel_def, compile_env_aux] >>
    ntac 2 strip_tac >>
    unabbrev_all_tac >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
    metis_tac[EVERY2_APPEND_suff,LIST_REL_v_rel_trans,state_rel_trans,exc_rel_v_rel_trans]) >>
  (* Lit *)
  strip_tac >- (
    srw_tac[][patSemTheory.evaluate_def,evaluate_flat_def] >> full_simp_tac(srw_ss())[] ) >>
  (* Raise *)
  strip_tac >- (
    srw_tac[][patSemTheory.evaluate_def,evaluate_flat_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_flat_sing >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[]) >>
  (* Handle *)
  strip_tac >- (
    rpt gen_tac >>
    simp[patSemTheory.evaluate_def,evaluate_flat_def,PULL_EXISTS] >>
    ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    Cases_on`r`>>full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`er ≠ Rabort Rtype_error ⇒ _` >>
    Cases_on`er`>>full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    first_x_assum(qspec_then`exps § 2`strip_assume_tac) \\
    qhdtm_x_assum`result_rel`mp_tac >>
    specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
    simp [compile_state_NoRun, compile_exp_NoRun, compile_env_aux, compile_v_NoRun_v] >>
    simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
    full_simp_tac(srw_ss())[PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`evaluate (v5::env5) s5 [e5] = res5` >>
    qmatch_assum_rename_tac`v_rel v5 v6` >>
    qmatch_assum_rename_tac`state_rel s5 s6` >>
    disch_then(qspecl_then[`v6::env5`,`s6`,`e5`]mp_tac) >>
    impl_tac >- (
      simp[Abbr`env5`, compile_env_aux] >>
      reverse conj_tac >- metis_tac [compile_v_NoRun_v, v_rel_NoRun_v] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    strip_tac >>
    unabbrev_all_tac >> full_simp_tac(srw_ss())[] >>
    metis_tac[result_rel_LIST_v_v_rel_trans,state_rel_trans,compile_vs_map]) >>
  (* Con *)
  strip_tac >- (
    rpt gen_tac >>
    simp[patSemTheory.evaluate_def,evaluate_flat_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[compile_exps_reverse] >>
    srw_tac[][MAP_REVERSE,EVERY2_REVERSE,v_rel_cases]) >>
  (* Con *)
  strip_tac >- (
    rpt gen_tac >>
    simp[patSemTheory.evaluate_def,evaluate_flat_def] >>
    ntac 2 strip_tac \\ fs[] \\ rfs[]
    \\ fs[compile_exps_reverse]
    \\ CASE_TAC \\ fs[]
    \\ Cases_on`cn`
    \\ CASE_TAC \\ fs[patSemTheory.evaluate_def]
    \\ CASE_TAC \\ fs[] \\ rw[]
    \\ rw[v_rel_cases,EVERY2_REVERSE,MAP_REVERSE]) >>
  (* Var_local *)
  strip_tac >- (
    rpt gen_tac >>
    simp[evaluate_flat_def] >>
    ntac 2 strip_tac >> var_eq_tac >> full_simp_tac(srw_ss())[] >> pop_assum mp_tac >>
    BasicProvers.CASE_TAC >>
    imp_res_tac lookup_find_index_SOME >>
    first_x_assum(qspec_then`0`mp_tac) >>
    strip_tac >>
    simp[patSemTheory.evaluate_def] >>
    imp_res_tac find_index_LESS_LENGTH >>
    full_simp_tac(srw_ss())[] >> simp[EL_MAP] ) >>
  (* Fun *)
  strip_tac >- ( srw_tac[][patSemTheory.evaluate_def,evaluate_flat_def] >> full_simp_tac(srw_ss())[] ) >>
  (* App *)
  strip_tac >- (
    rpt gen_tac >>
    simp[patSemTheory.evaluate_def,evaluate_flat_def,PULL_EXISTS] >>
    ntac 2 strip_tac >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    Cases_on`r = Rerr (Rabort Rtype_error)`>>full_simp_tac(srw_ss())[] >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[] >- (
      full_simp_tac(srw_ss())[compile_exps_reverse] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] ) >>
    qmatch_assum_rename_tac`_ = (s',Rval vs)` >>
    Cases_on`op = Opapp` >> full_simp_tac(srw_ss())[] >- (
      Cases_on`do_opapp (REVERSE vs)`>>simp[] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac do_opapp >>
      full_simp_tac(srw_ss())[compile_exps_reverse] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
      first_assum(strip_assume_tac o MATCH_MP do_opapp_v_rel o MATCH_MP EVERY2_REVERSE) >>
      rev_full_simp_tac(srw_ss())[compile_vs_map,OPTREL_SOME,rich_listTheory.MAP_REVERSE] >>
      first_assum(split_uncurry_arg_tac o concl) >> full_simp_tac(srw_ss())[] >>
      IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- ( full_simp_tac(srw_ss())[state_rel_def,compile_state_def] ) >>
      qhdtm_x_assum`result_rel`mp_tac >>
      specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
      simp [compile_exp_NoRun, compile_env_aux, compile_v_NoRun_v, compile_state_NoRun] >>
      sg `EVERY NoRun_v v'` >- (
        fs [LIST_REL_EL_EQN, EVERY_EL] >>
        rw [] >>
        first_x_assum (qspec_then `n` mp_tac) >> fs [] >>
        strip_tac >>
        imp_res_tac v_rel_NoRun_v >> fs [compile_v_NoRun_v, EL_MAP] ) >>
      sg `EVERY NoRun_v env2` >- metis_tac [EVERY_REVERSE, do_opapp_NoRun] >>
      simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
      full_simp_tac(srw_ss())[PULL_EXISTS] >> strip_tac >>
      first_x_assum (fn th => first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
      full_simp_tac(srw_ss())[compile_state_dec_clock] >>
      imp_res_tac state_rel_dec_clock >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def,compile_state_def] >> full_simp_tac(srw_ss())[] >>
      metis_tac[state_rel_trans,result_rel_LIST_v_v_rel_trans]) >>
    TOP_CASE_TAC \\ rfs[] \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    fs[compile_exps_reverse] \\
    Q.ISPECL_THEN[`cc`,`co`]drule do_app >> strip_tac \\
    imp_res_tac EVERY2_REVERSE \\
    drule do_app_v_rel \\
    disch_then drule \\
    disch_then(qspec_then`Op op`mp_tac)  >>
    fs[MAP_REVERSE,OPTREL_SOME] >>
    strip_tac \\ fs[] \\
    pairarg_tac \\ fs[]) >>
  (* If *)
  strip_tac >-  (
    rpt gen_tac \\ ntac 2 strip_tac \\ fs[]
    \\ simp[evaluate_flat_def]
    \\ CASE_TAC \\ fs[]
    \\ ntac 2 strip_tac
    \\ DEEP_INTRO_TAC sIf_intro
    \\ simp[patSemTheory.evaluate_def]
    \\ CASE_TAC \\ fs[]
    \\ rveq
    \\ reverse CASE_TAC \\ fs[] \\ rfs[]
    >- ( rw[] \\ strip_tac \\ fs[] )
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC
    >- (
      fs[patSemTheory.do_if_def,flatSemTheory.do_if_def]
      \\ imp_res_tac evaluate_flat_sing
      \\ imp_res_tac evaluate_sing
      \\ fs[bool_case_eq]
      \\ rveq \\ fs[flatSemTheory.Boolv_def,v_rel_cases,patSemTheory.Boolv_def] )
    \\ qhdtm_x_assum`state_rel`mp_tac
    \\ specl_args_of_then ``patSem$evaluate``evaluate_exp_rel mp_tac
    \\ simp[compile_state_NoRun,compile_exp_NoRun,compile_env_aux]
    \\ simp[pair_lemma] >> pairarg_tac \\ fs[]
    \\ imp_res_tac evaluate_flat_sing
    \\ imp_res_tac patPropsTheory.evaluate_sing
    \\ rveq
    \\ fs[PULL_EXISTS]
    \\ disch_then (first_assum o mp_then Any mp_tac )
    \\ qmatch_goalsub_abbrev_tac`evaluate env1 _ [ex1]`
    \\ disch_then(qspecl_then[`env1`,`ex1`]mp_tac)
    \\ simp[Abbr`env1`,Abbr`ex1`,compile_env_aux]
    \\ impl_tac
    >- (
      fs[patSemTheory.do_if_def,flatSemTheory.do_if_def,bool_case_eq]
      \\ rw[]
      \\ fs[flatSemTheory.Boolv_def,patSemTheory.Boolv_def,v_rel_cases,
            backend_commonTheory.true_tag_def,backend_commonTheory.false_tag_def]
      \\ match_mp_tac (CONJUNCT1 exp_rel_refl)
      \\ rw[env_rel_def] )
    \\ ntac 2 strip_tac \\ fs[]
    \\ conj_tac >- metis_tac[state_rel_trans, result_rel_LIST_v_v_rel_trans]
    \\ strip_tac \\ fs[]) >>
  (* Mat *)
  strip_tac >- (
    simp[PULL_EXISTS,evaluate_flat_def] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    DEEP_INTRO_TAC sLet_intro >>
    simp[patSemTheory.evaluate_def] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[] >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    rename1`compile_pes (tr § 2) _ pes` \\
    first_x_assum(qspec_then`tr§2`strip_assume_tac) \\
    qhdtm_x_assum`result_rel`mp_tac >>
    specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
    simp [compile_exp_NoRun, compile_state_NoRun, compile_env_aux, compile_v_NoRun_v] >>
    simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
    full_simp_tac(srw_ss())[PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`evaluate (v5::env5) s5 [e5] = res5` >>
    imp_res_tac evaluate_flat_sing >>
    imp_res_tac patPropsTheory.evaluate_sing >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> var_eq_tac >>
    qmatch_assum_rename_tac`v_rel v5 v6` >>
    qmatch_assum_rename_tac`state_rel s5 s6` >>
    disch_then(qspecl_then[`v6::env5`,`s6`,`e5`]mp_tac) >>
    impl_tac >- (
      simp[Abbr`env5`, compile_env_aux] >>
      reverse conj_tac >- metis_tac [v_rel_NoRun_v, compile_v_NoRun_v] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    strip_tac >>
    unabbrev_all_tac >> full_simp_tac(srw_ss())[] >>
    strip_tac >>
    full_simp_tac(srw_ss())[EXT compile_vs_map] >>
    conj_tac >- metis_tac[result_rel_LIST_v_v_rel_trans,state_rel_trans] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
  (* Let *)
  strip_tac >- (
    simp[PULL_EXISTS,evaluate_flat_def] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`r ≠ Rerr (Rabort Rtype_error) ⇒ _` >>
    Cases_on`n`>>full_simp_tac(srw_ss())[libTheory.opt_bind_def] >- (
      simp[patSemTheory.evaluate_def] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>>
      qhdtm_x_assum`result_rel`mp_tac >>
      specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
      simp [compile_exp_NoRun, compile_v_NoRun_v, compile_env_aux, compile_state_NoRun] >>
      simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
      full_simp_tac(srw_ss())[PULL_EXISTS] >>
      simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
      metis_tac[result_rel_LIST_v_v_rel_trans,state_rel_trans,
                FST,SND,exp_rel_refl,env_rel_def,LENGTH_MAP,v_rel_refl,
                compile_v_NoRun_v,compile_env_aux]) >>
    DEEP_INTRO_TAC sLet_intro >>
    simp[patSemTheory.evaluate_def] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    reverse(Cases_on`r`)>>full_simp_tac(srw_ss())[]>- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    qhdtm_x_assum`result_rel`mp_tac >>
    specl_args_of_then``patSem$evaluate``evaluate_exp_rel mp_tac >>
    simp [compile_exp_NoRun, compile_v_NoRun_v, compile_env_aux, compile_state_NoRun] >>
    simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
    full_simp_tac(srw_ss())[PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`evaluate (v5::env5) s5 [e5] = res5` >>
    rpt var_eq_tac >>
    imp_res_tac patPropsTheory.evaluate_sing >>
    imp_res_tac evaluate_flat_sing >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`v_rel v5 v6` >>
    qmatch_assum_rename_tac`state_rel s5 s6` >>
    disch_then(qspecl_then[`v6::env5`,`s6`,`e5`]mp_tac) >>
    impl_tac >- (
      simp[Abbr`env5`, compile_env_aux] >>
      reverse conj_tac >- metis_tac [v_rel_NoRun_v, compile_v_NoRun_v] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    strip_tac >>
    unabbrev_all_tac >> full_simp_tac(srw_ss())[] >>
    strip_tac >>
    full_simp_tac(srw_ss())[EXT compile_vs_map] >>
    conj_tac >- metis_tac[result_rel_LIST_v_v_rel_trans,state_rel_trans] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
  (* Letrec *)
  strip_tac >- (
    rpt gen_tac >>
    simp[patSemTheory.evaluate_def,PULL_EXISTS,evaluate_flat_def] >>
    strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
    qpat_abbrev_tac`xx = evaluate _ _ _` >>
    qho_match_abbrev_tac`P xx ∧ Q xx` >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_abbrev_tac`P (evaluate a b c)` >>
    qmatch_assum_abbrev_tac`Abbrev(xx = evaluate a' b c')` >>
    `a = a'` by (
      unabbrev_all_tac >>
      full_simp_tac(srw_ss())[patSemTheory.build_rec_env_def,flatPropsTheory.build_rec_env_merge,compile_funs_map] >>
      srw_tac[][LIST_EQ_REWRITE,EL_MAP,UNCURRY,compile_funs_map] >>
      imp_res_tac find_index_ALL_DISTINCT_EL >>
      first_x_assum(qspec_then`x`mp_tac) >>
      impl_tac >- simp[] >>
      disch_then(qspec_then`0`mp_tac) >>
      asm_simp_tac(std_ss)[EL_MAP] >>
      simp[libTheory.the_def]) >>
    `c = c'` by (
      unabbrev_all_tac >>
      simp[flatPropsTheory.build_rec_env_merge] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[FUN_EQ_THM,FORALL_PROD] ) >>
    metis_tac[]) >>
  (* match nil *)
  strip_tac >- ( rw[evaluate_flat_def] >> fs[] ) >>
  (* match cons *)
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[evaluate_flat_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    reverse(BasicProvers.CASE_TAC) >> full_simp_tac(srw_ss())[] >- (
      ntac 2 strip_tac >>
      Cases_on`pes`>>simp[]>>full_simp_tac(srw_ss())[]
      >|[ALL_TAC,
        DEEP_INTRO_TAC sIf_intro >>
        simp[patSemTheory.evaluate_def] >>
        split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
        Q.ISPECL_THEN[`co`,`cc`]mp_tac
          (Q.GENL[`co`,`cc`](CONJUNCT1 compile_pat_correct)) >>
        disch_then(qspecl_then[`t § 2`,`p`,`v`,`env`,`s`,`[]`]mp_tac) >> simp[] >>
        strip_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> pop_assum kall_tac >>
        simp[patSemTheory.do_if_def] >>
        qspec_tac(`t§3`,`t`) \\ gen_tac]
      >>> USE_SG_THEN (fn th => metis_tac[th]) 2 1 >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_rename_tac `_ = (bvs,_,f)` >>
      full_simp_tac(srw_ss())[Once(CONJUNCT1 flatPropsTheory.pmatch_nil)] >>
      Cases_on`pmatch env s.refs p v []`>>full_simp_tac(srw_ss())[]>>
      rveq >> qmatch_asmsub_rename_tac`menv ++ env.v` >>
      qmatch_assum_abbrev_tac`compile_row t (NONE::bvs0) p = X` >>
      (compile_row_correct
       |> CONJUNCT1
       |> SIMP_RULE (srw_ss())[]
       |> Q.SPECL[`t`,`p`,`bvs0`,`env`,`s`,`v`]
       |> Q.GENL[`any_cc`,`any_co`]
       |> mp_tac) >>
      simp[Abbr`X`] >>
      disch_then(qspecl_then[`cc`,`pure_co compile o co`]strip_assume_tac) >>
      var_eq_tac >>
      qpat_abbrev_tac`xx = evaluate _ _ _` >>
      qmatch_assum_abbrev_tac`Abbrev(xx = evaluate (v4::env4) s4 [f (compile_exp bvss exp)])` >>
      qunabbrev_tac`xx` >>
      qhdtm_x_assum`state_rel`mp_tac >>
      qpat_abbrev_tac`xx = evaluate _ _ _` >>
      qmatch_assum_abbrev_tac`Abbrev(xx = evaluate env3 s4 [exp3])` >>
      qunabbrev_tac`xx` >> strip_tac >>
      qspecl_then[`env3`,`s4`,`[exp3]`]mp_tac evaluate_exp_rel >>
      sg `NoRun_state s4` >- fs [Abbr`s4`, compile_state_NoRun] >> fs [] >>
      sg `NoRun exp3 /\ EVERY NoRun_v env3` >- (
        fs [Abbr`exp3`, Abbr`env3`, Abbr`env4`, compile_exp_NoRun, compile_env_aux]) >>
      simp[pair_lemma] >> (fn (g as (_,w)) => split_uncurry_arg_tac (rand(rator w)) g) >>
      full_simp_tac(srw_ss())[PULL_EXISTS] >>
      disch_then(qspecl_then[`menv4++env4`,`s4`,`compile_exp bvss exp`]mp_tac) >>
      (impl_tac >- (
         simp[Abbr`env3`,Abbr`env4`,Abbr`exp3`] >>
         simp [compile_env_aux] >>
         match_mp_tac(CONJUNCT1 compile_exp_shift) >>
         simp[Abbr`bvss`,Abbr`bvs0`] >> conj_tac >- (
           qpat_x_assum`X = MAP Y menv`mp_tac >>
           disch_then(mp_tac o Q.AP_TERM`set`) >>
           simp[pred_setTheory.EXTENSION,MEM_FILTER,MEM_ZIP,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
           simp[MEM_EL,PULL_EXISTS,FORALL_PROD] >>metis_tac[] ) >>
         simp[bvs_V_def,env_rel_def] >>
         rpt gen_tac >> strip_tac >>
         imp_res_tac find_index_LESS_LENGTH >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> simp[] >>
         full_simp_tac(srw_ss())[find_index_APPEND] >>
         qpat_x_assum`X = SOME k2`mp_tac >>
         BasicProvers.CASE_TAC >- (
           qpat_x_assum`X = SOME k1`mp_tac >>
           BasicProvers.CASE_TAC >- (
             simp[Once find_index_shift_0] >> strip_tac >>
             simp[Once find_index_shift_0] >> strip_tac >>
             srw_tac[][] >>
             simp[rich_listTheory.EL_APPEND2] ) >>
           full_simp_tac(srw_ss())[GSYM find_index_NOT_MEM] >>
           imp_res_tac find_index_is_MEM >>
           qpat_x_assum`X = MAP Y Z`(mp_tac o Q.AP_TERM`set`) >>
           full_simp_tac(srw_ss())[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,UNCURRY] >>
           simp[EQ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
           full_simp_tac(srw_ss())[PULL_EXISTS] >>
           first_x_assum(qspec_then`y`mp_tac) >>
           rev_full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
           rev_full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] >>
           metis_tac[] ) >>
         qpat_x_assum`X = SOME k1`mp_tac >>
         BasicProvers.CASE_TAC >- (
           full_simp_tac(srw_ss())[GSYM find_index_NOT_MEM] >>
           imp_res_tac find_index_is_MEM >>
           qpat_x_assum`X = MAP Y Z`(mp_tac o Q.AP_TERM`set`) >>
           full_simp_tac(srw_ss())[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,UNCURRY] >>
           simp[EQ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
           full_simp_tac(srw_ss())[PULL_EXISTS] >>
           rev_full_simp_tac(srw_ss())[MEM_ZIP,PULL_EXISTS] >>
           rev_full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] >>
           qmatch_assum_rename_tac`z < SUC _` >>
           last_x_assum(qspec_then`z`mp_tac) >>
           qpat_x_assum`SOME x = Y`(assume_tac o SYM) >>
           simp[] >> srw_tac[][] >>
           metis_tac[] ) >>
         srw_tac[][] >>
         imp_res_tac find_index_LESS_LENGTH >>
         full_simp_tac(srw_ss())[] >> simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
         qmatch_assum_rename_tac`k2 < LENGTH l2` >>
         Q.ISPEC_THEN`l2`mp_tac(CONV_RULE SWAP_FORALL_CONV (INST_TYPE[beta|->``:patSem$v``]find_index_in_FILTER_ZIP_EQ)) >>
         disch_then(qspec_then`IS_SOME`mp_tac) >>
         disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(op@ o (partition(equal"v1" o fst o dest_var))))) >>
         disch_then(qspec_then`menv4`mp_tac) >>
         simp[] >>
         disch_then(qspecl_then[`SOME x`,`0`,`0`]mp_tac) >>
         simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
         full_simp_tac(srw_ss())[combinTheory.o_DEF,UNCURRY] >>
         simp[EL_ZIP,EL_MAP,UNCURRY])) >>
      strip_tac >>
      `r2 ≠ Rerr (Rabort Rtype_error)` by (
        spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] ) >>
      full_simp_tac(srw_ss())[Abbr`s4`,compile_state_def,EXT compile_vs_map] >>
      metis_tac[state_rel_trans,result_rel_LIST_v_v_rel_trans]) >>
    ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`pes`>>full_simp_tac(srw_ss())[evaluate_flat_def] >>
    DEEP_INTRO_TAC sIf_intro >>
    simp[patSemTheory.evaluate_def] >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    Q.ISPECL_THEN[`co`,`cc`]mp_tac
      (Q.GENL[`co`,`cc`](CONJUNCT1 compile_pat_correct)) >>
    disch_then(qspecl_then[`t§2`,`p`,`v`,`env`,`s`,`[]`]mp_tac) >> simp[] >>
    strip_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> pop_assum kall_tac >>
    simp[patSemTheory.do_if_def] >>
    first_x_assum(qspec_then`t§4`strip_assume_tac) \\
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
QED

Theorem compile_evaluate_decs:
   flatSem$evaluate_decs env ^s prog = res ∧ ¬env.check_ctor ∧ env.exh_pat ∧
   SND (SND res) ≠ SOME (Rabort Rtype_error) ⇒
   ∃res4.
   patSem$evaluate [] (compile_state co cc ^s) (compile prog) = res4 ∧
   state_rel (compile_state co cc (FST res)) (FST res4) ∧
   OPTREL (exc_rel v_rel)
     (OPTION_MAP (map_error_result compile_v) (SND (SND res)))
     (case (SND res4) of Rval _ => NONE | Rerr e => SOME e)
Proof
  map_every qid_spec_tac[`res`,`env`,`s`]
  \\ Induct_on`prog`
  >- (
    rw[flatSemTheory.evaluate_decs_def, compile_def]
    \\ fs[OPTREL_def, patSemTheory.evaluate_def] )
  \\ simp[flatSemTheory.evaluate_decs_def]
  \\ reverse Cases \\ simp[flatSemTheory.evaluate_dec_def]
  >- (
    rpt gen_tac \\ strip_tac \\ rfs[]
    \\ simp[compile_def]
    \\ qmatch_goalsub_abbrev_tac`evaluate_decs env1`
    \\ `env1 = env` by simp[Abbr`env1`,flatSemTheory.environment_component_equality]
    \\ fs[Abbr`env1`]
    \\ CASE_TAC
    \\ CASE_TAC
    \\ fs[]
    \\ metis_tac[FST,SND] )
  >- (
    rpt gen_tac \\ strip_tac \\ rfs[]
    \\ simp[compile_def]
    \\ qmatch_goalsub_abbrev_tac`evaluate_decs env1`
    \\ `env1 = env` by simp[Abbr`env1`,flatSemTheory.environment_component_equality]
    \\ fs[Abbr`env1`]
    \\ CASE_TAC
    \\ CASE_TAC
    \\ fs[]
    \\ metis_tac[FST,SND] )
  \\ rpt gen_tac \\ strip_tac \\ rfs[]
  \\ fs[compile_def]
  \\ CASE_TAC
  \\ split_pair_case_tac \\ fs[]
  \\ simp[Once evaluate_cons]
  \\ split_pair_case_tac \\ fs[]
  \\ Q.ISPEC_THEN`cc`drule(Q.GEN`cc`(CONJUNCT1 compile_exp_evaluate))
  \\ simp[]
  \\ impl_tac >- ( strip_tac \\ fs[] \\ rw[] \\ fs[] )
  \\ split_pair_case_tac \\ fs[]
  \\ strip_tac
  \\ reverse CASE_TAC \\ fs[]
  >- (
    ntac 2 (pop_assum mp_tac)
    \\ CASE_TAC \\ fs[]
    >- (
      CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[] )
    \\ strip_tac \\ rveq
    \\ simp[Once evaluate_cons]
    \\ simp[OPTREL_def] )
  \\ ntac 2 (pop_assum mp_tac)
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ strip_tac \\ rveq
  \\ TOP_CASE_TAC \\ fs[]
  \\ simp[Once evaluate_cons]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`evaluate_decs env1`
  \\ `env1 = env` by simp[Abbr`env1`,flatSemTheory.environment_component_equality]
  \\ fs[Abbr`env1`]
  \\ qmatch_asmsub_rename_tac`evaluate_decs env s1 prog`
  \\ first_x_assum(qspecl_then[`s1`,`env`]mp_tac)
  \\ simp[]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`SND p`
  \\ Cases_on`p` \\ fs[markerTheory.Abbrev_def]
  \\ pop_assum(assume_tac o SYM) \\ fs[]
  \\ drule evaluate_exp_rel
  \\ simp[compile_NoRun, compile_state_NoRun]
  \\ qmatch_assum_rename_tac`state_rel (_ _ s1) s2`
  \\ disch_then(qspecl_then[`[]`,`s2`,`compile prog`]mp_tac)
  \\ simp[CONJUNCT2 exp_rel_refl]
  \\ strip_tac
  \\ qhdtm_x_assum`OPTREL`mp_tac
  \\ CASE_TAC \\ fs[OPTREL_def]
  >- metis_tac[state_rel_trans]
  \\ strip_tac \\ fs[]
  \\ rveq
  \\ metis_tac[state_rel_trans, exc_rel_v_rel_trans]
QED

Theorem compile_semantics:
   semantics T F (ffi:'ffi ffi$ffi_state) es ≠ Fail ⇒
   semantics
     []
     (compile_state co cc (initial_state ffi k0))
     (compile es) =
   semantics T F ffi es
Proof
  simp[flatSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    srw_tac[][] >>
    simp[patSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      qhdtm_x_assum`flatSem$evaluate_decs`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g as (_,w) => Cases_on[ANTIQUOTE(rand(rand(lhs w)))] g) \\
      fs[] \\ spose_not_then strip_assume_tac \\
      drule(compile_evaluate_decs) >>
      impl_tac >- (fs[] \\ EVAL_TAC) \\ strip_tac \\
      rveq >>
      rfs[flatSemTheory.initial_state_def, compile_state_with_clock, OPTREL_SOME] \\
      qpat_x_assum`Rabort _ = _`(assume_tac o SYM) \\
      fs[map_error_result_Rtype_error] ) \\
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      srw_tac[][] >>
      qmatch_assum_abbrev_tac`flatSem$evaluate_decs env ss es = _` >>
      qmatch_assum_abbrev_tac`patSem$evaluate bnv bs be = _` >>
      qispl_then[`es`,`env`,`ss`]mp_tac flatPropsTheory.evaluate_decs_add_to_clock_io_events_mono >>
      Q.ISPECL_THEN [`bnv`,`bs`,`be`](mp_tac o Q.GEN`extra`) patPropsTheory.evaluate_add_to_clock_io_events_mono >>
      simp[Abbr`bs`,Abbr`ss`] >>
      disch_then(qspec_then`k`strip_assume_tac) >>
      disch_then(qspec_then`k'`strip_assume_tac) >>
      first_assum(mp_then (Pos last) mp_tac (GEN_ALL(flatPropsTheory.evaluate_decs_add_to_clock))) >>
      disch_then(qspec_then `k'` mp_tac) >>
      impl_tac >- (every_case_tac >> fs[]) >>
      strip_tac \\
      first_assum (mp_then Any mp_tac (GEN_ALL patPropsTheory.evaluate_add_to_clock)) >>
      simp[]
      \\ disch_then(qspec_then `k` mp_tac) >>
      impl_tac >- (every_case_tac >> fs[]) >>
      strip_tac >>
      drule (compile_evaluate_decs) >>
      impl_tac >- (
        unabbrev_all_tac \\ EVAL_TAC
        \\ every_case_tac \\ fs[] )
      \\ strip_tac >> unabbrev_all_tac
      \\ fs[flatSemTheory.initial_state_def, compile_state_def]
      \\ rveq \\ fs[] \\ rfs[]
      \\ fs[OPTREL_def,CaseEq"semanticPrimitives$result"] \\ rveq \\ fs[]
      \\ fs[state_rel_def,result_rel_def]
      \\ every_case_tac \\ fs[]) >>
    drule (compile_evaluate_decs) >> simp[] >>
    impl_tac >- ( EVAL_TAC \\ strip_tac\\ fs[]) \\
    strip_tac >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    full_simp_tac(srw_ss())[state_rel_def,compile_state_def,flatSemTheory.initial_state_def] >>
    qexists_tac`k`>>simp[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    fs[OPTREL_def]
    \\ Cases_on`z` \\ rveq \\ fs[]
    \\ rveq \\ fs[]
    \\ CASE_TAC \\ fs[]) >>
  strip_tac >>
  simp[patSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`SND p ≠ _` >>
    Cases_on`p`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(mp_tac o SYM) >>
    (fn g as (_,w) => Cases_on[ANTIQUOTE(rand(lhs(#1(dest_imp w))))] g) \\
    drule compile_evaluate_decs \\
    rw[] \\ strip_tac \\ rw[] \\ fs[] \\
    first_x_assum(fn th => mp_tac th \\ impl_tac >- (fs[] \\ EVAL_TAC)) \\
    fs[flatSemTheory.initial_state_def,compile_state_with_clock,OPTREL_SOME]
    \\ spose_not_then strip_assume_tac \\ rw[]
    \\ qpat_x_assum`Rabort _ = _`(assume_tac o SYM)
    \\ fs[map_error_result_Rtype_error] ) \\
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g as (_,w) => Cases_on[ANTIQUOTE(rand(rand(lhs(rand(#1(dest_imp w))))))] g) \\
    strip_tac >>
    drule compile_evaluate_decs >>
    impl_tac >- (fs[] \\ EVAL_TAC) \\
    fs[compile_state_with_clock,flatSemTheory.initial_state_def] >>
    spose_not_then strip_assume_tac >>
    full_simp_tac(srw_ss())[state_rel_def,compile_state_def] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
    Cases_on`r'` >>
    fs[OPTREL_def]
    \\ rveq
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ every_case_tac \\ fs[]) >>
  strip_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  specl_args_of_then``flatSem$evaluate_decs``(Q.GENL[`env`,`s`,`prog`,`res`]compile_evaluate_decs) mp_tac >>
  simp[state_rel_def,compile_state_def,flatSemTheory.initial_state_def] \\
  impl_tac >- EVAL_TAC \\ simp[]
QED

val set_globals_let_els = Q.prove(`
  ∀t n m e.
  set_globals (Let_Els t n m e) = set_globals e`,
  ho_match_mp_tac Let_Els_ind>>rw[Let_Els_def,sLet_def,op_gbag_def]>>
  CASE_TAC \\ fs[op_gbag_def] \\
  CASE_TAC \\ fs[op_gbag_def] \\
  last_x_assum sym_sub_tac>>fs[])

Theorem set_globals_sIf_sub:
   set_globals (sIf t e1 e2 e3) ≤ set_globals (If t e1 e2 e3)
Proof
  rw[sIf_def,SUB_BAG_UNION] \\
  CASE_TAC \\ fs[] \\
  CASE_TAC \\ fs[] \\
  CASE_TAC \\ fs[]
QED

Theorem set_globals_sIf_empty_suff:
   set_globals (If t e1 e2 e3) = {||} ⇒ set_globals (sIf t e1 e2 e3) = {||}
Proof
  metis_tac[set_globals_sIf_sub,SUB_BAG_EMPTY]
QED

Theorem set_globals_sLet_sub:
   set_globals (sLet t e1 e2) ≤ set_globals (Let t e1 e2)
Proof
  rw[sLet_def] \\
  CASE_TAC \\ fs[] \\
  CASE_TAC \\ fs[]
QED

Theorem set_globals_sLet_empty_suff:
   set_globals (Let t e1 e2) = {||} ⇒ set_globals (sLet t e1 e2) = {||}
Proof
  metis_tac[set_globals_sLet_sub,SUB_BAG_EMPTY]
QED

val compile_pat_empty = Q.prove(`
  (∀t p. set_globals (compile_pat t p) = {||}) ∧
  (∀t n ps. set_globals (compile_pats t n ps) = {||})`,
  ho_match_mp_tac compile_pat_ind>>
  rw[compile_pat_def,op_gbag_def,set_globals_let_els]>>
  TRY(match_mp_tac set_globals_sIf_empty_suff) \\
  TRY(match_mp_tac set_globals_sLet_empty_suff) \\
  rw[op_gbag_def,set_globals_let_els]>>
  TRY(match_mp_tac set_globals_sLet_empty_suff) \\
  rw[op_gbag_def,set_globals_let_els]);

val compile_row_set_globals = Q.prove(`
  (∀t bvs p a b f exp.
  compile_row t bvs p = (a,b,f) ⇒ set_globals (f exp) = set_globals exp) ∧
  (∀t bvs n k ps a b f exp. compile_cols t bvs n k ps = (a,b,f) ⇒ set_globals (f exp) = set_globals exp)`,
  ho_match_mp_tac compile_row_ind>>rw[compile_row_def]>>fs[]>>
  rpt (pairarg_tac \\ fs[]) \\ rw[] >>
  last_x_assum(qspec_then`exp`strip_assume_tac) \\
  TRY(first_x_assum(qspec_then`fs exp`strip_assume_tac)) \\
  rw[sLet_def] \\ CASE_TAC \\ fs[op_gbag_def] \\
  CASE_TAC \\ fs[op_gbag_def] \\
  qpat_x_assum `{||}=f` sym_sub_tac>>rw[op_gbag_def]>>
  qpat_x_assum `{||}=f` sym_sub_tac>>rw[op_gbag_def]);

val sIf_set_globals_lemma =
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] SUB_BAG_TRANS)
           set_globals_sIf_sub;

val sLet_set_globals_lemma =
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] SUB_BAG_TRANS)
           set_globals_sLet_sub;

Theorem set_globals_eq:
   (!bvs exp. set_globals (compile_exp bvs exp) ≤ set_globals exp) /\
   (!bvs exps.
     elist_globals (compile_exps bvs exps) ≤ elist_globals exps) /\
   (!bvs funs.
     elist_globals (compile_funs bvs funs) ≤
     elist_globals (MAP (SND o SND) funs)) /\
   (!tra bvs pes.
     set_globals (compile_pes tra bvs pes) ≤ elist_globals (MAP SND pes))
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rw [compile_exp_def]
  \\ fs [SUB_BAG_UNION]
  >- (match_mp_tac sIf_set_globals_lemma \\ fs [SUB_BAG_UNION])
  >- (FULL_CASE_TAC \\ fs [])
  >-
   (Cases_on `op` \\
    fs [flatPropsTheory.op_gbag_def, op_gbag_def, SUB_BAG_UNION])
  >- (match_mp_tac sLet_set_globals_lemma \\ fs [SUB_BAG_UNION])
  >- (match_mp_tac sLet_set_globals_lemma \\ fs [SUB_BAG_UNION])
  >-
   (split_pair_case_tac \\ fs []
    \\ imp_res_tac compile_row_set_globals \\ fs [])
  \\ match_mp_tac sIf_set_globals_lemma
  \\ fs [SUB_BAG_UNION]
  \\ split_pair_case_tac \\ fs []
  \\ fs [compile_pat_empty]
  \\ imp_res_tac compile_row_set_globals \\ fs [SUB_BAG_UNION]
QED

val esgc_free_let_els = Q.prove(`
  ∀t n m e.
  esgc_free e ⇒
  esgc_free (Let_Els t n m e)`,
  ho_match_mp_tac Let_Els_ind>>rw[Let_Els_def,sLet_def,op_gbag_def]>>
  CASE_TAC \\ fs[op_gbag_def] \\
  CASE_TAC \\ fs[op_gbag_def] \\
  last_x_assum sym_sub_tac>>fs[])

Theorem esgc_free_sIf_sub:
   esgc_free (If t e1 e2 e3) ⇒ esgc_free (sIf t e1 e2 e3)
Proof
  rw[sIf_def,SUB_BAG_UNION] \\
  every_case_tac \\ fs[]
QED

Theorem esgc_free_sLet_sub:
   esgc_free (Let t e1 e2) ⇒ esgc_free (sLet t e1 e2)
Proof
  rw[sLet_def] \\
  CASE_TAC \\ fs[] \\
  CASE_TAC \\ fs[]
QED

val compile_pat_esgc_free = Q.prove(`
  (∀t p. esgc_free (compile_pat t p)) ∧
  (∀t n ps. esgc_free (compile_pats t n ps))`,
  ho_match_mp_tac compile_pat_ind>>
  rw[compile_pat_def,op_gbag_def,esgc_free_let_els]>>
  TRY(match_mp_tac esgc_free_sIf_sub) \\
  rw[compile_pat_def,op_gbag_def,esgc_free_let_els]>>
  TRY(match_mp_tac esgc_free_sLet_sub) \\
  rw[compile_pat_def,op_gbag_def,esgc_free_let_els]);

val compile_row_esgc_free = Q.prove(`
  (∀t bvs p a b f exp.
  compile_row t bvs p = (a,b,f) ∧ esgc_free exp ⇒
  esgc_free (f exp)) ∧
  (∀t bvs n k ps a b f exp.
  compile_cols t bvs n k ps = (a,b,f) ∧ esgc_free exp ⇒
  esgc_free (f exp))`,
  ho_match_mp_tac compile_row_ind>>rw[compile_row_def]>>fs[]>>
  rpt (pairarg_tac \\ fs[]) \\ rw[] >>
  last_x_assum(qspec_then`exp`strip_assume_tac) \\
  TRY(first_x_assum(qspec_then`fs exp`strip_assume_tac)) \\
  rw[sLet_def] \\ CASE_TAC \\ fs[op_gbag_def] \\
  CASE_TAC \\ fs[op_gbag_def]);

Theorem compile_exp_esgc_free:
   (!bvs exp.
      esgc_free exp
      ==>
      esgc_free (compile_exp bvs exp)) /\
   (!bvs exps.
      EVERY esgc_free exps
      ==>
      EVERY esgc_free (compile_exps bvs exps)) /\
   (!bvs funs.
      EVERY esgc_free (MAP (SND o SND) funs)
      ==>
      EVERY esgc_free (compile_funs bvs funs)) /\
   (!tra bvs pes.
      EVERY esgc_free (MAP SND pes)
      ==>
      esgc_free (compile_pes tra bvs pes))
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rw [compile_exp_def]
  \\ fs [esgc_free_sLet_sub, esgc_free_sIf_sub]
  >- (FULL_CASE_TAC \\ fs [])
  >-
   (qspecl_then [`SOME x::bvs`,`exp`]
                assume_tac
                (el 1 (CONJUNCTS set_globals_eq))
    \\ rfs [])
  >-
   (qspecl_then [`MAP (SOME o FST) funs ++ bvs`,`funs`]
                assume_tac
                (el 3 (CONJUNCTS set_globals_eq))
    \\ rfs [])
  \\ split_pair_case_tac \\ fs []
  >- metis_tac [compile_row_esgc_free]
  \\ match_mp_tac esgc_free_sIf_sub \\ fs []
  \\ metis_tac [compile_row_esgc_free, compile_pat_esgc_free]
QED

Theorem compile_esgc_free:
   ∀p. EVERY (esgc_free o dest_Dlet) (FILTER is_Dlet p) ⇒
    EVERY esgc_free (flat_to_pat$compile p)
Proof
  recInduct flat_to_patTheory.compile_ind
  \\ rw[flat_to_patTheory.compile_def]
  \\ irule (CONJUNCT1 compile_exp_esgc_free)
  \\ rw[]
QED

Theorem compile_distinct_setglobals:
   ∀e. BAG_ALL_DISTINCT (set_globals e) ⇒
       BAG_ALL_DISTINCT (set_globals (compile_exp [] e))
Proof
  rw[]>>
  match_mp_tac BAG_ALL_DISTINCT_SUB_BAG >>
  HINT_EXISTS_TAC>>fs[set_globals_eq]
QED

Theorem elist_globals_compile:
   ∀ls.
      elist_globals (flat_to_pat$compile ls) ≤ elist_globals (MAP dest_Dlet (FILTER is_Dlet ls))
Proof
  recInduct flat_to_patTheory.compile_ind
  \\ rw[flat_to_patTheory.compile_def]
  \\ irule (List.nth(CONJUNCTS SUB_BAG_UNION, 6))
  \\ rw[]
  \\ rw[set_globals_eq]
QED

val _ = export_theory()
