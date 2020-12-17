(*
  Correctness proof for flat_to_clos
*)
open preamble
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     flatLangTheory flatSemTheory flatPropsTheory backendPropsTheory
     closLangTheory closSemTheory closPropsTheory flat_to_closTheory;
local open helperLib induct_tweakLib in end;

val _ = new_theory"flat_to_closProof"

val _ = set_grammar_ancestry ["misc","ffi","flatProps","closProps",
                              "flat_to_clos","backendProps","backend_common"];

Theorem LIST_REL_EL: (* TODO: move *)
  !xs ys r.
    LIST_REL r xs ys <=>
    (LENGTH xs = LENGTH ys) /\
    !n. n < LENGTH ys ==> r (EL n xs) (EL n ys)
Proof
  Induct \\ Cases_on `ys` \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (Cases_on `n` \\ fs [])
  THEN1 (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
  \\ first_x_assum (qspec_then `SUC n` mp_tac) \\ fs []
QED

Inductive v_rel:
  (!n. v_rel (Loc n) (RefPtr n)) /\
  (!i. v_rel (Litv (IntLit i)) (Number i)) /\
  (!c. v_rel (Litv (Char c)) (Number (& (ORD c)))) /\
  (!s. v_rel (Litv (StrLit s)) (ByteVector (MAP (n2w o ORD) s))) /\
  (!b. v_rel (Litv (Word8 b)) (Number (& (w2n b)))) /\
  (!w. v_rel (Litv (Word64 w)) (Word64 w)) /\
  (!vs ws. LIST_REL v_rel vs ws ==> v_rel (Conv NONE vs) (Block 0 ws)) /\
  (!vs ws t r. LIST_REL v_rel vs ws ==> v_rel (Conv (SOME (t,r)) vs) (Block t ws)) /\
  (!vs ws. LIST_REL v_rel vs ws ==> v_rel (Vectorv vs) (Block 0 ws)) /\
  (!env m db.
    (!n x. ALOOKUP env.v n = SOME x ==>
           findi (SOME n) m < LENGTH db /\
           v_rel x (EL (findi (SOME n) m) db)) ==>
     env_rel env (m:string option list) (db:closSem$v list)) /\
  (!env m db n e.
     env_rel env m db /\ no_Mat e ==>
     v_rel (Closure env n e)
           (Closure NONE [] db 1 (HD (compile (SOME n::m) [e])))) /\
  (!funs n env m db.
    n < LENGTH funs /\ env_rel env m db /\ ALL_DISTINCT (MAP FST funs) /\
    EVERY no_Mat (MAP (SND o SND) funs) ==>
     v_rel (Recclosure env funs (FST (EL n funs)))
      (Recclosure NONE [] db (MAP
            (λ(f,v,x). (1, HD (compile
                       (SOME v::(MAP (λn. SOME (FST n)) funs ++ m))
                       [x]))) funs) n))
End

Theorem v_rel_def =
  [``v_rel (Loc n) x1``,
   ``v_rel (Litv (IntLit l1)) x1``,
   ``v_rel (Litv (StrLit s)) x1``,
   ``v_rel (Litv (Char c)) x1``,
   ``v_rel (Litv (Word8 b)) x1``,
   ``v_rel (Litv (Word64 w)) x1``,
   ``v_rel (Vectorv y) x1``,
   ``v_rel (Conv x y) x1``,
   ``v_rel (Closure x y z) x1``,
   ``v_rel (Recclosure x y t) x1``]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ

Theorem env_rel_def = ``env_rel env m db`` |> ONCE_REWRITE_CONV [v_rel_cases];

Definition opt_rel_def[simp]:
  opt_rel f NONE NONE = T /\
  opt_rel f (SOME x) (SOME y) = f x y /\
  opt_rel f _ _ = F
End

Definition store_rel_def:
  store_rel refs t_refs =
    !i. if LENGTH refs <= i then FLOOKUP t_refs i = NONE else
          case EL i refs of
          | Refv v => (?x. FLOOKUP t_refs i = SOME (ValueArray [x]) /\ v_rel v x)
          | Varray vs => (?xs. FLOOKUP t_refs i = SOME (ValueArray xs) /\
                               LIST_REL v_rel vs xs)
          | W8array bs => FLOOKUP t_refs i = SOME (ByteArray F bs)
End

Definition inc_compile_decs_def:
  inc_compile_decs decs = (compile_decs decs ++
    compile_decs [Dlet (Con None NONE [])], [])
End

Definition install_config_rel_def:
  install_config_rel ic co cc = (
    (!i. no_Mat_decs (SND (ic.compile_oracle i))) /\
    co = pure_co inc_compile_decs o ic.compile_oracle /\
    ic.compile = pure_cc inc_compile_decs cc
  )
End

Definition state_rel_def:
  state_rel (s:('c, 'ffi) flatSem$state) (t:('c,'ffi) closSem$state) <=>
    1 <= t.max_app /\
    s.ffi = t.ffi /\
    s.clock = t.clock /\
    store_rel s.refs t.refs /\
    LIST_REL (opt_rel v_rel) s.globals t.globals /\
    install_config_rel s.eval_config t.compile_oracle t.compile
End

Theorem v_rel_to_list:
  !x y xs. v_rel x y /\ flatSem$v_to_list x = SOME xs ==>
           ?ys. closSem$v_to_list y = SOME ys /\ LIST_REL v_rel xs ys
Proof
  ho_match_mp_tac flatSemTheory.v_to_list_ind \\ fs [v_rel_def]
  \\ rpt strip_tac \\ fs [flatSemTheory.v_to_list_def,v_to_list_def]
  \\ rveq \\ fs [] \\ fs [option_case_eq] \\ rveq \\ fs [PULL_EXISTS]
QED

Theorem IMP_v_rel_to_list:
  !xs ys.
    LIST_REL v_rel xs ys ==>
    v_rel (list_to_v xs) (list_to_v ys)
Proof
  Induct \\ Cases_on `ys`
  \\ fs [flatSemTheory.list_to_v_def,list_to_v_def,v_rel_def]
QED

Theorem lookup_byte_array:
  state_rel s1 t1 /\ store_lookup i s1.refs = SOME (W8array bytes) ==>
  FLOOKUP t1.refs i = SOME (ByteArray F bytes)
Proof
  fs [state_rel_def,store_rel_def] \\ rw []
  \\ fs [store_lookup_def]
  \\ first_x_assum (qspec_then `i` mp_tac) \\ fs []
QED

Theorem lookup_array:
  state_rel s1 t1 /\ store_lookup i s1.refs = SOME (Varray vs) ==>
  ?ws. FLOOKUP t1.refs i = SOME (ValueArray ws) /\ LIST_REL v_rel vs ws
Proof
  fs [state_rel_def,store_rel_def] \\ rw []
  \\ fs [store_lookup_def]
  \\ first_x_assum (qspec_then `i` mp_tac) \\ fs []
QED

Triviality env_rel_CONS_upd:
  env_rel (env with v updated_by f) m db /\ v_rel v1 v2 ==>
  env_rel (env with v updated_by (\xs. (n,v1) :: f xs)) (SOME n :: m) (v2 :: db)
Proof
  fs [env_rel_def,findi_def,GSYM ADD1]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
QED

Triviality env_rel_CONS:
  env_rel (env with <| v := xs |>) m db /\ v_rel v1 v2 ==>
  env_rel (env with <| v := (n,v1) :: xs |>) (SOME n :: m) (v2 :: db)
Proof
  simp [K_DEF, env_rel_CONS_upd]
QED

Triviality env_rel_APPEND:
  !name_prefix prefix db_prefix env m db.
    env_rel env m db /\
    LIST_REL v_rel (MAP SND prefix) db_prefix /\
    name_prefix = MAP (SOME o FST) prefix ==>
    env_rel (env1 with <| v := prefix ++ env.v |>) (name_prefix ++ m)
      (db_prefix ++ db)
Proof
  Induct \\ fs []
  THEN1 (rw[env_rel_def])
  \\ Cases_on `prefix` \\ fs [PULL_EXISTS] \\ rw []
  \\ PairCases_on `h` \\ fs []
  \\ match_mp_tac env_rel_CONS
  \\ fs []
QED

Theorem state_rel_initial_state:
  0 < max_app /\ install_config_rel ec co cc ==>
  state_rel (initial_state ffi k ec)
            (initial_state ffi max_app FEMPTY co cc k)
Proof
  fs [state_rel_def,flatSemTheory.initial_state_def,initial_state_def,store_rel_def]
QED

Triviality state_rel_IMP_clock:
  state_rel s t ==> s.clock = t.clock
Proof
  fs [state_rel_def]
QED

Triviality state_rel_dec_clock:
  state_rel s t ==> s.clock = t.clock /\
    state_rel (dec_clock s) (dec_clock 1 t)
Proof
  fs [state_rel_def, flatSemTheory.dec_clock_def, dec_clock_def]
QED

val s = ``s:('c, 'ffi) flatSem$state``;
val t = ``t:('c, 'ffi) closSem$state``;

val exps_goal =
  ``\env ^s es.
      !m db res1 s1 ^t.
        evaluate env s es = (s1,res1) /\ state_rel s t /\ env_rel env m db /\
        EVERY no_Mat es /\ res1 <> Rerr (Rabort Rtype_error) ==>
        ?res2 t1.
          evaluate (compile m es, db, t) = (res2,t1) /\ state_rel s1 t1 /\
          result_rel (LIST_REL v_rel) v_rel res1 res2``

val dec_goal =
  ``\^s d. !res1 s1 ^t.
    evaluate_dec s d = (s1,res1) ∧ state_rel s t ∧
    no_Mat_decs [d] /\ res1 ≠ SOME (Rabort Rtype_error) ⇒
    ∃res2 t1.
      evaluate (compile_decs [d],[],t) = (res2,t1) ∧ state_rel s1 t1 /\
      ?v.
        let res1' = (case res1 of NONE => Rval v | SOME e => Rerr e) in
          result_rel (LIST_REL (\x y. T)) v_rel res1' res2``

Theorem evaluate_decs_sing:
  evaluate_decs s [d] = evaluate_dec s d
Proof
  simp [flatSemTheory.evaluate_def]
  \\ every_case_tac \\ simp []
QED

val decs_goal =
  ``\^s ds. !res1 s1 ^t.
    evaluate_decs s ds = (s1,res1) ∧ state_rel s t ∧
    no_Mat_decs ds /\ res1 ≠ SOME (Rabort Rtype_error) ⇒
    ∃res2 t1.
      evaluate (compile_decs ds,[],t) = (res2,t1) ∧ state_rel s1 t1 /\
      ?v.
        let res1' = (case res1 of NONE => Rval v | SOME e => Rerr e) in
          result_rel (LIST_REL (\x y. T)) v_rel res1' res2``

local
  val ind_thm = flatSemTheory.evaluate_ind
    |> induct_tweakLib.list_single_induct
    |> ISPEC exps_goal
    |> ISPEC decs_goal
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
    |> REWRITE_RULE [evaluate_decs_sing];
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_nil:
  ^(get_goal "[]")
Proof
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def]
QED

Theorem compile_cons:
  ^(get_goal "_::_::_")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs [evaluate_APPEND]
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ fs [pair_case_eq] \\ fs []
  \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ qpat_x_assum `_ = (s1,res1)` mp_tac
  \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
QED

Theorem compile_Lit:
  ^(get_goal "flatLang$Lit")
Proof
  fs [flatSemTheory.evaluate_def,compile_def]
  \\ Cases_on `l` \\ fs [PULL_EXISTS]
  \\ once_rewrite_tac [CONJUNCT2 v_rel_cases] \\ fs []
  \\ fs [compile_lit_def,evaluate_def,do_app_def]
QED

Theorem compile_Raise:
  ^(get_goal "flatLang$Raise")
Proof
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def] \\ rw []
  \\ reverse (fs [pair_case_eq,result_case_eq]) \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule \\ strip_tac \\ rveq \\ fs []
  \\ imp_res_tac flatPropsTheory.evaluate_sing \\ fs []
QED

Theorem dest_pat_from_case:
  (case pes of [(Pvar _, _)] => T | _ => F) ==>
  ?nm rhs. dest_pat pes = SOME (nm, rhs)
Proof
  EVERY_CASE_TAC \\ simp [dest_pat_def]
QED

Theorem compile_Handle:
  ^(get_goal "flatLang$Handle")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ imp_res_tac dest_pat_from_case
  \\ fs []
  \\ fs [dest_pat_thm] \\ rveq \\ fs []
  \\ fs [flatSemTheory.evaluate_def,evaluate_def,
         EVAL ``ALL_DISTINCT (pat_bindings (Pvar x) [])``,
         EVAL ``pmatch e s' (Pvar x) v []``,pmatch_rows_def]
  \\ fs [pmatch_def, pat_bindings_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ fs [error_result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ rename [`v_rel v1 v2`]
  \\ `env_rel <| v := (nm,v1)::env.v |> (SOME nm::m) (v2::db)` by
    (match_mp_tac env_rel_CONS \\ fs [env_rel_def])
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED

Theorem compile_Let:
  ^(get_goal "flatLang$Let")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ rename [`v_rel v1 v2`]
  \\ `env_rel (env with v updated_by opt_bind n v1) (n::m) (v2::db)` by
   (fs [env_rel_def]
    \\ Cases_on `n` \\ fs [libTheory.opt_bind_def,findi_def,GSYM ADD1]
    \\ rw [] \\ fs [])
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED

Triviality LIST_REL_MAP_GENLIST:
  !funs f1 f2 R.
    (!n. n < LENGTH funs ==> R (f1 (EL n funs)) (f2 n)) ==>
    LIST_REL R (MAP f1 funs) (GENLIST f2 (LENGTH funs))
Proof
  recInduct SNOC_INDUCT \\ fs []
  \\ fs [GENLIST,MAP_SNOC,LIST_REL_SNOC] \\ rpt strip_tac
  THEN1
   (first_x_assum match_mp_tac
    \\ metis_tac [EL_SNOC,DECIDE ``n<m ==> n < SUC m``])
  \\ first_x_assum (qspec_then `LENGTH l` mp_tac)
  \\ fs [SNOC_APPEND,EL_LENGTH_APPEND]
QED

Theorem compile_Letrec:
  ^(get_goal "flatLang$Letrec")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [EVERY_MAP]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ rpt strip_tac \\ `1 <= t.max_app` by fs [state_rel_def] \\ fs []
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ qmatch_goalsub_abbrev_tac `GENLIST recc`
  \\ first_x_assum drule
  \\ disch_then match_mp_tac
  \\ fs [build_rec_env_eq_MAP]
  \\ match_mp_tac env_rel_APPEND \\ fs []
  \\ simp [MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [Abbr`recc`]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ rw [MAP_EQ_f, FORALL_PROD]
  \\ qexists_tac `m`
  \\ simp [EVERY_MAP]
QED

Theorem compile_Fun:
  ^(get_goal "flatLang$Fun")
Proof
  fs [evaluate_def,flatSemTheory.evaluate_def,PULL_EXISTS,compile_def]
  \\ rpt strip_tac \\ `1 <= t.max_app` by fs [state_rel_def] \\ fs []
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ metis_tac []
QED

Theorem compile_Con:
  ^(get_goal "flatLang$Con _ NONE") /\
  ^(get_goal "flatLang$Con _ (SOME _)")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq,CaseEq"bool"] \\ fs []
  \\ first_x_assum drule
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ (disch_then drule \\ impl_tac THEN1 (CCONTR_TAC \\ fs []))
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs [] \\ fs [do_app_def]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ PairCases_on `cn` \\ fs []
QED

Theorem compile_Var_local:
  ^(get_goal "flatLang$Var_local")
Proof
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def] \\ rpt strip_tac
  \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ fs [env_rel_def]
QED

Triviality find_recfun_EL:
  !l0 n.
    n < LENGTH l0 /\ ALL_DISTINCT (MAP FST l0) ==>
    find_recfun (FST (EL n l0)) l0 = SOME (SND (EL n l0))
Proof
  Induct \\ fs [] \\ simp [Once find_recfun_def,FORALL_PROD]
  \\ rpt strip_tac \\ Cases_on `n` \\ fs []
  \\ rw [] \\ fs [MEM_MAP] \\ fs [FORALL_PROD] \\ fs [MEM_EL]
  \\ metis_tac [PAIR,PAIR_EQ,FST]
QED

Triviality IMP_PAIR:
  z = (x,y) ==> x = FST z /\ y = SND z
Proof
  Cases_on `z` \\ fs []
QED

Theorem compile_If:
  ^(get_goal "flatLang$If")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ fs [option_case_eq] \\ fs []
  \\ fs [do_if_def,bool_case_eq] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ fs []
  \\ fs [flatSemTheory.Boolv_def]
  \\ qpat_x_assum `v_rel _ _` mp_tac
  \\ once_rewrite_tac [v_rel_cases] \\ fs [Boolv_def]
QED

Theorem compile_Mat:
  ^(get_goal "flatLang$Mat")
Proof
  fs [no_Mat_def,dest_pat_thm] \\ rw []
  \\ fs [EVAL ``pmatch e s (Pvar p') v []``]
  \\ fs [EVAL ``ALL_DISTINCT (pat_bindings (Pvar p') [])``]
QED

Theorem state_rel_LEAST:
  state_rel s1 t1 ==>
  (LEAST ptr. ptr ∉ FDOM t1.refs) = LENGTH s1.refs
Proof
  fs [state_rel_def,store_rel_def] \\ rw []
  \\ ho_match_mp_tac
    (whileTheory.LEAST_ELIM
     |> ISPEC ``\x. x = LENGTH s1.refs``
     |> CONV_RULE (DEPTH_CONV BETA_CONV))
  \\ fs [] \\ rpt strip_tac \\ fs [FLOOKUP_DEF]
  THEN1
   (first_x_assum (qspec_then `LENGTH s1.refs` mp_tac)
    \\ fs [] \\ rw [] \\ asm_exists_tac \\ fs [])
  \\ `!i. i IN FDOM t1.refs <=> ~(LENGTH s1.refs <= i)` by
   (strip_tac \\ last_x_assum (qspec_then `i` mp_tac) \\ rw []
    \\ every_case_tac \\ fs[])
  \\ fs [] \\ CCONTR_TAC \\ fs []
  \\ `LENGTH s1.refs < ptr` by fs []
  \\ res_tac \\ fs []
QED

Theorem compile_op_evaluates_args:
  evaluate (xs,db,t) = (Rerr err,t1) /\ op <> Opapp /\ op <> Eval ==>
  evaluate ([compile_op tra op xs],db,t) = (Rerr err,t1)
Proof
  Cases_on `op`
  \\ fs [compile_op_def,evaluate_def,evaluate_APPEND,arg1_def,arg2_def]
  \\ every_case_tac \\ fs [evaluate_def]
  \\ fs [pair_case_eq,result_case_eq]
  \\ rw [] \\ fs [PULL_EXISTS,do_app_def]
QED

Theorem v_rel_Boolv[simp]:
  v_rel (Boolv b) v = (v = Boolv b)
Proof
  Cases_on `b` \\ fs [Once v_rel_cases,flatSemTheory.Boolv_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Theorem v_rel_Unitv[simp]:
  v_rel Unitv v = (v = Block 0 [])
Proof
  simp [Unitv_def, v_rel_def]
QED

val op_goal =
  ``do_app s1 op vs = SOME (s2,res2) /\
    state_rel s1 (t1:('c,'ffi) closSem$state) /\
    evaluate (xs,db,t) = (Rval ws,t1) /\
    LIST_REL v_rel vs (REVERSE ws) /\
    LENGTH xs = LENGTH vs /\ op <> Opapp ==>
    ∃res2' t1.
      evaluate ([compile_op tt op xs],db,t) = (res2',t1) ∧
      state_rel s2 t1 ∧
      result_rel (LIST_REL v_rel) v_rel (list_result res2) res2'``

Theorem op_refs:
  (op = Opref) \/
  (?n. op = El n) \/
  (op = Opassign) ==>
  ^op_goal
Proof
  Cases_on `op = Opref` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
           CaseEq "ast$lit",store_assign_def,option_case_eq]
    \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
    \\ fs [store_alloc_def] \\ rveq \\ fs [PULL_EXISTS]
    \\ simp [Once v_rel_cases]
    \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
    \\ imp_res_tac state_rel_LEAST \\ fs []
    \\ fs [state_rel_def,store_rel_def]
    \\ strip_tac
    \\ first_assum (qspec_then `i` mp_tac)
    \\ rewrite_tac [GSYM NOT_LESS,FLOOKUP_UPDATE,EL_LUPDATE]
    \\ Cases_on `LENGTH s1.refs = i` \\ rveq \\ fs [EL_LENGTH_APPEND]
    \\ IF_CASES_TAC \\ fs [EL_APPEND1])
  \\ Cases_on `?n. op = El n` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
           CaseEq "ast$lit",store_assign_def,option_case_eq]
    \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
    THEN1
     (qpat_x_assum `v_rel (Conv _ _) _` mp_tac
      \\ simp [Once v_rel_cases] \\ rw [] \\ fs [compile_op_def,arg1_def]
      \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ fs [LIST_REL_EL])
    \\ qpat_x_assum `v_rel (Loc _) _` mp_tac
    \\ simp [Once v_rel_cases]
    \\ Cases_on `v2` \\ fs []
    \\ fs [SWAP_REVERSE_SYM] \\ rw [] \\ fs [PULL_EXISTS]
    \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
    \\ fs [pair_case_eq,result_case_eq] \\ rveq \\ fs []
    \\ fs [state_rel_def,store_rel_def,store_lookup_def]
    \\ rename [`i < LENGTH s1.refs`]
    \\ first_assum (qspec_then `i` mp_tac)
    \\ rewrite_tac [GSYM NOT_LESS]
    \\ Cases_on `EL i s1.refs` \\ fs [store_v_same_type_def]
    \\ rpt strip_tac \\ fs []
    \\ strip_tac
    \\ fs [GSYM NOT_LESS,FLOOKUP_UPDATE,EL_LUPDATE])
  \\ Cases_on `op = Opassign` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
           CaseEq "ast$lit",store_assign_def,option_case_eq]
    \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel (Loc _) _` mp_tac
    \\ simp [Once v_rel_cases]
    \\ fs [SWAP_REVERSE_SYM] \\ rw [] \\ fs [PULL_EXISTS]
    \\ fs [compile_op_def,evaluate_def,do_app_def]
    \\ fs [pair_case_eq,result_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ fs [arg2_def,evaluate_def,do_app_def]
    \\ fs [state_rel_def,store_rel_def]
    \\ rename [`i < LENGTH s1.refs`]
    \\ first_assum (qspec_then `i` mp_tac)
    \\ rewrite_tac [GSYM NOT_LESS]
    \\ Cases_on `EL i s1.refs` \\ fs [store_v_same_type_def]
    \\ rpt strip_tac \\ fs []
    \\ simp [Unit_def, EVAL ``tuple_tag``]
    \\ strip_tac
    \\ fs [GSYM NOT_LESS,FLOOKUP_UPDATE,EL_LUPDATE]
    \\ rename [`if i = j then _ else _`]
    \\ Cases_on `i = j` \\ fs [] \\ fs [LUPDATE_def])
  \\ fs []
QED

Theorem op_chars:
  (?chop. op = Chopb chop) \/
  (op = Ord) \/
  (op = Chr) ==>
  ^op_goal
Proof
  Cases_on `?chop. op = Chopb chop` THEN1
   (fs [] \\ Cases_on `chop`
    \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
           CaseEq "ast$lit"]
    \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ simp [Once v_rel_cases]
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ simp [Once v_rel_cases]
    \\ fs [SWAP_REVERSE_SYM] \\ rw []
    \\ fs [compile_op_def,evaluate_def,do_app_def,opb_lookup_def])
  \\ Cases_on `op = Ord \/ op = Chr` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
        CaseEq "ast$lit"]
    \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute]
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [compile_op_def,evaluate_def,evaluate_APPEND,do_app_def,evaluate_def,arg1_def]
    \\ simp [Once v_rel_cases] \\ rw [ORD_CHR,chr_exn_v_def]
    \\ TRY (rename1 `~(ii < 0i)` \\ Cases_on `ii` \\ fs [])
    \\ TRY (rename1 `(0i <= ii)` \\ Cases_on `ii` \\ fs [])
    \\ `F` by intLib.COOPER_TAC)
  \\ rw [] \\ fs []
QED

Theorem op_ints:
  (?b. op = Opb b) \/
  (?b. op = Opn b) ==>
  ^op_goal
Proof
  rpt strip_tac \\ Cases_on `b` \\ rveq
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ rpt (qpat_x_assum `v_rel _ _` mp_tac)
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs [do_word_op_def]
  \\ rveq \\ fs [compile_op_def,arg1_def]
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ simp [evaluate_def,do_app_def,opb_lookup_def,opn_lookup_def,do_eq_def]
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [div_exn_v_def,v_rel_def,opn_lookup_def]
QED

Theorem op_words:
  (?w w1. op = Opw w w1) \/
  (?w. op = WordFromInt w) \/
  (?w. op = WordToInt w) ==>
  ^op_goal
Proof
  rw [] \\ Cases_on `w` \\ rveq \\ fs [] \\ TRY (Cases_on `w1`)
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ rpt (qpat_x_assum `v_rel _ _` mp_tac)
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs [do_word_op_def]
  \\ rveq \\ fs [compile_op_def,arg1_def]
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ simp [evaluate_def,do_app_def]
  \\ fs [some_def,EXISTS_PROD]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ `!x. b = FST x ∧ b' = SND x <=> x = (b,b')` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ simp [integer_wordTheory.w2n_i2w]
QED

Theorem op_shifts:
  (?w s n. op = Shift w s n) ==>
  ^op_goal
Proof
  rw [] \\ Cases_on `w` \\ Cases_on `s` \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ rename [`v_rel (Litv ww) y`] \\ Cases_on `ww`
  \\ fs [v_rel_def,do_shift_def] \\ rveq \\ fs []
  \\ fs [compile_op_def,evaluate_def,do_app_def,v_rel_def]
QED

Theorem op_floats:
  (?f. op = FP_cmp f) \/
  (?f. op = FP_uop f) \/
  (?f. op = FP_bop f) \/
  (?f. op = FP_top f) ==>
  ^op_goal
Proof
  rw [] \\ Cases_on `f` \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ simp [compile_op_def,evaluate_def,do_app_def]
QED

Theorem op_byte_arrays:
  op = Aw8length \/
  op = Aw8alloc \/
  op = Aw8sub_unsafe \/
  op = Aw8sub \/
  op = Aw8update_unsafe \/
  op = Aw8update ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ imp_res_tac lookup_byte_array
  \\ fs [compile_op_def,subscript_exn_v_def,v_rel_def]
  THEN1 fs [evaluate_def,do_app_def]
  THEN1
   (fs [evaluate_def,do_app_def,integerTheory.int_le]
    \\ rw [] \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ fs [store_alloc_def] \\ rveq \\ fs []
    \\ imp_res_tac state_rel_LEAST \\ fs []
    \\ fs [state_rel_def,store_rel_def,FLOOKUP_UPDATE,v_rel_def]
    \\ strip_tac
    \\ last_x_assum (qspec_then `i` mp_tac)
    \\ rename [`¬(k < 0)`]
    \\ `ABS k = k` by intLib.COOPER_TAC \\ simp []
    \\ Cases_on `i = LENGTH s1.refs` \\ fs [EL_APPEND2]
    \\ IF_CASES_TAC \\ fs [EL_APPEND1])
  THEN1
   (fs [evaluate_def,do_app_def,integerTheory.int_le]
    \\ rename [`¬(k < 0)`]
    \\ `Num (ABS k) < LENGTH ws' <=> k < &LENGTH ws'` by intLib.COOPER_TAC
    \\ fs [GREATER_EQ,GSYM NOT_LESS]
    \\ `ABS k = k` by intLib.COOPER_TAC \\ simp [])
  THEN1
   (fs [evaluate_def,do_app_def,integerTheory.int_le]
    \\ Cases_on `i < 0` \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ rename [`¬(k < 0)`]
    \\ `Num (ABS k) < LENGTH ws' <=> k < &LENGTH ws'` by intLib.COOPER_TAC
    \\ fs [GREATER_EQ,GSYM NOT_LESS]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ `ABS k = k` by intLib.COOPER_TAC \\ simp [])
  THEN1
   (fs [evaluate_def,do_app_def,integerTheory.int_le]
    \\ rename [`¬(k < 0)`]
    \\ `Num (ABS k) < LENGTH ws' <=> k < &LENGTH ws'` by intLib.COOPER_TAC
    \\ fs [GREATER_EQ,GSYM NOT_LESS]
    \\ fs [option_case_eq] \\ rveq \\ fs [v_rel_def,Unit_def,EVAL ``tuple_tag``]
    \\ rename [`store_v_same_type (EL j s1.refs)`]
    \\ Cases_on `EL j s1.refs` \\ fs [store_v_same_type_def]
    \\ fs [state_rel_def,store_rel_def]
    \\ strip_tac
    \\ last_x_assum (qspec_then `i` mp_tac)
    \\ fs [FLOOKUP_UPDATE] \\ IF_CASES_TAC \\ fs [EL_LUPDATE]
    \\ Cases_on `i = j` \\ fs []
    \\ rveq \\ fs [] \\ rpt strip_tac \\ rveq \\ fs []
    \\ `ABS k = k` by intLib.COOPER_TAC \\ simp [])
  THEN1
   (fs [evaluate_def,do_app_def,integerTheory.int_le]
    \\ rename [`¬(k < 0)`]
    \\ Cases_on `k < 0` \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ `Num (ABS k) < LENGTH ws' <=> k < &LENGTH ws'` by intLib.COOPER_TAC
    \\ fs [GREATER_EQ,GSYM NOT_LESS]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ fs [option_case_eq] \\ rveq \\ fs [v_rel_def,Unit_def,EVAL ``tuple_tag``]
    \\ rename [`store_v_same_type (EL j s1.refs)`]
    \\ Cases_on `EL j s1.refs` \\ fs [store_v_same_type_def]
    \\ fs [state_rel_def,store_rel_def]
    \\ strip_tac
    \\ last_x_assum (qspec_then `i` mp_tac)
    \\ fs [FLOOKUP_UPDATE] \\ IF_CASES_TAC \\ fs [EL_LUPDATE]
    \\ Cases_on `i = j` \\ fs []
    \\ rveq \\ fs [] \\ rpt strip_tac \\ rveq \\ fs []
    \\ `ABS k = k` by intLib.COOPER_TAC \\ simp [])
QED

Theorem op_byte_copy:
  op = CopyStrAw8 \/
  op = CopyAw8Str \/
  op = CopyAw8Aw8 \/
  op = CopyStrStr ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,CaseEq "store_v"]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM,v_rel_def] \\ rveq \\ fs []
  \\ imp_res_tac lookup_byte_array
  \\ fs [compile_op_def,subscript_exn_v_def,v_rel_def,CopyByteAw8_def,CopyByteStr_def]
  \\ simp [evaluate_def,do_app_def]
  THEN1
   (fs [copy_array_def]
    \\ qpat_x_assum `IS_SOME _ ==> _` mp_tac
    \\ rpt (IF_CASES_TAC \\ fs [ws_to_chars_def])
    \\ intLib.COOPER_TAC)
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ fs [Unit_def,EVAL ``tuple_tag``] \\ rveq \\ fs []
    \\ fs [state_rel_def,store_rel_def,v_rel_def]
    \\ strip_tac \\ last_x_assum (qspec_then `i` mp_tac)
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `i=dst` \\ fs []
    \\ fs [chars_to_ws_def,MAP_TAKE,MAP_DROP,MAP_MAP_o,o_DEF,ORD_CHR,
           integer_wordTheory.i2w_pos])
  THEN1
   (fs [copy_array_def]
    \\ rpt (IF_CASES_TAC \\ fs [ws_to_chars_def])
    \\ intLib.COOPER_TAC)
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ fs [MAP_MAP_o,o_DEF])
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ qpat_x_assum `IS_SOME _ ==> _` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rpt strip_tac \\ fs []
    \\ rpt (IF_CASES_TAC \\ fs [] \\ rpt strip_tac \\ fs [])
    \\ intLib.COOPER_TAC)
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ fs [Unit_def,EVAL ``tuple_tag``] \\ rveq \\ fs []
    \\ fs [state_rel_def,store_rel_def]
    \\ strip_tac \\ last_x_assum (qspec_then `i` mp_tac)
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `i=dst'` \\ fs [])
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ rpt (IF_CASES_TAC \\ fs [] \\ rpt strip_tac \\ fs [])
    \\ intLib.COOPER_TAC)
  THEN1
   (fs [copy_array_def] \\ fs [ws_to_chars_def]
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ intLib.COOPER_TAC)
    \\ fs [] \\ rveq \\ fs [MAP_TAKE,MAP_DROP])
QED

Theorem op_eq_gc:
  op = ConfigGC \/
  op = Equality ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS,SWAP_REVERSE_SYM] \\ rveq \\ fs []
  THEN1
   (ntac 2 (pop_assum mp_tac) \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rw [] \\ fs [compile_op_def,evaluate_def,do_app_def,Unit_def] \\ EVAL_TAC)
  \\ fs [CaseEq"eq_result"] \\ rveq \\ fs []
  \\ fs [compile_op_def,evaluate_def,do_app_def]
  \\ qsuff_tac `
       (!v1 v2 x1 x2 b.
         v_rel v1 x1 /\ v_rel v2 x2 /\ do_eq v1 v2 = Eq_val b ==>
         do_eq x1 x2 = Eq_val b) /\
       (!v1 v2 x1 x2 b.
         LIST_REL v_rel v1 x1 /\ LIST_REL v_rel v2 x2 /\ do_eq_list v1 v2 = Eq_val b ==>
         do_eq_list x1 x2 = Eq_val b)`
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ rpt (pop_assum kall_tac)
  \\ ho_match_mp_tac flatSemTheory.do_eq_ind \\ rw []
  \\ fs [v_rel_def,flatSemTheory.do_eq_def,bool_case_eq] \\ rveq \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  THEN1
   (rename [`lit_same_type l1 l2`]
    \\ Cases_on `l1` \\ Cases_on `l2` \\ fs [lit_same_type_def,v_rel_def]
    \\ fs [do_eq_def] \\ rveq \\ fs [ORD_11]
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ qid_spec_tac `l1`
    \\ Induct \\ Cases_on `l2` \\ fs [ORD_BOUND,ORD_11])
  \\ TRY (fs [do_eq_def] \\ rveq \\ fs [v_rel_def] \\ NO_TAC)
  \\ rveq \\ fs [ctor_same_type_def]
  \\ fs [CaseEq"eq_result",bool_case_eq] \\ rveq \\ fs []
  \\ fs [do_eq_def]
  \\ qpat_x_assum `Eq_val b = _` (assume_tac o GSYM)
  \\ res_tac \\ fs []
QED

Theorem v_rel_v_to_char_list:
  !x ls y.
    v_to_char_list x = SOME ls /\ v_rel x y ==>
    v_to_list y = SOME (MAP (Number ∘ $&) (MAP ORD ls))
Proof
  ho_match_mp_tac v_to_char_list_ind \\ rw []
  \\ fs [v_rel_def,v_to_list_def,v_to_char_list_def]
  \\ rveq \\ fs [option_case_eq] \\ rveq \\ fs []
QED

Theorem op_str:
  op = Explode \/
  op = Implode \/
  op = Strlen \/
  op = Strsub \/
  op = Strcat ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def,get_global_def,v_rel_def]
  \\ rveq \\ fs [SWAP_REVERSE_SYM]
  \\ rveq \\ fs [SWAP_REVERSE_SYM]
  THEN1
   (match_mp_tac IMP_v_rel_to_list \\ rename [`MAP _ xs`]
    \\ qid_spec_tac `xs` \\ Induct \\ fs [v_rel_def,ORD_BOUND])
  THEN1
   (imp_res_tac v_rel_v_to_char_list \\ fs []
    \\ `!xs. MAP (Number ∘ $&) (MAP ORD ls) =
             MAP (Number ∘ $&) xs <=> xs = (MAP ORD ls)` by
       (qid_spec_tac `ls` \\ Induct \\ Cases_on `xs`
        \\ fs [] \\ rw [] \\ eq_tac \\ rw[])
    \\ fs []
    \\ `(!xs. xs = MAP ORD ls /\ EVERY (λn. n < 256n) xs <=>
              xs = MAP ORD ls /\ EVERY (λn. n < 256n) (MAP ORD ls))` by
          metis_tac [] \\ fs []
    \\ `!ls. EVERY (λn. n < 256) (MAP ORD ls)` by (Induct \\ fs [ORD_BOUND]) \\ fs []
    \\ fs [MAP_MAP_o,stringTheory.IMPLODE_EXPLODE_I])
  THEN1
   (fs [integerTheory.int_le] \\ rename [`~(i4 < 0)`]
    \\ Cases_on `i4 < 0` \\ fs [] \\ rveq \\ fs [subscript_exn_v_def,v_rel_def]
    \\ rename [`i4 < &LENGTH str`] \\ fs [GREATER_EQ,GSYM NOT_LESS]
    \\ `Num (ABS i4) < STRLEN str <=> i4 < &STRLEN str` by intLib.COOPER_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [v_rel_def]
    \\ Cases_on `i4` \\ fs []
    \\ fs [EL_MAP,ORD_BOUND] \\ Cases_on `str` \\ fs [EL_MAP,ORD_BOUND])
  \\ qsuff_tac `!x vs str y.
        v_to_list x = SOME vs /\ vs_to_string vs = SOME str /\ v_rel x y ==>
        ?wss. v_to_list y = SOME (MAP ByteVector wss) /\
              MAP (CHR o w2n) (FLAT wss) = str`
  THEN1
   (rpt (disch_then drule \\ fs []) \\ strip_tac \\ fs []
    \\ `!xs ys. MAP ByteVector xs = MAP ByteVector ys <=> xs = ys` by
           (Induct \\ Cases_on `ys` \\ fs []) \\ fs [] \\ rveq
    \\ fs [MAP_MAP_o,o_DEF])
  \\ rpt (pop_assum kall_tac)
  \\ recInduct flatSemTheory.v_to_list_ind \\ rw [] \\ fs [v_rel_def]
  \\ rveq \\ fs [flatSemTheory.v_to_list_def] \\ rveq \\ fs [vs_to_string_def]
  \\ rveq \\ fs [] THEN1 (qexists_tac `[]` \\ EVAL_TAC)
  \\ fs [option_case_eq] \\ rveq
  \\ Cases_on `v1` \\ fs [flatSemTheory.v_to_list_def,vs_to_string_def]
  \\ Cases_on `l` \\ fs [flatSemTheory.v_to_list_def,vs_to_string_def,option_case_eq]
  \\ rveq \\ fs [v_rel_def,v_to_list_def,option_case_eq,PULL_EXISTS]
  \\ res_tac \\ fs [] \\ rveq \\ fs []
  \\ qexists_tac `(MAP (n2w ∘ ORD) s) :: wss`
  \\ fs [MAP_MAP_o,o_DEF,ORD_BOUND,CHR_ORD]
QED

Theorem op_globals:
  (?n. op = GlobalVarLookup n) \/
  (?n. op = GlobalVarInit n) \/
  (?n. op = GlobalVarAlloc n) ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def,get_global_def]
  THEN1
   (Cases_on `EL n s1.globals` \\ fs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [LIST_REL_EL] \\ res_tac \\ fs []
    \\ qpat_x_assum `_ = SOME x` assume_tac
    \\ Cases_on `EL n t.globals` \\ fs [])
  THEN1
   (fs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [LIST_REL_EL] \\ res_tac \\ fs []
    \\ qpat_x_assum `_ = NONE` assume_tac
    \\ Cases_on `EL n t1.globals` \\ fs []
    \\ fs [EL_LUPDATE]
    \\ simp [Once v_rel_cases,Unit_def]
    \\ rw [] \\ EVAL_TAC)
  \\ simp [Once v_rel_cases,Unit_def]
  \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
  \\ qsuff_tac `!n db (t:('c,'ffi) closSem$state).
       evaluate ([AllocGlobals tt n],db,t) =
         (Rval [Block 0 []],t with globals := t.globals ++ REPLICATE n NONE)`
  THEN1
   (fs [state_rel_def] \\ rw []
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
    \\ qid_spec_tac `n` \\ Induct \\ fs [])
  \\ Induct \\ simp [Once AllocGlobals_def,evaluate_def,do_app_def]
  THEN1 (fs [state_component_equality])
  \\ rw []
  THEN1 (simp [Once AllocGlobals_def,evaluate_def,do_app_def,Unit_def] \\ EVAL_TAC)
  \\ simp [evaluate_def,do_app_def,Unit_def]
  \\ fs [state_component_equality]
QED

Theorem op_vectors:
  op = Vlength \/
  op = Vsub \/
  op = VfromList ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [v_rel_def] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs [SWAP_REVERSE_SYM]
  THEN1
   (rveq \\ fs [] \\ rename [`0 <= i5`]
    \\ Cases_on `i5` \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ fs [subscript_exn_v_def,v_rel_def,GREATER_EQ]
    \\ fs [LIST_REL_EL]
    \\ first_x_assum (qspec_then `0` mp_tac) \\ fs []
    \\ rename [`wss <> []`] \\ Cases_on `wss` \\ fs [])
  \\ rename [`v_rel x y`]
  \\ imp_res_tac v_rel_to_list \\ fs []
QED

Theorem op_arrays:
  op = Aalloc \/
  op = Asub_unsafe \/
  op = Asub \/
  op = Alength \/
  op = Aupdate_unsafe \/
  op = Aupdate ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq,store_alloc_def]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [v_rel_def] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs [SWAP_REVERSE_SYM,list_case_eq]
  \\ rveq \\ fs [bool_case_eq] \\ rveq \\ fs []
  \\ fs [subscript_exn_v_def,v_rel_def,integerTheory.INT_NOT_LT,CaseEq"store_v"]
  \\ rveq \\ fs [PULL_EXISTS]
  \\ imp_res_tac state_rel_LEAST \\ fs []
  THEN1
   (rename [`0<=i`]
    \\ `Num (ABS i) = Num i` by intLib.COOPER_TAC \\ fs []
    \\ fs [state_rel_def,store_rel_def,EL_LUPDATE]
    \\ strip_tac
    \\ first_x_assum (qspec_then `i'` mp_tac)
    \\ IF_CASES_TAC
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE,EL_APPEND1,EL_APPEND2]
    \\ Cases_on `LENGTH s1.refs = i'` \\ fs [] \\ rveq \\ fs [] \\ rw []
    \\ qspec_tac (`Num i`,`j`) \\ Induct \\ fs [])
  THEN1
   (imp_res_tac lookup_array \\ fs [GREATER_EQ,GSYM NOT_LESS,v_rel_def]
    \\ fs [bool_case_eq] \\ rveq \\ fs [integerTheory.int_le]
    \\ fs [v_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [PULL_EXISTS]
    \\ rename [`i6 < _:int`]
    \\ reverse IF_CASES_TAC THEN1 `F` by intLib.COOPER_TAC \\ fs []
    \\ fs [LIST_REL_EL]
    \\ Cases_on `i6` \\ fs []
    \\ first_x_assum (qspec_then `0` mp_tac)
    \\ Cases_on `ws` \\ fs [])
  THEN1
   (imp_res_tac lookup_array \\ fs [GREATER_EQ,GSYM NOT_LESS,v_rel_def]
    \\ fs [bool_case_eq] \\ rveq \\ fs [integerTheory.int_le]
    \\ fs [v_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH THEN1 intLib.COOPER_TAC
    \\ fs [PULL_EXISTS]
    \\ rename [`i6 < _:int`]
    \\ Cases_on `i6` \\ fs []
    \\ fs [LIST_REL_EL]
    \\ first_x_assum (qspec_then `0` mp_tac)
    \\ Cases_on `ws` \\ fs [])
  THEN1
   (imp_res_tac lookup_array \\ fs [GREATER_EQ,GSYM NOT_LESS,v_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ decide_tac)
  THEN1
   (imp_res_tac lookup_array \\ fs [GREATER_EQ,GSYM NOT_LESS,v_rel_def]
    \\ fs [bool_case_eq,CaseEq"option"]
    \\ rveq \\ fs [integerTheory.int_le,v_rel_def]
    \\ rename [`~(i7 < 0i)`]
    \\ `Num (ABS i7) = Num i7 /\
        (i7 < &LENGTH ws <=> Num i7 < LENGTH ws)` by intLib.COOPER_TAC
    \\ fs [] \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [option_case_eq] \\ rveq \\ fs [v_rel_def,Unit_def,EVAL ``tuple_tag``]
    \\ fs [state_rel_def,store_rel_def,EL_LUPDATE]
    \\ strip_tac
    \\ first_x_assum (qspec_then `i` mp_tac)
    \\ IF_CASES_TAC
    \\ fs [FLOOKUP_UPDATE,EL_LUPDATE,EL_APPEND1,EL_APPEND2]
    \\ IF_CASES_TAC \\ fs []
    \\ CASE_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [LUPDATE_def]
    \\ match_mp_tac EVERY2_LUPDATE_same \\ fs [])
  \\ imp_res_tac lookup_array \\ fs [GREATER_EQ,GSYM NOT_LESS,v_rel_def]
  \\ fs [bool_case_eq] \\ rveq \\ fs [integerTheory.int_le,v_rel_def]
  \\ rename [`~(i7 < 0i)`]
  \\ `Num (ABS i7) = Num i7 /\
      (i7 < &LENGTH ws <=> Num i7 < LENGTH ws)` by intLib.COOPER_TAC
  \\ fs [] \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ qpat_x_assum `SOME (s2,res2) = _` (assume_tac o GSYM)
  \\ fs [option_case_eq] \\ rveq \\ fs [v_rel_def,Unit_def,EVAL ``tuple_tag``]
  \\ fs [state_rel_def,store_rel_def,EL_LUPDATE]
  \\ strip_tac
  \\ first_x_assum (qspec_then `i` mp_tac)
  \\ IF_CASES_TAC
  \\ fs [FLOOKUP_UPDATE,EL_LUPDATE,EL_APPEND1,EL_APPEND2]
  \\ IF_CASES_TAC \\ fs []
  \\ CASE_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [LUPDATE_def]
  \\ match_mp_tac EVERY2_LUPDATE_same \\ fs []
QED

Theorem op_blocks:
  (?n0 n1. op = TagLenEq n0 n1) \/
  (?l. op = LenEq l) \/
  op = ListAppend ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [v_rel_def] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs [SWAP_REVERSE_SYM,list_case_eq]
  \\ rveq \\ fs []
  \\ imp_res_tac v_rel_to_list \\ fs []
  \\ rveq \\ fs []
  \\ match_mp_tac IMP_v_rel_to_list
  \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
QED

Theorem op_ffi:
  (?n. op = FFI n) ==>
  ^op_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS,
         CaseEq "ast$lit",store_assign_def,option_case_eq]
  \\ rw [] \\ fs [] \\ rveq \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
  \\ fs [v_rel_def] \\ rveq \\ fs [PULL_EXISTS]
  \\ fs [compile_op_def,evaluate_def,do_app_def,arg1_def]
  \\ fs [CaseEq "store_v",CaseEq"ffi_result",option_case_eq,bool_case_eq]
  \\ rveq \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
  \\ imp_res_tac lookup_byte_array \\ fs []
  \\ `t1.ffi = s1.ffi` by fs[state_rel_def] \\ fs [o_DEF]
  \\ fs [v_rel_def,Unit_def,EVAL ``tuple_tag``]
  \\ fs [state_rel_def,store_rel_def,EL_LUPDATE]
  \\ strip_tac
  \\ first_x_assum (qspec_then `i` mp_tac)
  \\ IF_CASES_TAC \\ fs [FLOOKUP_UPDATE]
  \\ IF_CASES_TAC \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem op_eval:
  op = Eval ==>
  ^op_goal
Proof
  simp [compile_op_def, flatSemTheory.do_app_def]
QED

Theorem compile_op_correct:
  ^op_goal
Proof
  EVERY (map assume_tac
    [op_refs, op_chars, op_ints, op_words, op_str, op_shifts,
     op_floats, op_eq_gc, op_byte_arrays, op_vectors, op_arrays,
     op_globals, op_blocks, op_ffi, op_byte_copy, op_eval])
  \\ `?this_is_case. this_is_case op` by (qexists_tac `K T` \\ fs [])
  \\ rpt strip_tac \\ fs [] \\ Cases_on `op` \\ fs []
QED

Theorem v_rel_to_words:
  !x y xs. v_rel x y /\ flatSem$v_to_words x = SOME xs ==>
           ?ys. closSem$v_to_words y = SOME xs
Proof
  simp [flatSemTheory.v_to_words_def, closSemTheory.v_to_words_def]
  \\ rpt gen_tac
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ rpt strip_tac
  \\ fs []
  \\ drule_then drule v_rel_to_list
  >- (
    simp [LIST_REL_MAP1, CONV_RULE (DEPTH_CONV ETA_CONV) LIST_REL_MAP2]
    \\ simp [v_rel_def, EQ_SYM_EQ, ETA_THM]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ simp []
  )
  \\ strip_tac
  \\ last_x_assum (qspec_then `xs` mp_tac)
  \\ rveq \\ fs []
  \\ simp [Once EQ_SYM_EQ]
  \\ full_simp_tac bool_ss [LIST_REL_MAP1, GSYM LIST_REL_eq]
  \\ first_x_assum mp_tac
  \\ match_mp_tac LIST_REL_mono
  \\ simp [Once v_rel_cases]
QED

Theorem v_rel_to_bytes:
  !x y xs. v_rel x y /\ flatSem$v_to_bytes x = SOME xs ==>
           ?ys. closSem$v_to_bytes y = SOME xs
Proof
  simp [flatSemTheory.v_to_bytes_def, closSemTheory.v_to_bytes_def]
  \\ rpt gen_tac
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ rpt strip_tac
  \\ fs []
  \\ drule_then drule v_rel_to_list
  >- (
    simp [LIST_REL_MAP1, CONV_RULE (DEPTH_CONV ETA_CONV) LIST_REL_MAP2]
    \\ simp [v_rel_def, EQ_SYM_EQ, ETA_THM]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ simp []
  )
  \\ strip_tac
  \\ last_x_assum (qspec_then `xs` mp_tac)
  \\ rveq \\ fs []
  \\ simp [Once EQ_SYM_EQ]
  \\ full_simp_tac bool_ss [LIST_REL_MAP1, GSYM LIST_REL_eq]
  \\ first_x_assum mp_tac
  \\ match_mp_tac LIST_REL_mono
  \\ simp [Once v_rel_cases]
QED

Theorem do_eval_install:
  do_eval xs s.eval_config = SOME res /\
  state_rel s t /\
  LIST_REL v_rel xs ys ==>
  ?decs exps eval_config t'. state_rel (s with eval_config := eval_config) t' /\
  res = (decs, eval_config, Unitv) /\
  do_install ys t = (if t'.clock = 0
    then (Rerr (Rabort Rtimeout_error), t')
    else (Rval (exps ++ compile [] [Con None NONE []]), dec_clock 1 t')) /\
  no_Mat_decs decs /\
  (?envv dsv. xs = [envv; dsv]) /\
  (t'.clock <> 0 ==> exps = compile_decs decs)
Proof
  rw []
  \\ `install_config_rel s.eval_config t.compile_oracle t.compile`
    by fs [state_rel_def]
  \\ fs [install_config_rel_def]
  \\ fs [do_eval_def, case_eq_thms]
  \\ fs [listTheory.SWAP_REVERSE_SYM]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs [case_eq_thms, pair_case_eq]
  \\ rveq \\ fs []
  \\ drule_then drule v_rel_to_bytes
  \\ drule_then drule v_rel_to_words
  \\ rw []
  \\ fs [do_install_def, pure_co_def |> REWRITE_RULE [FUN_EQ_THM],
    shift_seq_def |> REWRITE_RULE [FUN_EQ_THM]]
  \\ fs [pure_cc_def, inc_compile_decs_def, compile_decs_def]
  \\ qexists_tac `compile_decs decs`
  \\ qexists_tac `t with <| compile_oracle := shift_seq 1 t.compile_oracle;
        code := t.code |++ [] |>`
  \\ conj_tac
  >- (
    fs [state_rel_def, install_config_rel_def, shift_seq_def, o_DEF]
  )
  \\ first_x_assum (qspec_then `0` mp_tac)
  \\ simp [dec_clock_def, bool_case_eq]
  \\ simp [state_component_equality]
QED

Theorem dest_nop_thm:
  dest_nop op es = SOME x ⇔
    (∃t. op = WordFromInt W8 ∧ es = [App t Ord [x]]) ∨
    (∃t. op = Chr ∧ es = [App t (WordToInt W8) [x]])
Proof
  Cases_on ‘op’ \\ fs [dest_nop_def] \\ every_case_tac \\ fs []
QED

Theorem compile_single_DEEP_INTRO:
  !P. (!exp'. flat_to_clos$compile m [exp] = [exp'] ==> P [exp']) ==>
  P (flat_to_clos$compile m [exp])
Proof
  qspecl_then [`m`, `[exp]`] assume_tac LENGTH_compile
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2]
QED

Theorem compile_App:
  ^(get_goal "flatLang$App")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ rfs [pair_case_eq]
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac
  \\ Cases_on `op = Opapp` \\ fs []
  THEN1
   (fs [compile_op_def,dest_nop_def] \\ rveq
    \\ reverse (fs [result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs [])
    THEN1
     (Cases_on `compile m (REVERSE es)` \\ fs [arg2_def]
      \\ fs [evaluate_def]
      \\ rename [`_ = _::ys`] \\ Cases_on `ys` \\ fs [arg2_def]
      \\ fs [evaluate_def]
      \\ rename [`_ = _::_::ys`] \\ Cases_on `ys` \\ fs [arg2_def]
      \\ fs [evaluate_def] \\ fs [pair_case_eq,result_case_eq])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ fs [flatSemTheory.do_opapp_def]
    \\ `?f x. vs = [x;f]` by fs [list_case_eq,SWAP_REVERSE_SYM]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `?ef ex. es = [ex;ef]` by
      (imp_res_tac evaluate_IMP_LENGTH \\ fs [LENGTH_compile]
       \\ Cases_on `es` \\ fs [] \\ Cases_on `t'` \\ fs [])
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `compile m [ef; ex] = HD (compile m [ef]) :: HD (compile m [ex]) :: []` by
          fs [compile_def,LENGTH_compile]
    \\ asm_rewrite_tac [arg2_def] \\ fs []
    \\ fs [evaluate_def,LENGTH_compile]
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ once_rewrite_tac [evaluate_CONS] \\ fs []
    \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ `?vx. v = [vx]` by
        (imp_res_tac evaluate_IMP_LENGTH \\ fs [LENGTH_compile] \\ Cases_on `v` \\ fs [])
    \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ Cases_on `f` \\ fs [] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ strip_tac \\ fs []
    \\ rename [`state_rel s1 t1`]
    \\ `1 <= t1.max_app /\ t1.clock = s1.clock` by fs [state_rel_def]
    \\ fs [dest_closure_def,check_loc_def] \\ rveq \\ fs []
    THEN1
     (Cases_on `s1.clock = 0`
      THEN1 (fs [] \\ fs [state_rel_def] \\ rveq \\ fs[])
      \\ fs []
      \\ rename [`compile (SOME vn::m1) [e],vx::db1,dec_clock 1 t1`]
      \\ `state_rel (dec_clock s1) (dec_clock 1 t1)` by
           fs [flatSemTheory.dec_clock_def,dec_clock_def,state_rel_def]
      \\ first_x_assum drule
      \\ `env_rel (e' with v updated_by (λenv. (vn,x)::env))
                (SOME vn::m1) (vx::db1)` by
            (ho_match_mp_tac env_rel_CONS_upd \\ fs [env_rel_def])
      \\ disch_then drule \\ strip_tac \\ fs []
      \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_sing \\ rveq \\ fs [])
    \\ fs [EL_MAP]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
    \\ Cases_on `s1.clock = 0`
    THEN1 (fs [] \\ fs [state_rel_def] \\ rveq \\ fs[])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ `state_rel (dec_clock s1) (dec_clock 1 t1)` by
         fs [flatSemTheory.dec_clock_def,dec_clock_def,state_rel_def]
    \\ first_x_assum drule
    \\ qpat_x_assum `ALL_DISTINCT (MAP FST l0)` assume_tac
    \\ fs [find_recfun_EL]
    \\ qpat_x_assum `SND (EL n l0) = (_,_)` assume_tac
    \\ drule IMP_PAIR \\ strip_tac \\ rveq
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate (compile m2 _, db2, _)`
    \\ disch_then (qspecl_then [`m2`,`db2`] mp_tac)
    \\ reverse impl_tac
    THEN1
     (strip_tac \\ fs []
      \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
      \\ Cases_on `res1` \\ fs []
      \\ rveq \\ fs [] \\ imp_res_tac evaluate_sing \\ fs [])
    \\ unabbrev_all_tac
    \\ reverse conj_tac
    THEN1 (fs [EVERY_EL] \\ fs [EL_MAP])
    \\ fs []
    \\ match_mp_tac env_rel_CONS
    \\ fs [build_rec_env_eq_MAP]
    \\ match_mp_tac env_rel_APPEND \\ fs []
    \\ fs [MAP_MAP_o,o_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
    \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [] \\ rw []
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rename [`env_rel env3 m3 db3`]
    \\ qexists_tac `m3` \\ fs []
    \\ fs [o_DEF])
  \\ Cases_on `op = Eval`
  THEN1 (
    simp [compile_op_def, evaluate_def, dest_nop_def]
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs []
    \\ drule (Q.INST [`ys` |-> `REVERSE zs`] do_eval_install)
    \\ simp []
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ drule_then strip_assume_tac state_rel_dec_clock
    \\ fs []
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ fs [Q.ISPEC `(x, y)` EQ_SYM_EQ, pair_case_eq]
    \\ fs []
    \\ last_x_assum drule
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ fs [option_case_eq] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [evaluate_append, compile_def, evaluate_def, do_app_def]
    \\ simp [v_rel_def, Unitv_def]
  )
  \\ Cases_on ‘dest_nop op es’
  THEN1
   (reverse (fs [result_case_eq])
    \\ rveq \\ fs [] \\ rveq \\ fs []
    THEN1 (drule compile_op_evaluates_args \\ fs [])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ rename [`state_rel s1 t1`,`LIST_REL v_rel vs ws`,`_ = SOME (s2,res2)`]
    \\ qmatch_goalsub_rename_tac `compile_op tt op cexps`
    \\ drule EVERY2_REVERSE
    \\ qmatch_goalsub_rename_tac `LIST_REL _ vvs`
    \\ fs [] \\ rw []
    \\ match_mp_tac (GEN_ALL compile_op_correct)
    \\ rpt (asm_exists_tac \\ fs [])
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ gvs [dest_nop_thm] \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ qpat_x_assum ‘_ = (_,_)’ mp_tac
  \\ simp [Once compile_def,dest_nop_def,compile_op_def]
  \\ fs [arg1_def]
  \\ DEEP_INTRO_TAC compile_single_DEEP_INTRO \\ ntac 2 strip_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ fs [flatSemTheory.evaluate_def,AllCaseEqs(),PULL_EXISTS]
  \\ fs [flatSemTheory.do_app_def,AllCaseEqs(),PULL_EXISTS]
  THEN1
   (rw [] \\ fs [] \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rw [] \\ gvs [integer_wordTheory.i2w_pos,ORD_BOUND])
  \\ Cases \\ fs [do_word_to_int_def] \\ strip_tac \\ gvs []
  \\ ‘w2n c < dimword (:8)’ by fs [w2n_lt] \\ fs []
  \\ ‘¬(&w2n c > 255i)’ by intLib.COOPER_TAC \\ fs[]
  \\ rw [] \\ fs [] \\ gvs []
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
QED

Theorem compile_Dlet:
  ^(get_goal "Dlet")
Proof
  rw []
  \\ fs [flatSemTheory.evaluate_def, pair_case_eq]
  \\ fs [compile_decs_def]
  \\ first_x_assum (qspecl_then [`[]`, `[]`] drule)
  \\ simp [env_rel_def]
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ strip_tac
  \\ fs []
  \\ fs [case_eq_thms, bool_case_eq]
  \\ rveq \\ fs []
QED

Theorem compile_Dtype_Dexn:
  ^(get_goal "Dtype") /\ ^(get_goal "Dexn")
Proof
  rw []
  \\ fs [compile_decs_def, flatSemTheory.evaluate_def, evaluate_def]
  \\ fs [case_eq_thms, bool_case_eq]
  \\ rveq \\ fs []
  \\ fs [state_rel_def]
QED

Theorem compile_decs_nil:
  ^(get_goal "evaluate_decs _ []")
Proof
  rw []
  \\ fs [compile_decs_def, flatSemTheory.evaluate_def, evaluate_def]
  \\ rveq \\ fs []
QED

Theorem compile_decs_cons:
  ^(get_goal "evaluate_decs _ (_ :: ds)")
Proof
  rw []
  \\ fs [compile_decs_def, flatSemTheory.evaluate_def, evaluate_def]
  \\ fs [pair_case_eq]
  \\ fs []
  \\ first_x_assum drule
  \\ reverse (fs [option_case_eq])
  >- (
    rveq \\ fs []
    \\ Cases_on `d` \\ fs []
    \\ fs [compile_decs_def, evaluate_append]
    \\ rw []
    \\ fs [evaluate_def]
  )
  \\ Cases_on `d` \\ fs []
  \\ fs [compile_decs_def, evaluate_append]
  \\ rw []
  \\ first_x_assum drule
  \\ rw []
  \\ fs [evaluate_def]
  \\ rveq \\ fs []
  \\ EVERY_CASE_TAC \\ fs []
  \\ metis_tac [LIST_REL_APPEND_suff]
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_nil, compile_cons,
       compile_Lit, compile_Handle, compile_Raise, compile_Let,
       compile_Letrec, compile_Fun, compile_Con, compile_App,
       compile_If, compile_Mat, compile_Var_local, compile_Dlet,
       compile_Dtype_Dexn, compile_decs_nil, compile_decs_cons])
  \\ asm_rewrite_tac []
QED

Theorem compile_decs_correct = last (CONJUNCTS compile_correct)

Theorem compile_decs_correct2:
  evaluate_decs s1 decs = res_tup /\
  evaluate (compile_decs decs, [], s2) = (res2, t2) /\
  state_rel s1 s2 /\ no_Mat_decs decs /\
  SND res_tup ≠ SOME (Rabort Rtype_error) ==>
  state_rel (FST res_tup) t2 /\
  result_rel (\x y. T) v_rel
    (case SND res_tup of NONE => Rval [] | SOME e => Rerr e) res2
Proof
  PairCases_on `res_tup`
  \\ rw []
  \\ drule_then drule compile_decs_correct
  \\ simp []
  \\ rw []
  \\ CASE_TAC \\ fs []
QED

Theorem FST_SND_EQ_CASE:
  FST = (\(a, b). a) /\ SND = (\(a, b). b)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem compile_semantics:
   0 < max_app /\ no_Mat_decs ds /\ install_config_rel ec co cc ==>
   flatSem$semantics ec (ffi:'ffi ffi_state) ds ≠ Fail ==>
   closSem$semantics ffi max_app FEMPTY co cc (compile_decs ds) =
   flatSem$semantics ec ffi ds
Proof
  strip_tac
  \\ simp[flatSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ simp[]
  \\ conj_tac >- (
    rw[] \\ simp[closSemTheory.semantics_def]
    \\ IF_CASES_TAC \\ fs[]
    THEN1
     (
      qhdtm_x_assum`flatSem$evaluate_decs`kall_tac
      \\ last_x_assum(qspec_then`k'`mp_tac) \\ simp[]
      \\ fs [FST_SND_EQ_CASE]
      \\ rpt (pairarg_tac \\ fs [])
      \\ drule_then drule compile_decs_correct2
      \\ simp [state_rel_initial_state]
      \\ CCONTR_TAC \\ fs [] \\ fs []
      \\ fs [option_case_eq])
    \\ DEEP_INTRO_TAC some_intro \\ simp[]
    \\ conj_tac >- (
      rw[]
      \\ qmatch_assum_abbrev_tac`flatSem$evaluate_decs ss es = _`
      \\ qmatch_assum_abbrev_tac`closSem$evaluate bp = _`
      \\ fs [option_case_eq,result_case_eq]
      \\ drule (Q.GENL [`extra`, `res2`, `s2`]
            evaluate_decs_add_to_clock_io_events_mono_alt)
      \\ Q.ISPEC_THEN`bp`(mp_tac o Q.GEN`extra`)
            (CONJUNCT1 closPropsTheory.evaluate_add_to_clock_io_events_mono)
      \\ simp[Abbr`ss`,Abbr`bp`]
      \\ disch_then(qspec_then`k`strip_assume_tac)
      \\ disch_then(qspec_then`k'`strip_assume_tac)
      \\ drule(GEN_ALL(SIMP_RULE std_ss [](CONJUNCT1 closPropsTheory.evaluate_add_to_clock)))
      \\ disch_then(qspec_then `k` mp_tac)
      \\ impl_tac >- rpt(PURE_FULL_CASE_TAC \\ fs[])
      \\ drule(GEN_ALL(SIMP_RULE std_ss []
           (ONCE_REWRITE_RULE [CONJ_COMM] flatPropsTheory.evaluate_decs_add_to_clock)))
      \\ disch_then(qspec_then `k'` mp_tac)
      \\ impl_tac >- rpt(PURE_FULL_CASE_TAC \\ fs[])
      \\ ntac 2 strip_tac \\ fs[]
      \\ drule_then drule compile_decs_correct2
      \\ simp [flatPropsTheory.initial_state_clock,
               closPropsTheory.initial_state_clock,
               state_rel_initial_state]
      \\ impl_tac >- (CCONTR_TAC \\ fs [])
      \\ strip_tac \\ unabbrev_all_tac \\ fs[]
      \\ fs[initial_state_def] \\ rfs[]
      \\ rveq \\ fs []
      \\ every_case_tac
      \\ fs[state_component_equality] \\ fs [state_rel_def])
    \\ qexists_tac `k`
    \\ simp [PAIR_FST_SND_EQ]
    \\ simp [FST_SND_EQ_CASE]
    \\ pairarg_tac \\ fs []
    \\ drule_then drule compile_decs_correct2
    \\ simp [state_rel_initial_state]
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs []
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ fs [GSYM IMP_DISJ_THM]
  \\ simp[closSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs [] >- (
    last_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ drule_then drule compile_decs_correct2
    \\ simp [state_rel_initial_state]
    \\ res_tac
    \\ every_case_tac
  )
  \\ DEEP_INTRO_TAC some_intro \\ simp[]
  \\ conj_tac >- (
    spose_not_then strip_assume_tac
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ simp [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ CCONTR_TAC
    \\ drule_then drule compile_decs_correct2
    \\ simp [state_rel_initial_state]
    \\ res_tac
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM] \\ gen_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp [FST_SND_EQ_CASE]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule_then drule compile_decs_correct2
  \\ simp [state_rel_initial_state]
  \\ last_x_assum (qspec_then `k` mp_tac)
  \\ simp []
  \\ simp [state_rel_def]
QED

Theorem contains_App_SOME_APPEND:
  closProps$contains_App_SOME ma (xs ++ ys) <=>
  closProps$contains_App_SOME ma xs \/ closProps$contains_App_SOME ma ys
Proof
  simp [Once closPropsTheory.contains_App_SOME_EXISTS]
  \\ simp [GSYM closPropsTheory.contains_App_SOME_EXISTS]
QED

val props_defs = [closPropsTheory.contains_App_SOME_def,
    closPropsTheory.every_Fn_vs_NONE_def,
    closPropsTheory.no_mti_def, Q.ISPEC `no_mti` ETA_THM,
    closPropsTheory.esgc_free_def]

Theorem EVERY_IMP_HD:
  EVERY P xs /\ ~ NULL xs ==> P (HD xs)
Proof
  Cases_on `xs` \\ simp []
QED

Theorem elist_globals_empty:
   !es. closProps$elist_globals es = {||} <=>
        !e. MEM e es ==> set_globals e = {||}
Proof
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem compile_set_globals:
  ∀m e. EVERY no_Mat e ==>
  closProps$elist_globals (compile m e) = flatProps$elist_globals e
Proof
  ho_match_mp_tac flat_to_closTheory.compile_ind
  \\ simp [compile_def, elist_globals_REVERSE]
  \\ rw []
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ gvs [dest_nop_thm]
  \\ TRY
    (rename [‘dest_nop op es’] \\ reverse (Cases_on ‘dest_nop op es’) \\ fs []
     THEN1 (gvs [dest_nop_thm] \\ fs [flatPropsTheory.op_gbag_def])
     \\ last_x_assum kall_tac)
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_lit _ lit` \\ Cases_on `lit`
    \\ simp [compile_lit_def])
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_op _ op` \\ Cases_on `op`
    \\ simp ([compile_op_def] @ props_defs)
    \\ rpt (CASE_TAC \\ simp props_defs))
  \\ TRY (qmatch_goalsub_abbrev_tac `AllocGlobals _ n` \\ Induct_on `n`
    \\ simp [Once AllocGlobals_def]
    \\ rw props_defs)
  \\ simp [compile_def, closPropsTheory.op_gbag_def,
    flatPropsTheory.op_gbag_def, closPropsTheory.elist_globals_append]
  \\ rpt (
    DEEP_INTRO_TAC compile_single_DEEP_INTRO
    \\ rw [] \\ fs []
  )
  \\ fs [dest_nop_def]
  \\ simp ([CopyByteAw8_def, CopyByteStr_def] @ props_defs)
  \\ simp [arg1_def, arg2_def]
  \\ EVERY_CASE_TAC
  \\ simp [flatPropsTheory.op_gbag_def, closPropsTheory.op_gbag_def]
  \\ fs [Q.ISPEC `{||}` EQ_SYM_EQ, COMM_BAG_UNION]
  \\ rpt (DEEP_INTRO_TAC compile_single_DEEP_INTRO
    \\ rw [] \\ fs [])
  \\ fs [dest_pat_def]
  \\ simp [flatPropsTheory.elist_globals_FOLDR,
        closPropsTheory.elist_globals_FOLDR]
  \\ irule FOLDR_CONG
  \\ simp [MAP_MAP_o]
  \\ irule MAP_CONG
  \\ simp [FORALL_PROD]
  \\ rw []
  \\ fs [EVERY_MAP]
  \\ fs [EVERY_MEM]
  \\ res_tac
  \\ fs []
  \\ qpat_x_assum `_ = flatProps$set_globals _` (assume_tac o GSYM)
  \\ simp []
  \\ rpt (DEEP_INTRO_TAC compile_single_DEEP_INTRO
    \\ rw [] \\ fs [])
QED

Theorem compile_eq_set_globals:
  flat_to_clos$compile m exps = exps' /\
  EVERY no_Mat exps ==>
  closProps$elist_globals exps' = flatProps$elist_globals exps
Proof
  metis_tac [compile_set_globals]
QED

Theorem compile_decs_set_globals:
  ∀decs. no_Mat_decs decs ==>
  closProps$elist_globals (compile_decs decs) =
  flatProps$elist_globals (MAP dest_Dlet (FILTER is_Dlet decs))
Proof
  Induct
  \\ simp [compile_decs_def]
  \\ Cases
  \\ simp [compile_decs_def, closPropsTheory.elist_globals_append]
  \\ simp [compile_set_globals]
QED

Theorem compile_esgc_free:
  !m e. EVERY flatProps$esgc_free e /\ EVERY no_Mat e ==>
    EVERY closProps$esgc_free (flat_to_clos$compile m e)
Proof
  ho_match_mp_tac compile_ind
  \\ simp [compile_def, closPropsTheory.esgc_free_def]
  \\ simp [EVERY_REVERSE]
  \\ rw []
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ TRY
    (rename [‘dest_nop op es’] \\ reverse (Cases_on ‘dest_nop op es’) \\ fs []
     THEN1 (gvs [dest_nop_thm])
     \\ last_x_assum kall_tac)
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_lit _ lit` \\ Cases_on `lit`
    \\ simp [compile_lit_def])
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_op _ op` \\ Cases_on `op`
    \\ simp ([compile_op_def] @ props_defs)
    \\ rpt (CASE_TAC \\ simp props_defs))
  \\ TRY (qmatch_goalsub_abbrev_tac `AllocGlobals _ n` \\ Induct_on `n`
    \\ simp [Once AllocGlobals_def]
    \\ rw props_defs)
  \\ simp [compile_def, closPropsTheory.op_gbag_def,
    flatPropsTheory.op_gbag_def, closPropsTheory.elist_globals_append]
  \\ rpt (
    DEEP_INTRO_TAC compile_single_DEEP_INTRO
    \\ rw [] \\ fs []
  )
  \\ fs [dest_nop_def]
  \\ simp ([CopyByteAw8_def, CopyByteStr_def] @ props_defs)
  \\ simp [arg1_def, arg2_def]
  \\ EVERY_CASE_TAC
  \\ simp [flatPropsTheory.op_gbag_def, closPropsTheory.op_gbag_def]
  \\ fs [Q.ISPEC `{||}` EQ_SYM_EQ, EVERY_REVERSE]
  \\ imp_res_tac compile_eq_set_globals
  \\ fs []
  \\ rpt (DEEP_INTRO_TAC compile_single_DEEP_INTRO
    \\ rw [] \\ fs [])
  \\ fs [dest_pat_def]
  \\ simp [elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS]
  \\ fs [flatPropsTheory.elist_globals_eq_empty,
    FORALL_PROD, MEM_MAP, PULL_EXISTS]
  \\ rw []
  \\ res_tac
  \\ DEEP_INTRO_TAC compile_single_DEEP_INTRO
  \\ rw [] \\ fs []
  \\ imp_res_tac compile_eq_set_globals
  \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ res_tac
  \\ fs []
QED

Theorem compile_decs_esgc_free:
  !decs. EVERY (flatProps$esgc_free o dest_Dlet) (FILTER is_Dlet decs) /\
  no_Mat_decs decs ==>
  EVERY closProps$esgc_free (compile_decs decs)
Proof
  Induct
  \\ simp [compile_decs_def]
  \\ Cases
  \\ simp [compile_decs_def]
  \\ simp [compile_esgc_free]
QED

Theorem compile_syntactic_props:
  0 < max_app ⇒ ∀m e.
    ¬closProps$contains_App_SOME max_app (compile m e) /\
    EVERY closProps$no_mti (compile m e) /\
    closProps$every_Fn_vs_NONE (compile m e)
Proof
  disch_tac
  \\ ho_match_mp_tac compile_ind
  \\ simp ([compile_def] @ props_defs)
  \\ simp [contains_App_SOME_APPEND, EVERY_REVERSE]
  \\ rw []
  \\ TRY
    (rename [‘dest_nop op es’] \\ reverse (Cases_on ‘dest_nop op es’) \\ fs [])
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_lit _ lit` \\ Cases_on `lit`
    \\ simp [compile_lit_def])
  \\ TRY (qmatch_goalsub_abbrev_tac `compile_op _ op` \\ Cases_on `op`
    \\ simp ([compile_op_def] @ props_defs)
    \\ rpt (CASE_TAC \\ simp props_defs))
  \\ TRY (qmatch_goalsub_abbrev_tac `AllocGlobals _ n` \\ Induct_on `n`
    \\ simp [Once AllocGlobals_def]
    \\ rw props_defs)
  \\ fs [dest_nop_def]
  \\ simp ([CopyByteAw8_def, CopyByteStr_def] @ props_defs)
  \\ simp [arg1_def, arg2_def]
  \\ EVERY_CASE_TAC
  \\ fs props_defs
  \\ imp_res_tac EVERY_IMP_HD
  \\ fs [NULL_LENGTH, EVERY_REVERSE]
  \\ simp [Once closPropsTheory.contains_App_SOME_EXISTS,
        Once closPropsTheory.every_Fn_vs_NONE_EVERY,
        EVERY_MAP, ELIM_UNCURRY]
  \\ rw [EVERY_MEM, FORALL_PROD]
  \\ first_x_assum drule
  \\ rw []
  \\ imp_res_tac EVERY_IMP_HD
  \\ fs [NULL_LENGTH]
QED

Theorem compile_decs_syntactic_props:
  !decs. EVERY closProps$no_mti (compile_decs decs) /\
    closProps$every_Fn_vs_NONE (compile_decs decs) /\
    (0 < max_app ==> ¬closProps$contains_App_SOME max_app (compile_decs decs))
Proof
  Induct
  \\ simp ([compile_decs_def] @ props_defs)
  \\ Cases
  \\ simp ([compile_decs_def, contains_App_SOME_APPEND] @ props_defs)
  \\ rw [] \\ simp [compile_syntactic_props]
QED

Theorem FST_inc_compile_syntactic_props:
  EVERY closProps$no_mti (FST (inc_compile_decs decs)) /\
  closProps$every_Fn_vs_NONE (FST (inc_compile_decs decs)) /\
  (0 < max_app ==> ¬closProps$contains_App_SOME max_app (FST (inc_compile_decs decs)))
Proof
  simp [inc_compile_decs_def, compile_decs_syntactic_props,
    contains_App_SOME_APPEND]
QED

Theorem FST_inc_compile_set_globals:
  ∀decs. no_Mat_decs decs ==>
  closProps$elist_globals (FST (inc_compile_decs decs)) =
  flatProps$elist_globals (MAP flatProps$dest_Dlet (FILTER flatProps$is_Dlet decs))
Proof
  simp [inc_compile_decs_def, closPropsTheory.elist_globals_append]
  \\ simp [compile_decs_set_globals]
QED

Theorem FST_inc_compile_esgc_free:
  EVERY (flatProps$esgc_free o flatProps$dest_Dlet) (FILTER flatProps$is_Dlet decs) /\
  no_Mat_decs decs ==>
  EVERY closProps$esgc_free (FST (inc_compile_decs decs))

Proof
  simp [inc_compile_decs_def]
  \\ simp [compile_decs_esgc_free]
QED

val _ = export_theory()
