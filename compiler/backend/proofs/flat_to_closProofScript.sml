(*
  Correctness proof for flat_to_clos
*)
open preamble
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     flatLangTheory flatSemTheory flatPropsTheory backendPropsTheory
     closLangTheory closSemTheory closPropsTheory

val _ = new_theory"flat_to_closProof"

val _ = set_grammar_ancestry ["misc","ffi","bag","flatProps","closProps",
                              (*"flat_to_clos",*)"backendProps","backend_common"];


Definition dest_pat_def:
  dest_pat [(Pvar v, h)] = SOME (v:string,h) /\
  dest_pat _ = NONE
End

Theorem dest_pat_thm:
  dest_pat pes = SOME (p_1,p_2) <=> pes = [(Pvar p_1, p_2)]
Proof
  Cases_on `pes` \\ fs [dest_pat_def]
  \\ Cases_on `t` \\ fs [dest_pat_def]
  \\ Cases_on `h` \\ fs [dest_pat_def]
  \\ Cases_on `q` \\ fs [dest_pat_def]
QED

Definition compile_lit_def:
  compile_lit t (IntLit i) = closLang$Op t (Const i) [] /\
  compile_lit t (Char c) = closLang$Op t (Const (& (ORD c))) [] /\
  compile_lit t (StrLit s) = closLang$Op t (String s) [] /\
  compile_lit t (Word8 b) = closLang$Op t (Const (& (w2n b))) [] /\
  compile_lit t (Word64 w) =
    closLang$Op t WordFromInt [closLang$Op t (Const (& (w2n w))) []]
End

Definition arg2_def:
  arg2 [x; y] f = f x y /\
  arg2 xs f = closLang$Let None xs (Var None 0)
End

Definition compile_op_def:
  compile_op t op xs =
    case op of
    | Opapp => arg2 xs (\x f. closLang$App t NONE f [x])
    | TagLenEq tag n => closLang$Op t (TagLenEq tag n) xs
    | El n => closLang$Op t El ([Op None (Const (& n)) []] ++ xs)
    | _ => Let None xs (Var None 0)
End

Triviality MEM_IMP_exp_size:
  !funs f v x. MEM (f,v,x) funs ==> exp_size x < flatLang$exp1_size funs
Proof
  Induct \\ fs [] \\ rw [] \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition compile_def:
  (compile m [] = []) /\
  (compile m (x::y::xs) = compile m [x] ++ compile m (y::xs)) /\
  (compile m [flatLang$Raise t e] = [closLang$Raise t (HD (compile m [e]))]) /\
  (compile m [Lit t l] = [compile_lit t l]) /\
  (compile m [Var_local t v] = [Var t (findi (SOME v) m)]) /\
  (compile m [Con t n es] =
     let tag = (case n of SOME (t,_) => t | _ => 0) in
       [Op t (Cons tag) (compile m (REVERSE es))]) /\
  (compile m [App t op es] = [compile_op t op (compile m (REVERSE es))]) /\
  (compile m [Fun t v e] = [Fn t NONE NONE 1 (HD (compile (SOME v::m) [e]))]) /\
  (compile m [If t x1 x2 x3] =
     [If t (HD (compile m [x1]))
           (HD (compile m [x2]))
           (HD (compile m [x3]))]) /\
  (compile m [Let t vo e1 e2] =
     [Let t (compile m [e1]) (HD (compile (vo::m) [e2]))]) /\
  (compile m [Mat t e pes] = [Op t (Const 0) []]) /\
  (compile m [Handle t e pes] =
     case dest_pat pes of
     | SOME (v,h) => [Handle t (HD (compile m [e])) (HD (compile (SOME v::m) [h]))]
     | _ => compile m [e]) /\
  (compile m [Letrec t funs e] =
     let new_m = MAP (\n. SOME (FST n)) funs ++ m in
       [Letrec t NONE NONE
          (MAP ( \ (f,v,x). (1, HD (compile (SOME v :: new_m) [x]))) funs)
          (HD (compile new_m [e]))])
Termination
  WF_REL_TAC `measure (flatLang$exp6_size o SND)` \\ rw []
  \\ imp_res_tac MEM_IMP_exp_size \\ fs [dest_pat_thm]
  \\ fs [flatLangTheory.exp_size_def]
End

Definition compile_decs_def:
  compile_decs [] = [] /\
  compile_decs ((Dlet e)::xs) = compile [] [e] ++ compile_decs xs /\
  compile_decs (_::xs) = compile_decs xs
End

Theorem LENGTH_compile:
  !m xs. LENGTH (compile m xs) = LENGTH xs
Proof
  ho_match_mp_tac compile_ind \\ fs [compile_def]
  \\ rw [] \\ every_case_tac \\ fs []
QED

Theorem HD_compile[simp]:
  [HD (compile m [x])] = compile m [x]
Proof
  qspecl_then [`m`,`[x]`] mp_tac (SIMP_RULE std_ss [] LENGTH_compile)
  \\ Cases_on `compile m [x]` \\ fs []
QED

Definition no_Mat_def[simp]:
  (no_Mat [] <=> T) /\
  (no_Mat (x::y::xs) <=> no_Mat [x] /\ no_Mat (y::xs)) /\
  (no_Mat [flatLang$Raise t e] <=> no_Mat [e]) /\
  (no_Mat [Lit t l] <=> T) /\
  (no_Mat [Var_local t v] <=> T) /\
  (no_Mat [Con t n es] <=> no_Mat (REVERSE es)) /\
  (no_Mat [App t op es] <=> no_Mat (REVERSE es)) /\
  (no_Mat [Fun t v e] <=> no_Mat [e]) /\
  (no_Mat [If t x1 x2 x3] <=> no_Mat [x1] /\ no_Mat [x2] /\ no_Mat [x3]) /\
  (no_Mat [Let t vo e1 e2] <=> no_Mat [e1] /\ no_Mat [e2]) /\
  (no_Mat [Mat t e pes] <=> F) /\
  (no_Mat [Handle t e pes] <=> no_Mat [e] /\ case dest_pat pes of SOME (v,h) => no_Mat [h] | _ => F) /\
  (no_Mat [Letrec t funs e] <=> no_Mat (MAP (SND o SND) funs) /\ no_Mat [e])
Termination
  WF_REL_TAC `measure (flatLang$exp6_size)` \\ rw []
  \\ fs [dest_pat_thm] \\ fs [flatLangTheory.exp_size_def]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac `exp1_size funs` \\ fs []
  \\ Induct_on `funs` \\ fs [flatLangTheory.exp_size_def]
  \\ rw [] \\ fs []
  \\ PairCases_on `h` \\ fs [flatLangTheory.exp_size_def]
End

Definition no_Mat_decs_def[simp]:
  no_Mat_decs [] = T /\
  no_Mat_decs ((Dlet e)::xs) = (no_Mat [e] /\ no_Mat_decs xs) /\
  no_Mat_decs (_::xs) = no_Mat_decs xs
End

Inductive v_rel:
  (!i. v_rel (Litv (IntLit i)) (Number i)) /\
  (!c. v_rel (Litv (Char c)) (Number (& (ORD c)))) /\
  (!s. v_rel (Litv (StrLit s)) (ByteVector (MAP (n2w o ORD) s))) /\
  (!b. v_rel (Litv (Word8 b)) (Number (& (w2n b)))) /\
  (!w. v_rel (Litv (Word64 w)) (Word64 w)) /\
  (!vs ws t r. LIST_REL v_rel vs ws ==> v_rel (Conv (SOME (t,r)) vs) (Block t ws)) /\
  (!env m db.
    (!n x. ALOOKUP env.v n = SOME x ==>
           findi (SOME n) m < LENGTH db /\
           v_rel x (EL (findi (SOME n) m) db)) ==>
     env_rel env (m:string option list) (db:closSem$v list)) /\
  (!env m db n e.
     env_rel env m db /\ no_Mat [e] ==>
     v_rel (Closure env.v n e)
           (Closure NONE [] db 1 (HD (compile (SOME n::m) [e])))) /\
  (!funs n env m db.
    n < LENGTH funs /\ env_rel env m db /\ ALL_DISTINCT (MAP FST funs) /\
    no_Mat (MAP (SND o SND) funs) ==>
     v_rel (Recclosure env.v funs (FST (EL n funs)))
      (Recclosure NONE [] db (MAP
            (λ(f,v,x). (1, HD (compile
                       (SOME v::(MAP (λn. SOME (FST n)) funs ++ m))
                       [x]))) funs) n))
End

Theorem env_rel_def =
  ``env_rel env m db`` |> ONCE_REWRITE_CONV [v_rel_cases] |> GEN_ALL;

Definition state_rel_def:
  state_rel (s:'ffi flatSem$state) (t:('c,'ffi) closSem$state) <=>
    ~s.check_ctor /\
    1 <= t.max_app /\
    s.ffi = t.ffi /\
    s.clock = t.clock
End

Triviality env_rel_CONS:
  env_rel <| v := xs |> m db /\ v_rel v1 v2 ==>
  env_rel <| v := (n,v1) :: xs |> (SOME n :: m) (v2 :: db)
Proof
  fs [env_rel_def,findi_def,GSYM ADD1]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
QED

Triviality env_rel_APPEND:
  !name_prefix prefix db_prefix env m db.
    env_rel env m db /\
    LIST_REL v_rel (MAP SND prefix) db_prefix /\
    name_prefix = MAP (SOME o FST) prefix ==>
    env_rel <| v := prefix ++ env.v |> (name_prefix ++ m) (db_prefix ++ db)
Proof
  Induct \\ fs []
  THEN1 (rw[env_rel_def])
  \\ Cases_on `prefix` \\ fs [PULL_EXISTS] \\ rw []
  \\ PairCases_on `h` \\ fs []
  \\ match_mp_tac env_rel_CONS
  \\ fs []
QED

Theorem state_rel_initial_state:
  0 < max_app ==>
  state_rel (initial_state ffi k T F)
            (initial_state ffi max_app FEMPTY co cc k)
Proof
  fs [state_rel_def,flatSemTheory.initial_state_def,initial_state_def]
QED

Triviality state_rel_IMP_check_ctor:
  state_rel s t ==> ~s.check_ctor
Proof
  fs [state_rel_def]
QED

val goal =
  ``\env (s:'ffi flatSem$state) es.
      !m db res1 s1 (t:('c,'ffi) closSem$state).
        evaluate env s es = (s1,res1) /\ state_rel s t /\ env_rel env m db /\
        no_Mat es /\ res1 <> Rerr (Rabort Rtype_error) ==>
        ?res2 t1.
          evaluate (compile m es, db, t) = (res2,t1) /\ state_rel s1 t1 /\
          result_rel (LIST_REL v_rel) v_rel res1 res2``

val goal_match =
  ``\env (s:'ffi flatSem$state) (v:flatSem$v) pes (xv:flatSem$v).
      !m db res1 s1 (t:('c,'ffi) closSem$state) p e.
        dest_pat pes = SOME (p,e) /\
        evaluate <|v := (p,v)::env.v|> s [e] = (s1,res1) /\ state_rel s t /\
        env_rel <|v := (p,v)::env.v|> m db /\
        no_Mat [e] /\ res1 <> Rerr (Rabort Rtype_error) ==>
        ?res2 t1.
          evaluate (compile m [e], db, t) = (res2,t1) /\ state_rel s1 t1 /\
          result_rel (LIST_REL v_rel) v_rel res1 res2``

local
  val ind_thm = flatSemTheory.evaluate_ind
    |> ISPEC goal |> SPEC goal_match
    |> CONV_RULE (DEPTH_CONV BETA_CONV) |> REWRITE_RULE [];
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

Theorem compile_Handle:
  ^(get_goal "flatLang$Handle")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ Cases_on `dest_pat pes` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ fs [dest_pat_thm] \\ rveq \\ fs []
  \\ fs [flatSemTheory.evaluate_def,evaluate_def,
         EVAL ``ALL_DISTINCT (pat_bindings (Pvar x0) [])``,
         EVAL ``pmatch s' (Pvar x0) v []``]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ fs [error_result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ rename [`v_rel v1 v2`]
  \\ `env_rel <|v := (x0,v1)::env.v|> (SOME x0::m) (v2::db)` by
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
  \\ fs [bool_case_eq]
  \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM) \\ fs []
  \\ qmatch_goalsub_abbrev_tac `GENLIST recc`
  \\ first_x_assum drule
  \\ disch_then match_mp_tac
  \\ fs [build_rec_env_eq_MAP]
  \\ match_mp_tac env_rel_APPEND \\ fs []
  \\ reverse conj_tac
  THEN1
   (qspec_tac (`Recclosure env.v funs`,`rr`)
    \\ qid_spec_tac `funs`
    \\ Induct \\ fs [FORALL_PROD])
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [Abbr`recc`]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ rw [] \\ qexists_tac `env` \\ qexists_tac `m` \\ fs [o_DEF]
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
  ^(get_goal "flatLang$Con") /\
  ^(get_goal "s.check_ctor ∧ _")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ imp_res_tac state_rel_IMP_check_ctor \\ fs []
  \\ PairCases_on `cn`
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ fs [do_app_def]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
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

Theorem EVERY_no_Mat:
  !xs. no_Mat xs ==> EVERY (\x. no_Mat [x]) xs
Proof
  recInduct no_Mat_ind \\ fs [no_Mat_def]
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
  ^(get_goal "flatLang$Mat") /\
  ^(get_goal "dest_pat []") /\
  ^(get_goal "dest_pat ((p,e)::pes)")
Proof
  fs [no_Mat_def,dest_pat_thm] \\ rw []
  \\ fs [EVAL ``pmatch s (Pvar p') v []``]
  \\ fs [EVAL ``ALL_DISTINCT (pat_bindings (Pvar p') [])``]
QED

Theorem compile_op_evaluates_args:
  evaluate (xs,db,t) = (Rerr err,t1) /\ op <> Opapp ==>
  evaluate ([compile_op tra op xs],db,t) = (Rerr err,t1)
Proof
  Cases_on `op` \\ fs [compile_op_def,evaluate_def,evaluate_APPEND]
  \\ simp [Once evaluate_CONS] \\ fs [evaluate_def,do_app_def]
QED

Theorem v_rel_Boolv[simp]:
  v_rel (Boolv b) v = (v = Boolv b)
Proof
  Cases_on `b` \\ fs [Once v_rel_cases,flatSemTheory.Boolv_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Theorem compile_op_correct:
  do_app F s1 op vs = SOME (s2,res2) /\
  state_rel s1 (t1:('c,'ffi) closSem$state) /\
  evaluate (xs,db,t) = (Rval ws,t1) /\
  LIST_REL v_rel vs (REVERSE ws) /\
  LENGTH xs = LENGTH vs /\ op <> Opapp ==>
  ∃res2' t1.
    evaluate ([compile_op tt op xs],db,t) = (res2',t1) ∧
    state_rel s2 t1 ∧
    result_rel (LIST_REL v_rel) v_rel (list_result res2) res2'
Proof
  Cases_on `?n. op = El n` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",PULL_EXISTS]
    \\ rw [] \\ fs [] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [compile_op_def,evaluate_def,evaluate_APPEND,do_app_def,evaluate_def]
    \\ once_rewrite_tac [evaluate_CONS] \\ fs []
    \\ fs [compile_op_def,evaluate_def,evaluate_APPEND,do_app_def,evaluate_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [listTheory.LIST_REL_EL_EQN])
  \\ Cases_on `?tag n. op = TagLenEq tag n` THEN1
   (fs [flatSemTheory.do_app_def,list_case_eq,CaseEq "flatSem$v",
        PULL_EXISTS,option_case_eq,pair_case_eq]
    \\ rw [] \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [compile_op_def,evaluate_def,evaluate_APPEND,do_app_def,evaluate_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ cheat
QED

Theorem compile_App:
  ^(get_goal "flatLang$App")
Proof
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ rfs [pair_case_eq]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac
  \\ Cases_on `op = Opapp` \\ fs []
  THEN1
   (fs [compile_op_def] \\ rveq
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
      \\ `env_rel <|v := (vn,x)::env'.v|> (SOME vn::m1) (vx::db1)` by
            (match_mp_tac env_rel_CONS \\ fs [env_rel_def])
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
    THEN1 (imp_res_tac EVERY_no_Mat \\ fs [EVERY_EL] \\ fs [EL_MAP])
    \\ fs []
    \\ match_mp_tac env_rel_CONS
    \\ fs [build_rec_env_eq_MAP]
    \\ match_mp_tac env_rel_APPEND \\ fs []
    \\ fs [MAP_MAP_o,o_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
    \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [] \\ rw []
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rename [`env_rel env3 m3 db3`]
    \\ qexists_tac `env3` \\ qexists_tac `m3` \\ fs []
    \\ fs [o_DEF])
  \\ reverse (fs [result_case_eq])
  \\ rveq \\ fs [] \\ rveq \\ fs []
  THEN1 (drule compile_op_evaluates_args \\ fs [])
  \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
  \\ rename [`state_rel s1 t1`,`LIST_REL v_rel vs ws`,`_ = SOME (s2,res2)`]
  \\ qmatch_goalsub_rename_tac `compile_op tt op cexps`
  \\ drule EVERY2_REVERSE
  \\ qmatch_goalsub_rename_tac `LIST_REL _ vvs`
  \\ imp_res_tac state_rel_IMP_check_ctor \\ fs [] \\ rw []
  \\ match_mp_tac (GEN_ALL compile_op_correct)
  \\ rpt (asm_exists_tac \\ fs [])
  \\ imp_res_tac evaluate_IMP_LENGTH
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_nil, compile_cons,
       compile_Lit, compile_Handle, compile_Raise, compile_Let,
       compile_Letrec, compile_Fun, compile_Con, compile_App,
       compile_If, compile_Mat, compile_Var_local])
  \\ asm_rewrite_tac []
QED

Theorem compile_decs_correct:
  ∀ds s res1 s1 (t:('c,'ffi) closSem$state).
    evaluate_decs s ds = (s1,res1) ∧ state_rel s t ∧
    no_Mat_decs ds /\ res1 ≠ SOME (Rabort Rtype_error) ⇒
    ∃res2 t1.
      evaluate (compile_decs ds,[],t) = (res2,t1) ∧ state_rel s1 t1 /\
      ?v.
        let res1' = (case res1 of NONE => Rval v | SOME e => Rerr e) in
          result_rel (LIST_REL (\x y. T)) v_rel res1' res2
Proof
  Induct
  THEN1 fs [evaluate_decs_def,compile_decs_def,closSemTheory.evaluate_def]
  \\ reverse Cases \\ rw []
  \\ imp_res_tac state_rel_IMP_check_ctor \\ fs [compile_decs_def]
  \\ TRY (first_x_assum match_mp_tac)
  \\ fs [evaluate_decs_def,compile_decs_def,closSemTheory.evaluate_def,evaluate_dec_def]
  \\ TRY asm_exists_tac \\ fs []
  \\ fs [pair_case_eq,option_case_eq,result_case_eq,bool_case_eq]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ drule (CONJUNCT1 compile_correct)
  \\ fs [evaluate_APPEND]
  \\ `env_rel <|v := []|> [] []` by fs [env_rel_def]
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ disch_then drule
  \\ rw [] \\ fs []
  \\ Cases_on `res1` \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem compile_semantics:
   0 < max_app /\ no_Mat_decs ds ==>
   flatSem$semantics T F (ffi:'ffi ffi_state) ds ≠ Fail ==>
   closSem$semantics ffi max_app FEMPTY co cc (compile_decs ds) =
   flatSem$semantics T F ffi ds
Proof
  strip_tac
  \\ simp[flatSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ simp[]
  \\ conj_tac >- (
    rw[] \\ simp[closSemTheory.semantics_def]
    \\ IF_CASES_TAC \\ fs[]
    THEN1
     (qhdtm_x_assum`flatSem$evaluate_decs`kall_tac
      \\ last_x_assum(qspec_then`k'`mp_tac) \\ simp[]
      \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g)
      \\ spose_not_then strip_assume_tac
      \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``])
      \\ qmatch_asmsub_abbrev_tac `([],init)`
      \\ `state_rel (initial_state ffi k' T F) init` by
           fs [Abbr`init`,state_rel_initial_state]
      \\ disch_then drule
      \\ impl_tac THEN1 fs []
      \\ strip_tac
      \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp[]
    \\ conj_tac >- (
      rw[]
      \\ qmatch_assum_abbrev_tac`flatSem$evaluate_decs ss es = _`
      \\ qmatch_assum_abbrev_tac`closSem$evaluate bp = _`
      \\ fs [option_case_eq,result_case_eq]
      \\ drule evaluate_decs_add_to_clock_io_events_mono_alt
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
      \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``]) \\ rfs []
      \\ disch_then (qspec_then `initial_state ffi max_app FEMPTY co cc k' with
           clock := k + k'` mp_tac)
      \\ impl_tac >-
       (reverse conj_tac THEN1 (CCONTR_TAC \\ fs [])
        \\ fs [flatPropsTheory.initial_state_clock,
               closPropsTheory.initial_state_clock,
               state_rel_initial_state])
      \\ strip_tac \\ unabbrev_all_tac \\ fs[]
      \\ fs[initial_state_def] \\ rfs[]
      \\ rveq \\ fs []
      \\ every_case_tac
      \\ fs[state_component_equality] \\ fs [state_rel_def])
    \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``])
    \\ `state_rel (initial_state ffi k T F)
         (initial_state ffi max_app FEMPTY co cc k)` by
       (match_mp_tac state_rel_initial_state \\ fs []) \\ rfs []
    \\ disch_then drule
    \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs []
    \\ qexists_tac `k` \\ fs []
    \\ every_case_tac
    \\ fs[state_component_equality] \\ fs [state_rel_def])
  \\ strip_tac
  \\ simp[closSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs [] >- (
    last_x_assum(qspec_then`k`strip_assume_tac)
    \\ qmatch_assum_abbrev_tac`SND p ≠ _`
    \\ Cases_on`p` \\ fs[markerTheory.Abbrev_def]
    \\ pop_assum(assume_tac o SYM)
    \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``])
    \\ `state_rel (initial_state ffi k T F)
         (initial_state ffi max_app FEMPTY co cc k)` by
       (match_mp_tac state_rel_initial_state \\ fs [])
    \\ disch_then drule
    \\ impl_tac THEN1 (fs [] \\ CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs []
    \\ rveq \\ fs [] \\ every_case_tac \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ simp[]
  \\ conj_tac >- (
    spose_not_then strip_assume_tac
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``])
    \\ `state_rel (initial_state ffi k T F)
         (initial_state ffi max_app FEMPTY co cc k)` by
       (match_mp_tac state_rel_initial_state \\ fs [])
    \\ disch_then drule
    \\ impl_tac THEN1 (fs [] \\ CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ qpat_x_assum `!k s. _` (qspecl_then [`k`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM] \\ gen_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ qpat_abbrev_tac`s0 = closSem$initial_state _ _ _ _ _`
  \\ Cases_on `evaluate_decs (initial_state ffi k T F) ds`
  \\ drule (compile_decs_correct |> INST_TYPE [``:'c``|->``:'a``])
  \\ `state_rel (initial_state ffi k T F)
       (initial_state ffi max_app FEMPTY co cc k)` by
     (match_mp_tac state_rel_initial_state \\ fs [])
  \\ disch_then drule
  \\ impl_tac THEN1 (fs [] \\ last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ fs [] \\ strip_tac \\ fs [state_rel_def]
QED

val _ = export_theory()
