(*
  Correctness proof for flat_ticks, the removal of Tick in flatLang.
  The simulation goes from the tick-free program to the original one,
  which needs more clock to perform its ticks.
*)
Theory flat_ticksProof
Ancestors
  misc flatLang flat_ticks flatSem flatProps backendProps
  semanticPrimitivesProps
Libs
  preamble

(* relations, the tick-free side is on the left *)

Inductive v_rel:
  (∀v1 v2.
     simple_basic_val_rel v1 v2 ∧
     LIST_REL v_rel (v_container_xs v1) (v_container_xs v2) ⇒
     v_rel v1 v2) ∧
  (∀env1 env2 n e.
     env_rel env1 env2 ⇒
     v_rel (Closure env1 n (remove_ticks_exp e)) (Closure env2 n e)) ∧
  (∀env1 env2 fs n.
     env_rel env1 env2 ⇒
     v_rel (Recclosure env1 (remove_ticks_funs fs) n) (Recclosure env2 fs n)) ∧
  (∀env1 env2.
     LIST_REL (λ(n1,v1) (n2,v2). n1 = n2 ∧ v_rel v1 v2) env1.v env2.v ⇒
     env_rel env1 env2)
End

Theorem v_rel_l_cases = TypeBase.nchotomy_of “: v”
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (curry mk_comb “v_rel”)
  |> map (fn t => mk_comb (t, “v2 : v”))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

Theorem env_rel_def = “env_rel env1 env2” |> SIMP_CONV bool_ss [Once v_rel_cases]

Definition install_conf_rel_def:
  install_conf_rel ic1 ic2 ⇔
    (ic2.compile_oracle = pure_co remove_ticks_decs o ic1.compile_oracle) ∧
    (ic1.compile = pure_cc remove_ticks_decs ic2.compile)
End

Definition state_rel_def:
  state_rel (t:('c,'ffi) flatSem$state) (s:('c,'ffi) flatSem$state) ⇔
    t.clock = s.clock ∧
    LIST_REL (sv_rel v_rel) t.refs s.refs ∧
    t.ffi = s.ffi ∧
    LIST_REL (OPTREL v_rel) t.globals s.globals ∧
    install_conf_rel s.eval_config t.eval_config
End

Theorem simple_val_rel:
  simple_val_rel v_rel
Proof
  simp [simple_val_rel_def] \\ rw []
  \\ Cases_on ‘v1’ \\ gvs [isClosure_def, v_rel_l_cases]
  \\ Cases_on ‘v2’ \\ gvs [isClosure_def]
QED

Theorem simple_state_rel:
  simple_state_rel v_rel state_rel
Proof
  simp [simple_state_rel_def, state_rel_def]
QED

Theorem do_app_thm = MATCH_MP simple_do_app_thm (CONJ simple_val_rel simple_state_rel)

Theorem state_rel_dec_clock:
  state_rel t s ⇒ state_rel (dec_clock t) (dec_clock s)
Proof
  simp [state_rel_def, dec_clock_def]
QED

Theorem env_rel_ALOOKUP:
  ∀xs ys n.
    LIST_REL (λ(n1,v1) (n2,v2). n1 = n2 ∧ v_rel v1 v2) xs ys ⇒
    OPTREL v_rel (ALOOKUP xs n) (ALOOKUP ys n)
Proof
  Induct \\ rw [] \\ PairCases_on ‘h’ \\ Cases_on ‘y’ \\ gvs [] \\ rw []
QED

(* decomposing source expressions into ticks and the rest *)

Definition mk_Ticks_def:
  mk_Ticks [] e = e ∧
  mk_Ticks (t::ts) e = Tick t (mk_Ticks ts e)
End

Theorem remove_ticks_exp_cases:
  ∀x. ∃ts y. x = mk_Ticks ts y ∧ (∀t e. y ≠ Tick t e) ∧
             remove_ticks_exp x = remove_ticks_exp y
Proof
  measureInduct_on ‘exp_size x’ \\ Cases_on ‘x’
  \\ TRY (qexists_tac ‘[]’ \\ simp [mk_Ticks_def] \\ NO_TAC)
  \\ rename1 ‘Tick t e’
  \\ first_x_assum (qspec_then ‘e’ mp_tac) \\ simp [exp_size_def]
  \\ strip_tac \\ gvs []
  \\ qexistsl_tac [‘t::ts’, ‘y’] \\ simp [mk_Ticks_def, remove_ticks_exp_def]
QED

Theorem evaluate_mk_Ticks:
  ∀ts env s e.
    evaluate env s [mk_Ticks ts e] =
      case evaluate env s [e] of
      | (s1, Rval vs) =>
          if s1.clock < LENGTH ts
          then (s1 with clock := 0, Rerr (Rabort Rtimeout_error))
          else (s1 with clock := s1.clock - LENGTH ts, Rval vs)
      | res => res
Proof
  Induct \\ simp [mk_Ticks_def]
  >- (rpt strip_tac \\ Cases_on ‘evaluate env s [e]’ \\ Cases_on ‘r’ \\ gvs [])
  \\ rpt strip_tac \\ simp [evaluate_def]
  \\ Cases_on ‘evaluate env s [e]’ \\ Cases_on ‘r’ \\ gvs []
  \\ rw [dec_clock_def] \\ gvs [state_component_equality]
QED

Theorem mk_Ticks_suff:
  (∃ck s2 r1. evaluate env (s with clock := s.clock + ck) [y] = (s2,r1) ∧
              result_rel (LIST_REL v_rel) v_rel r2 r1 ∧ state_rel t2 s2) ⇒
  (∃ck s2 r1. evaluate env (s with clock := s.clock + ck) [mk_Ticks ts y] =
              (s2,r1) ∧ result_rel (LIST_REL v_rel) v_rel r2 r1 ∧
              state_rel t2 s2)
Proof
  rw [evaluate_mk_Ticks]
  \\ reverse (Cases_on ‘r1’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [])
  \\ drule (CONJUNCT1 evaluate_add_to_clock) \\ simp []
  \\ disch_then (qspec_then ‘LENGTH ts’ assume_tac)
  \\ qexists_tac ‘ck + LENGTH ts’ \\ gvs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ simp [state_component_equality]
QED

(* pattern matching *)

Theorem state_rel_store_lookup:
  state_rel t s ⇒
  OPTREL (sv_rel v_rel) (store_lookup n t.refs) (store_lookup n s.refs)
Proof
  rw [state_rel_def, semanticPrimitivesTheory.store_lookup_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs [LIST_REL_EL_EQN]
QED

Overload nv_rel = “LIST_REL (λ(n1:varN,v1) (n2,v2). n1 = n2 ∧ v_rel v1 v2)”

Definition match_rel_def:
  match_rel r1 r2 ⇔
    case (r1, r2) of
    | (Match env1, Match env2) => nv_rel env1 env2
    | (No_match, No_match) => T
    | (Match_type_error, Match_type_error) => T
    | _ => F
End

Theorem pmatch_thm:
  (∀(t:('c,'ffi) flatSem$state) p v1 bs1 s v2 bs2.
     state_rel t s ∧ v_rel v1 v2 ∧ nv_rel bs1 bs2 ⇒
     match_rel (pmatch t p v1 bs1) (pmatch s p v2 bs2)) ∧
  (∀(t:('c,'ffi) flatSem$state) ps vs1 bs1 s vs2 bs2.
     state_rel t s ∧ LIST_REL v_rel vs1 vs2 ∧ nv_rel bs1 bs2 ⇒
     match_rel (pmatch_list t ps vs1 bs1) (pmatch_list s ps vs2 bs2))
Proof
  ho_match_mp_tac pmatch_ind
  \\ rw [pmatch_def, match_rel_def] \\ gvs [v_rel_l_cases, pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ rw [] \\ gvs []
  >~ [‘store_lookup’] >- (
    drule_then (qspec_then ‘lnum’ mp_tac) state_rel_store_lookup
    \\ Cases_on ‘store_lookup lnum t.refs’
    \\ Cases_on ‘store_lookup lnum s.refs’ \\ simp []
    \\ rename1 ‘sv_rel _ x1 x2’ \\ Cases_on ‘x1’ \\ Cases_on ‘x2’
    \\ simp [sv_rel_def]
    \\ strip_tac \\ first_x_assum drule_all \\ simp [])
  \\ first_x_assum (qspecl_then [‘s’,‘y’,‘bs2’] mp_tac) \\ simp []
  \\ Cases_on ‘pmatch t p v1 bs1’ \\ Cases_on ‘pmatch s p y bs2’ \\ simp []
  \\ rpt strip_tac \\ gvs []
  \\ first_x_assum drule_all \\ simp []
  \\ every_case_tac \\ gvs []
QED

Theorem pmatch_rows_thm:
  ∀pes (t:('c,'ffi) flatSem$state) s v1 v2.
    state_rel t s ∧ v_rel v1 v2 ⇒
    case pmatch_rows (remove_ticks_pes pes) t v1 of
    | Match (env1, p, e1) =>
        ∃env2 e2. pmatch_rows pes s v2 = Match (env2, p, e2) ∧
                  nv_rel env1 env2 ∧ e1 = remove_ticks_exp e2
    | No_match => pmatch_rows pes s v2 = No_match
    | Match_type_error => pmatch_rows pes s v2 = Match_type_error
Proof
  Induct \\ TRY PairCases \\ rw [remove_ticks_exp_def, pmatch_rows_def]
  \\ ‘match_rel (pmatch t h0 v1 []) (pmatch s h0 v2 [])’
    by (irule (CONJUNCT1 pmatch_thm) \\ simp [])
  \\ first_x_assum drule_all
  \\ Cases_on ‘pmatch t h0 v1 []’ \\ Cases_on ‘pmatch s h0 v2 []’
  \\ gvs [match_rel_def]
  \\ every_case_tac \\ gvs []
QED

(* function application *)

Theorem find_recfun_remove_ticks_funs:
  ∀fs. find_recfun n (remove_ticks_funs fs) =
       OPTION_MAP (λ(x,e). (x, remove_ticks_exp e)) (find_recfun n fs)
Proof
  Induct \\ TRY PairCases
  \\ ONCE_REWRITE_TAC [semanticPrimitivesTheory.find_recfun_def]
  \\ rw [remove_ticks_exp_def]
QED

Theorem MAP_FST_remove_ticks_funs:
  ∀fs. MAP FST (remove_ticks_funs fs) = MAP FST fs
Proof
  Induct \\ TRY PairCases \\ rw [remove_ticks_exp_def]
QED

Theorem build_rec_env_rel:
  env_rel env1 env2 ∧ nv_rel xs ys ⇒
  nv_rel (build_rec_env (remove_ticks_funs fs) env1 xs)
         (build_rec_env fs env2 ys)
Proof
  rw [build_rec_env_eq_MAP]
  \\ irule EVERY2_APPEND_suff \\ simp []
  \\ simp [remove_ticks_exps_MAP, MAP_MAP_o, o_DEF, LIST_REL_MAP1,
           LIST_REL_MAP2, UNCURRY]
  \\ irule EVERY2_refl \\ rw []
  \\ ‘MAP (λ(f,x,e). (f,x,remove_ticks_exp e)) fs = remove_ticks_funs fs’
    by simp [remove_ticks_exps_MAP]
  \\ pop_assum SUBST1_TAC
  \\ irule (el 3 (CONJUNCTS v_rel_rules)) \\ simp []
QED

Theorem do_opapp_thm:
  do_opapp vs1 = SOME (env1, e1) ∧ LIST_REL v_rel vs1 vs2 ⇒
  ∃env2 e2. do_opapp vs2 = SOME (env2, e2) ∧ env_rel env1 env2 ∧
            e1 = remove_ticks_exp e2
Proof
  rw [do_opapp_def, AllCaseEqs()] \\ gvs [v_rel_l_cases]
  \\ gvs [find_recfun_remove_ticks_funs, MAP_FST_remove_ticks_funs]
  \\ gvs [env_rel_def]
  \\ PairCases_on ‘z’ \\ gvs []
  \\ irule build_rec_env_rel \\ gvs [env_rel_def]
QED

Theorem env_rel_opt_bind:
  env_rel env1 env2 ∧ v_rel v1 v2 ⇒
  env_rel (env1 with v updated_by opt_bind n v1)
          (env2 with v updated_by opt_bind n v2)
Proof
  Cases_on ‘n’ \\ rw [env_rel_def, miscTheory.opt_bind_def]
QED

Theorem v_rel_Unitv:
  v_rel x y ⇒ (x = Unitv ⇔ y = Unitv)
Proof
  Cases_on ‘x’ \\ rw [v_rel_l_cases, Unitv_def] \\ gvs []
  \\ Cases_on ‘l’ \\ Cases_on ‘vs2’ \\ gvs []
QED

Theorem do_if_thm:
  ∀v1 v2 e2 e3.
  v_rel v1 v2 ⇒
  do_if v1 (remove_ticks_exp e2) (remove_ticks_exp e3) =
  OPTION_MAP remove_ticks_exp (do_if v2 e2 e3)
Proof
  Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ rw [do_if_def, Boolv_def, v_rel_l_cases]
  \\ gvs [] \\ rw [] \\ gvs []
QED

(* Eval *)

Theorem remove_ticks_decs_NIL[simp]:
  remove_ticks_decs ds = [] ⇔ ds = []
Proof
  Cases_on ‘ds’ \\ simp [remove_ticks_decs_def, remove_ticks_exp_def]
QED

Theorem do_eval_thm:
  do_eval vs1 t.eval_config = SOME (decs1, ec1, rv1) ∧
  state_rel t s ∧ LIST_REL v_rel vs1 vs2 ⇒
  ∃decs2 ec2 rv2.
    do_eval vs2 s.eval_config = SOME (decs2, ec2, rv2) ∧
    decs1 = remove_ticks_decs decs2 ∧ v_rel rv1 rv2 ∧
    state_rel (t with eval_config := ec1) (s with eval_config := ec2)
Proof
  rw [state_rel_def]
  \\ fs [do_eval_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ drule_then drule (MATCH_MP simple_val_rel_v_to_mlstring simple_val_rel)
  \\ drule_then drule (MATCH_MP simple_val_rel_v_to_words simple_val_rel)
  \\ rw []
  \\ gvs [install_conf_rel_def, pure_co_def, pure_cc_def, AllCaseEqs()]
  \\ simp [shift_seq_def, FUN_EQ_THM, Unitv_def, v_rel_l_cases]
QED

(* converse directions, needed to transfer type errors *)

Theorem v_rel_r_cases = TypeBase.nchotomy_of “: v”
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (fn t => mk_comb (mk_comb (“v_rel”, “v1 : v”), t))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

Theorem LIST_REL_flip[local]:
  ∀xs ys. LIST_REL (λx y. R y x) xs ys ⇔ LIST_REL R ys xs
Proof
  Induct \\ Cases_on ‘ys’ \\ simp []
QED

Theorem OPTREL_flip[local]:
  OPTREL (λx y. R y x) = (λa b. OPTREL R b a)
Proof
  rw [FUN_EQ_THM] \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ simp []
QED

Theorem simple_val_rel_flip:
  simple_val_rel (λx y. v_rel y x)
Proof
  simp [simple_val_rel_def] \\ rw []
  \\ Cases_on ‘x’ \\ Cases_on ‘y’
  \\ gvs [isClosure_def, v_rel_r_cases, LIST_REL_flip] \\ metis_tac []
QED

Theorem sv_rel_flip:
  sv_rel (λx y. R y x) = (λa b. sv_rel R b a)
Proof
  rw [FUN_EQ_THM] \\ Cases_on ‘a’ \\ Cases_on ‘b’
  \\ simp [sv_rel_def, LIST_REL_flip] \\ metis_tac []
QED

Theorem flip_v_rel_simps[local] = LIST_CONJ [
  Q.ISPEC ‘v_rel’ (Q.GEN ‘R’ sv_rel_flip) |> BETA_RULE,
  Q.ISPEC ‘v_rel’ (Q.GEN ‘R’ OPTREL_flip) |> BETA_RULE,
  Q.ISPEC ‘v_rel’ (Q.GEN ‘R’ LIST_REL_flip) |> BETA_RULE,
  Q.ISPEC ‘sv_rel v_rel’ (Q.GEN ‘R’ LIST_REL_flip) |> BETA_RULE,
  Q.ISPEC ‘OPTREL v_rel’ (Q.GEN ‘R’ LIST_REL_flip) |> BETA_RULE]

Theorem simple_state_rel_flip:
  simple_state_rel (λx y. v_rel y x) (λs t. state_rel t s)
Proof
  simp [simple_state_rel_def, state_rel_def, flip_v_rel_simps]
  \\ rw [] \\ gvs [flip_v_rel_simps]
QED

Theorem do_app_flip_thm =
  MATCH_MP simple_do_app_thm (CONJ simple_val_rel_flip simple_state_rel_flip)
  |> SIMP_RULE std_ss []

Theorem do_opapp_NONE:
  LIST_REL v_rel vs1 vs2 ∧ do_opapp vs1 = NONE ⇒ do_opapp vs2 = NONE
Proof
  CCONTR_TAC \\ Cases_on ‘do_opapp vs2’ \\ gvs []
  \\ rename1 ‘do_opapp vs2 = SOME x’ \\ PairCases_on ‘x’
  \\ gvs [do_opapp_def, AllCaseEqs(), v_rel_r_cases]
  \\ gvs [find_recfun_remove_ticks_funs, MAP_FST_remove_ticks_funs]
QED

Theorem do_eval_NONE:
  state_rel t s ∧ LIST_REL v_rel vs1 vs2 ∧
  do_eval vs1 t.eval_config = NONE ⇒ do_eval vs2 s.eval_config = NONE
Proof
  CCONTR_TAC \\ Cases_on ‘do_eval vs2 s.eval_config’ \\ gvs []
  \\ rename1 ‘do_eval vs2 s.eval_config = SOME x’ \\ PairCases_on ‘x’
  \\ gvs [state_rel_def, do_eval_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac (MATCH_MP simple_val_rel_v_to_mlstring simple_val_rel_flip
                   |> BETA_RULE)
  \\ imp_res_tac (MATCH_MP simple_val_rel_v_to_words simple_val_rel_flip
                   |> BETA_RULE)
  \\ res_tac \\ gvs []
  \\ gvs [install_conf_rel_def, pure_co_def, pure_cc_def, shift_seq_def,
          AllCaseEqs()]
QED

Theorem dest_thunk_thm:
  ∀t s vs1 vs2.
  state_rel t s ∧ LIST_REL v_rel vs1 vs2 ⇒
  case dest_thunk vs1 t.refs of
  | BadRef => dest_thunk vs2 s.refs = BadRef
  | NotThunk => dest_thunk vs2 s.refs = NotThunk
  | IsThunk m v => ∃w. dest_thunk vs2 s.refs = IsThunk m w ∧ v_rel v w
Proof
  rw []
  \\ Cases_on ‘vs1’ \\ gvs [dest_thunk_def]
  \\ Cases_on ‘t'’ \\ gvs [dest_thunk_def]
  \\ Cases_on ‘h’ \\ gvs [dest_thunk_def, v_rel_l_cases]
  \\ drule_then (qspec_then ‘n’ assume_tac) state_rel_store_lookup
  \\ Cases_on ‘store_lookup n t.refs’ \\ Cases_on ‘store_lookup n s.refs’
  \\ gvs []
  \\ rename1 ‘sv_rel _ x1 x2’ \\ Cases_on ‘x1’ \\ Cases_on ‘x2’
  \\ gvs [sv_rel_cases]
  \\ rename1 ‘Thunk m’ \\ Cases_on ‘m’ \\ rw []
QED

Theorem update_thunk_thm:
  ∀t s vs1 vs2 ws1 ws2.
  state_rel t s ∧ LIST_REL v_rel vs1 vs2 ∧ LIST_REL v_rel ws1 ws2 ⇒
  case update_thunk vs1 t.refs ws1 of
  | NONE => update_thunk vs2 s.refs ws2 = NONE
  | SOME r1 => ∃r2. update_thunk vs2 s.refs ws2 = SOME r2 ∧
                    state_rel (t with refs := r1) (s with refs := r2)
Proof
  rw [] \\ Cases_on ‘update_thunk vs1 t.refs ws1’ \\ simp []
  >- (
    CCONTR_TAC \\ Cases_on ‘update_thunk vs2 s.refs ws2’ \\ gvs []
    \\ gvs [oneline update_thunk_def, AllCaseEqs(), v_rel_r_cases]
    \\ rename1 ‘v_rel w1 w2’
    \\ ‘LIST_REL v_rel [w1] [w2]’ by simp []
    \\ drule_all dest_thunk_thm \\ simp []
    \\ ‘sv_rel (λx y. v_rel y x) (Thunk Evaluated w2) (Thunk Evaluated w1)’
      by simp [sv_rel_cases]
    \\ drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                 simple_state_rel_store_assign) simple_state_rel_flip
               |> BETA_RULE)
    \\ disch_then drule \\ disch_then drule \\ simp [])
  \\ gvs [oneline update_thunk_def, AllCaseEqs(), v_rel_l_cases]
  \\ rename1 ‘v_rel w1 w2’
  \\ ‘LIST_REL v_rel [w1] [w2]’ by simp []
  \\ drule_all dest_thunk_thm \\ simp [] \\ strip_tac
  \\ ‘sv_rel v_rel (Thunk Evaluated w1) (Thunk Evaluated w2)’
    by simp [sv_rel_cases]
  \\ drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
               simple_state_rel_store_assign) simple_state_rel)
  \\ disch_then drule \\ disch_then drule \\ simp []
QED

(* main simulation, from the tick-free code to the original code *)

Theorem evaluate_dec_more_clock:
  evaluate_dec (s with clock := ck + s.clock) d = (s2, r) ∧
  r ≠ SOME (Rabort Rtimeout_error) ⇒
  evaluate_dec (s with clock := ck + ck' + s.clock) d =
    (s2 with clock := ck' + s2.clock, r)
Proof
  rw [] \\ drule (CONJUNCT1 (CONJUNCT2 evaluate_add_to_clock)) \\ simp []
  \\ disch_then (qspec_then ‘ck'’ mp_tac) \\ simp []
QED

Theorem evaluate_more_clock:
  evaluate env (s with clock := ck + s.clock) xs = (s2, r) ∧
  r ≠ Rerr (Rabort Rtimeout_error) ⇒
  evaluate env (s with clock := ck + ck' + s.clock) xs =
    (s2 with clock := ck' + s2.clock, r)
Proof
  rw [] \\ drule (CONJUNCT1 evaluate_add_to_clock) \\ simp []
  \\ disch_then (qspec_then ‘ck'’ mp_tac) \\ simp []
QED

val sing_tac =
  gvs [MAP_EQ_CONS]
  \\ rename1 ‘remove_ticks_exp x0’
  \\ qspec_then ‘x0’ strip_assume_tac remove_ticks_exp_cases \\ gvs []
  \\ FIRST (map irule [mk_Ticks_suff, ONCE_REWRITE_RULE [ADD_COMM] mk_Ticks_suff])
  \\ Cases_on ‘y’ \\ gvs [remove_ticks_exp_def, remove_ticks_exps_MAP];

Theorem evaluate_remove_ticks:
  (∀env1 (t1:('c,'ffi) flatSem$state) ys t2 r2.
     evaluate env1 t1 ys = (t2, r2) ⇒
     ∀env2 s1 xs.
       ys = MAP remove_ticks_exp xs ∧ env_rel env1 env2 ∧ state_rel t1 s1 ⇒
       ∃ck s2 r1.
         evaluate env2 (s1 with clock := s1.clock + ck) xs = (s2, r1) ∧
         result_rel (LIST_REL v_rel) v_rel r2 r1 ∧ state_rel t2 s2) ∧
  (∀(t1:('c,'ffi) flatSem$state) d t2 r2.
     evaluate_dec t1 d = (t2, r2) ⇒
     ∀s1 x.
       d = remove_ticks_exp x ∧ state_rel t1 s1 ⇒
       ∃ck s2 r1.
         evaluate_dec (s1 with clock := s1.clock + ck) x = (s2, r1) ∧
         OPTREL (exc_rel v_rel) r2 r1 ∧ state_rel t2 s2) ∧
  (∀(t1:('c,'ffi) flatSem$state) ds t2 r2.
     evaluate_decs t1 ds = (t2, r2) ⇒
     ∀s1 xs.
       ds = MAP remove_ticks_exp xs ∧ state_rel t1 s1 ⇒
       ∃ck s2 r1.
         evaluate_decs (s1 with clock := s1.clock + ck) xs = (s2, r1) ∧
         OPTREL (exc_rel v_rel) r2 r1 ∧ state_rel t2 s2)
Proof
  ho_match_mp_tac evaluate_ind \\ rpt strip_tac
  \\ TRY (qpat_x_assum ‘_ = MAP remove_ticks_exp _’ (assume_tac o GSYM))
  >~ [‘evaluate _ _ [] = _’] >- (
    gvs [evaluate_def] \\ qexists_tac ‘0’ \\ simp [state_component_equality])
  >~ [‘evaluate _ _ (_::_::_) = _’] >- suspend "cons"
  >~ [‘evaluate _ _ [Lit _ _] = _’] >- (
    sing_tac
    \\ gvs [evaluate_def] \\ qexists_tac ‘0’
    \\ simp [state_component_equality, v_rel_l_cases])
  >~ [‘evaluate _ _ [Raise _ _] = _’] >- suspend "Raise"
  >~ [‘evaluate _ _ [Handle _ _ _] = _’] >- suspend "Handle"
  >~ [‘evaluate _ _ [Con _ NONE _] = _’] >- suspend "Con_NONE"
  >~ [‘evaluate _ _ [Con _ (SOME _) _] = _’] >- suspend "Con_SOME"
  >~ [‘evaluate _ _ [Var_local _ _] = _’] >- suspend "Var_local"
  >~ [‘evaluate _ _ [Fun _ _ _] = _’] >- suspend "Fun"
  >~ [‘evaluate _ _ [App _ _ _] = _’] >- suspend "App"
  >~ [‘evaluate _ _ [If _ _ _ _] = _’] >- suspend "If"
  >~ [‘evaluate _ _ [Mat _ _ _] = _’] >- suspend "Mat"
  >~ [‘evaluate _ _ [Let _ _ _ _] = _’] >- suspend "Let"
  >~ [‘evaluate _ _ [Letrec _ _ _] = _’] >- suspend "Letrec"
  >~ [‘evaluate _ _ [Tick _ _] = _’] >- (
    gvs [MAP_EQ_CONS]
    \\ rename1 ‘remove_ticks_exp x0’
    \\ qspec_then ‘x0’ strip_assume_tac remove_ticks_exp_cases \\ gvs []
    \\ Cases_on ‘y’ \\ gvs [remove_ticks_exp_def])
  >~ [‘evaluate_dec _ _ = _’] >- suspend "dec"
  >~ [‘evaluate_decs _ [] = _’] >- (
    gvs [evaluate_def] \\ qexists_tac ‘0’ \\ simp [state_component_equality])
  \\ suspend "decs_cons"
QED

Resume evaluate_remove_ticks[cons]:
  gvs [MAP_EQ_CONS]
  \\ qpat_x_assum ‘evaluate _ _ (_::_::_) = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 [remove_ticks_exp x0]’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘[x0]’] mp_tac) \\ simp []
  \\ strip_tac
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (strip_tac \\ gvs [] \\ qexists_tac ‘ck’ \\ simp [Once evaluate_def])
  \\ Cases_on ‘evaluate env1 t1' (remove_ticks_exp x0'::MAP remove_ticks_exp t0')’
  \\ rename1 ‘_ = (t2', q2)’
  \\ first_x_assum (qspecl_then [‘t2'’, ‘q2’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s2’, ‘x0'::t0'’] mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘q2’ \\ gvs []
  \\ imp_res_tac evaluate_sing \\ gvs []
QED

Resume evaluate_remove_ticks[Raise]:
  sing_tac
  \\ gvs [evaluate_def, AllCaseEqs()]
  \\ first_x_assum (qspecl_then [‘env2’, ‘s1’, ‘[e']’] mp_tac)
  \\ simp [] \\ strip_tac
  \\ qexists_tac ‘ck’ \\ gvs []
  \\ imp_res_tac evaluate_sing \\ gvs []
QED

Resume evaluate_remove_ticks[Handle]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Handle _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 [remove_ticks_exp e']’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘[e']’] mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ Cases_on ‘q1’ \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ reverse (Cases_on ‘e’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ rename1 ‘v_rel v1 v2’
  \\ qspecl_then [‘l’,‘t1'’,‘s2’,‘v1’,‘v2’] mp_tac
       (REWRITE_RULE [remove_ticks_exps_MAP] pmatch_rows_thm)
  \\ simp []
  \\ Cases_on ‘pmatch_rows (MAP (λ(p,e). (p,remove_ticks_exp e)) l) t1' v1’
  \\ gvs []
  >- (strip_tac \\ qexists_tac ‘ck’ \\ simp [evaluate_def])
  >- (strip_tac \\ qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ PairCases_on ‘a’ \\ gvs [] \\ strip_tac \\ gvs []
  \\ reverse (Cases_on ‘ALL_DISTINCT (pat_bindings a1)’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ first_x_assum (qspecl_then [‘<|v := env2' ++ env2.v|>’, ‘s2’, ‘[e2]’] mp_tac)
  \\ impl_tac
  >- (gvs [env_rel_def] \\ irule EVERY2_APPEND_suff \\ simp [])
  \\ strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [evaluate_def]
QED

Resume evaluate_remove_ticks[Con_NONE]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Con _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 (REVERSE (MAP remove_ticks_exp l))’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘REVERSE l’] mp_tac)
  \\ simp [MAP_REVERSE]
  \\ rpt strip_tac \\ qexists_tac ‘ck’ \\ Cases_on ‘q1’ \\ gvs [evaluate_def]
  \\ simp [Once v_rel_cases, EVERY2_REVERSE]
QED

Resume evaluate_remove_ticks[Con_SOME]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Con _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 (REVERSE (MAP remove_ticks_exp l))’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘REVERSE l’] mp_tac)
  \\ simp [MAP_REVERSE]
  \\ rpt strip_tac \\ qexists_tac ‘ck’ \\ Cases_on ‘q1’ \\ gvs [evaluate_def]
  \\ simp [Once v_rel_cases, EVERY2_REVERSE]
QED

Resume evaluate_remove_ticks[Var_local]:
  sing_tac
  \\ gvs [evaluate_def] \\ qexists_tac ‘0’
  \\ ‘OPTREL v_rel (ALOOKUP env1.v m) (ALOOKUP env2.v m)’
    by (irule env_rel_ALOOKUP \\ fs [env_rel_def])
  \\ Cases_on ‘ALOOKUP env1.v m’ \\ Cases_on ‘ALOOKUP env2.v m’ \\ gvs []
QED

Resume evaluate_remove_ticks[Fun]:
  sing_tac
  \\ gvs [evaluate_def] \\ qexists_tac ‘0’
  \\ simp [state_component_equality]
  \\ irule (el 2 (CONJUNCTS v_rel_rules)) \\ simp []
QED

Resume evaluate_remove_ticks[App]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [App _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 (REVERSE (MAP remove_ticks_exp l))’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘REVERSE l’] mp_tac)
  \\ simp [MAP_REVERSE]
  \\ rpt strip_tac
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ rename1 ‘LIST_REL v_rel vs1 vs2’
  \\ Cases_on ‘o' = Src Opapp’ \\ gvs []
  >- (
    (* function application *)
    Cases_on ‘do_opapp (REVERSE vs1)’ \\ gvs []
    >- (‘do_opapp (REVERSE vs2) = NONE’
          by metis_tac [do_opapp_NONE, EVERY2_REVERSE]
        \\ qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ rename1 ‘do_opapp _ = SOME x’ \\ PairCases_on ‘x’
    \\ ‘∃env2' e2. do_opapp (REVERSE vs2) = SOME (env2', e2) ∧
                   env_rel x0 env2' ∧ x1 = remove_ticks_exp e2’
      by metis_tac [do_opapp_thm, EVERY2_REVERSE]
    \\ gvs []
    \\ ‘t1'.clock = s2.clock’ by fs [state_rel_def]
    \\ Cases_on ‘s2.clock = 0’ \\ gvs []
    >- (qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ first_x_assum (qspecl_then [‘env2'’, ‘dec_clock s2’, ‘[e2]’] mp_tac)
    \\ impl_tac >- simp [state_rel_dec_clock]
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
         (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                               evaluate_more_clock))
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def]
    \\ gvs [dec_clock_def]
    \\ ‘ck' + s2.clock - 1 = ck' + (s2.clock - 1)’ by decide_tac
    \\ simp [])
  \\ Cases_on ‘o' = Src Eval’ \\ gvs []
  >- (
    (* Eval *)
    Cases_on ‘do_eval (REVERSE vs1) t1'.eval_config’ \\ gvs []
    >- (‘do_eval (REVERSE vs2) s2.eval_config = NONE’
          by metis_tac [do_eval_NONE, EVERY2_REVERSE]
        \\ qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ rename1 ‘do_eval _ _ = SOME x’ \\ PairCases_on ‘x’
    \\ ‘∃decs2 ec2 rv2.
          do_eval (REVERSE vs2) s2.eval_config = SOME (decs2, ec2, rv2) ∧
          x0 = remove_ticks_decs decs2 ∧ v_rel x2 rv2 ∧
          state_rel (t1' with eval_config := x1) (s2 with eval_config := ec2)’
      by metis_tac [do_eval_thm, EVERY2_REVERSE]
    \\ gvs []
    \\ ‘t1'.clock = s2.clock’ by fs [state_rel_def]
    \\ Cases_on ‘s2.clock = 0’ \\ gvs []
    >- (qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ Cases_on ‘evaluate_decs (dec_clock (t1' with eval_config := x1))
                   (remove_ticks_decs decs2)’
    \\ rename1 ‘_ = (t3, q3)’
    \\ first_x_assum (qspecl_then [‘t3’, ‘q3’] mp_tac) \\ simp []
    \\ disch_then (qspecl_then [‘dec_clock (s2 with eval_config := ec2)’,
                                ‘decs2’] mp_tac)
    \\ impl_tac
    >- (simp [remove_ticks_decs_def, remove_ticks_exps_MAP]
        \\ drule state_rel_dec_clock \\ simp [])
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
         (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                               evaluate_more_clock))
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def]
    \\ ‘dec_clock (s2 with <|clock := ck' + s2.clock; eval_config := ec2|>) =
         dec_clock (s2 with eval_config := ec2) with
           clock := ck' + (dec_clock (s2 with eval_config := ec2)).clock’
      by (rw [dec_clock_def, state_component_equality] \\ decide_tac)
    \\ pop_assum SUBST_ALL_TAC \\ simp []
    \\ Cases_on ‘q3’ \\ Cases_on ‘r1’ \\ gvs [])
  \\ Cases_on ‘o' = Src (ThunkOp ForceThunk)’ \\ gvs []
  >- (
    (* forcing a thunk *)
    qspecl_then [‘t1'’, ‘s2’, ‘vs1’, ‘vs2’] mp_tac dest_thunk_thm \\ simp []
    \\ Cases_on ‘dest_thunk vs1 t1'.refs’ \\ gvs [] \\ rpt strip_tac
    >- (qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    >- (qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ rename1 ‘IsThunk m v’ \\ Cases_on ‘m’ \\ gvs []
    >- (qexists_tac ‘ck’ \\ simp [Once evaluate_def])
    \\ Cases_on ‘evaluate <|v := [(«f»,v)]|> t1' [AppUnit (Var_local None «f»)]’
    \\ rename1 ‘_ = (t3, q3)’
    \\ first_x_assum (qspecl_then [‘t3’, ‘q3’] mp_tac) \\ simp []
    \\ disch_then (qspecl_then [‘<|v := [(«f»,w)]|>’, ‘s2’,
                                ‘[AppUnit (Var_local None «f»)]’] mp_tac)
    \\ impl_tac >- simp [env_rel_def, AppUnit_def, remove_ticks_exp_def]
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
         (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                               evaluate_more_clock))
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def]
    \\ Cases_on ‘q3’ \\ Cases_on ‘r1’ \\ gvs []
    \\ rename1 ‘LIST_REL v_rel a1 b1’
    \\ qspecl_then [‘t3’, ‘s2'’, ‘vs1’, ‘vs2’, ‘a1’, ‘b1’] mp_tac
         update_thunk_thm
    \\ simp []
    \\ Cases_on ‘update_thunk vs1 t3.refs a1’ \\ gvs [] \\ rw [] \\ simp [])
  (* primitive operations *)
  \\ qexists_tac ‘ck’ \\ simp [Once evaluate_def]
  \\ Cases_on ‘do_app t1' o' (REVERSE vs1)’ \\ gvs []
  >- (
    Cases_on ‘do_app s2 o' (REVERSE vs2)’ \\ gvs []
    \\ rename1 ‘do_app s2 _ _ = SOME z’ \\ PairCases_on ‘z’
    \\ drule_then (qspecl_then [‘t1'’, ‘REVERSE vs1’] mp_tac) do_app_flip_thm
    \\ simp [flip_v_rel_simps, EVERY2_REVERSE])
  \\ rename1 ‘do_app t1' _ _ = SOME z’ \\ PairCases_on ‘z’
  \\ drule_then (qspecl_then [‘s2’, ‘REVERSE vs2’] mp_tac) do_app_thm
  \\ simp [EVERY2_REVERSE] \\ strip_tac \\ simp []
  \\ Cases_on ‘z1’ \\ gvs [evaluateTheory.list_result_def]
QED

Resume evaluate_remove_ticks[If]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [If _ _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 [remove_ticks_exp e]’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘[e]’] mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename1 ‘v_rel v1 v2’
  \\ drule do_if_thm \\ disch_then (qspecl_then [‘e0’, ‘e1'’] assume_tac)
  \\ Cases_on ‘do_if v2 e0 e1'’ \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ first_x_assum (qspecl_then [‘env2’, ‘s2’, ‘[x]’] mp_tac) \\ simp []
  \\ strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [evaluate_def]
QED

Resume evaluate_remove_ticks[Mat]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Mat _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 [remove_ticks_exp e']’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘[e']’] mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename1 ‘v_rel v1 v2’
  \\ qspecl_then [‘l’,‘t1'’,‘s2’,‘v1’,‘v2’] mp_tac
       (REWRITE_RULE [remove_ticks_exps_MAP] pmatch_rows_thm)
  \\ simp []
  \\ Cases_on ‘pmatch_rows (MAP (λ(p,e). (p,remove_ticks_exp e)) l) t1' v1’
  \\ gvs []
  >- (strip_tac \\ qexists_tac ‘ck’ \\ simp [evaluate_def]
      \\ simp [bind_exn_v_def, v_rel_l_cases])
  >- (strip_tac \\ qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ PairCases_on ‘a’ \\ gvs [] \\ strip_tac \\ gvs []
  \\ reverse (Cases_on ‘ALL_DISTINCT (pat_bindings a1)’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ first_x_assum (qspecl_then [‘<|v := env2' ++ env2.v|>’, ‘s2’, ‘[e2]’] mp_tac)
  \\ impl_tac
  >- (gvs [env_rel_def] \\ irule EVERY2_APPEND_suff \\ simp [])
  \\ strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [evaluate_def]
QED

Resume evaluate_remove_ticks[Let]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Let _ _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate env1 t1 [remove_ticks_exp e]’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘env2’, ‘s1’, ‘[e]’] mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename1 ‘v_rel v1 v2’
  \\ first_x_assum (qspecl_then [‘env2 with v updated_by opt_bind n v2’,
                                 ‘s2’, ‘[e0]’] mp_tac)
  \\ impl_tac >- (simp [] \\ irule env_rel_opt_bind \\ simp [])
  \\ strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate _ (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [evaluate_def]
QED

Resume evaluate_remove_ticks[Letrec]:
  sing_tac
  \\ qpat_x_assum ‘evaluate _ _ [Letrec _ _ _] = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ ‘MAP FST (MAP (λ(f,x,e). (f,x,remove_ticks_exp e)) l) = MAP FST l’
    by (rpt (pop_assum kall_tac) \\ Induct_on ‘l’ \\ simp [FORALL_PROD])
  \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  >- (rpt strip_tac
      \\ first_x_assum (drule_then (qspecl_then
           [‘<|v := build_rec_env l env2 env2.v|>’, ‘s1’, ‘[e']’] mp_tac))
      \\ impl_tac
      >- (simp [env_rel_def]
          \\ irule (REWRITE_RULE [remove_ticks_exps_MAP] build_rec_env_rel)
          \\ gvs [env_rel_def])
      \\ strip_tac
      \\ qexists_tac ‘ck’ \\ simp [evaluate_def])
  \\ rw [] \\ qexists_tac ‘0’ \\ simp [evaluate_def] \\ fs [state_rel_def]
QED

Resume evaluate_remove_ticks[dec]:
  qpat_x_assum ‘evaluate_dec _ _ = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate <|v := []|> t1 [remove_ticks_exp x]’
  \\ rename1 ‘_ = (t1', q1)’
  \\ first_x_assum (qspecl_then [‘t1'’, ‘q1’] mp_tac) \\ simp []
  \\ disch_then (qspecl_then [‘<|v := []|>’, ‘s1’, ‘[x]’] mp_tac)
  \\ simp [env_rel_def]
  \\ rpt strip_tac \\ qexists_tac ‘ck’ \\ simp [evaluate_def]
  \\ Cases_on ‘q1’ \\ gvs []
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename1 ‘v_rel a1 b1’
  \\ drule v_rel_Unitv \\ rw [] \\ gvs []
QED

Resume evaluate_remove_ticks[decs_cons]:
  gvs [MAP_EQ_CONS]
  \\ qpat_x_assum ‘evaluate_decs _ (_::_) = _’ mp_tac
  \\ simp [Once evaluate_def]
  \\ ‘∃t1' q1. evaluate_dec t1 (remove_ticks_exp x0) = (t1', q1)’
    by metis_tac [PAIR]
  \\ qpat_x_assum ‘∀t2 r2. evaluate_dec _ _ = _ ⇒ _’ drule
  \\ disch_then (qspecl_then [‘s1’, ‘x0’] mp_tac) \\ simp []
  \\ strip_tac \\ simp []
  \\ reverse (Cases_on ‘q1’) \\ gvs []
  >- (Cases_on ‘r1’ \\ gvs [] \\ rw []
      \\ qexists_tac ‘ck’ \\ simp [Once evaluate_def])
  \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [‘s2’, ‘t0’] mp_tac) \\ simp []
  \\ strip_tac
  \\ qexists_tac ‘ck + ck'’
  \\ qpat_assum ‘evaluate_dec (s1 with clock := _) _ = _’
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_dec_more_clock))
  \\ simp [] \\ strip_tac
  \\ simp [Once evaluate_def]
QED

Finalise evaluate_remove_ticks

(* preservation of observable semantics *)

Theorem remove_ticks_decs_eval_sim:
  install_conf_rel ic1 ic2 ⇒
  eval_sim ffi (remove_ticks_decs ds) ds ic2 ic1 (λds1 ds2. ds1 = remove_ticks_decs ds2) T
Proof
  rw [eval_sim_def]
  \\ drule (CONJUNCT2 (CONJUNCT2 evaluate_remove_ticks))
  \\ disch_then (qspecl_then [‘initial_state ffi k ic1’, ‘ds’] mp_tac)
  \\ impl_tac
  >- simp [remove_ticks_decs_def, remove_ticks_exps_MAP, state_rel_def,
           initial_state_def]
  \\ strip_tac
  \\ qexists_tac ‘ck’
  \\ gvs [initial_state_def, state_rel_def]
  \\ Cases_on ‘res1’ \\ Cases_on ‘r1’ \\ gvs []
  \\ rename1 ‘exc_rel _ e1 e2’ \\ Cases_on ‘e1’ \\ Cases_on ‘e2’ \\ gvs []
QED

Theorem remove_ticks_decs_semantics:
  install_conf_rel ic1 ic2 ⇒
  semantics ic2 ffi (remove_ticks_decs ds) = semantics ic1 ffi ds
Proof
  rw [] \\ irule IMP_semantics_eq_no_fail
  \\ qexists_tac ‘λds1 ds2. ds1 = remove_ticks_decs ds2’
  \\ simp [remove_ticks_decs_eval_sim]
QED

(* syntactic properties *)

Theorem remove_ticks_set_globals:
  (∀e. set_globals (remove_ticks_exp e) = set_globals e) ∧
  (∀es. elist_globals (remove_ticks_exps es) = elist_globals es) ∧
  (∀pes. elist_globals (MAP SND (remove_ticks_pes pes)) =
         elist_globals (MAP SND pes)) ∧
  (∀fs. elist_globals (MAP (SND o SND) (remove_ticks_funs fs)) =
        elist_globals (MAP (SND o SND) fs))
Proof
  ho_match_mp_tac remove_ticks_exp_ind \\ rw [remove_ticks_exp_def]
QED

Theorem remove_ticks_esgc_free:
  (∀e. esgc_free (remove_ticks_exp e) ⇔ esgc_free e) ∧
  (∀es. EVERY esgc_free (remove_ticks_exps es) ⇔ EVERY esgc_free es) ∧
  (∀pes. EVERY esgc_free (MAP SND (remove_ticks_pes pes)) ⇔
         EVERY esgc_free (MAP SND pes)) ∧
  (∀fs:(varN # varN # exp) list. T)
Proof
  ho_match_mp_tac remove_ticks_exp_ind
  \\ rw [remove_ticks_exp_def, remove_ticks_set_globals]
QED

Theorem remove_ticks_decs_esgc_free:
  EVERY esgc_free (remove_ticks_decs ds) ⇔ EVERY esgc_free ds
Proof
  simp [remove_ticks_decs_def, remove_ticks_esgc_free]
QED

Theorem remove_ticks_decs_elist_globals:
  elist_globals (remove_ticks_decs ds) = elist_globals ds
Proof
  simp [remove_ticks_decs_def, remove_ticks_set_globals]
QED
