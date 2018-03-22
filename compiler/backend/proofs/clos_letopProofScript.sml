open preamble closPropsTheory clos_inlineTheory closSemTheory;
open closLangTheory;
open backendPropsTheory;

val qexistsl_tac = map_every qexists_tac;
fun bump_assum pat = qpat_x_assum pat assume_tac;

val _ = new_theory "clos_letopProof";

val LENGTH_let_op = store_thm("LENGTH_let_op",
  ``!xs. LENGTH (let_op xs) = LENGTH xs``,
  recInduct let_op_ind \\ simp [let_op_def]
  \\ rw [] \\ CASE_TAC \\ simp []);

val let_op_SING = store_thm("let_op_SING",
  ``!x. ?y. let_op [x] = [y]``,
  Induct \\ fs [let_op_def] \\ CASE_TAC);

val HD_let_op_SING = store_thm("HD_let_op_SING[simp]",
  ``!x. [HD (let_op [x])] = let_op [x]``,
  strip_tac \\ strip_assume_tac (Q.SPEC `x` let_op_SING) \\ simp []);

(* *)

val code_rel_def = Define `
  code_rel e1 e2 <=>
    e2 = let_op e1`;

val code_rel_IMP_LENGTH = store_thm("code_rel_IMP_LENGTH",
  ``!xs ys. code_rel xs ys ==> LENGTH xs = LENGTH ys``,
  fs [code_rel_def, LENGTH_let_op]);

val code_rel_CONS_CONS = store_thm("code_rel_CONS_CONS",
  ``code_rel (x1::x2::xs) (y1::y2::ys) ==>
      code_rel [x1] [y1] /\ code_rel (x2::xs) (y2::ys)``,
  simp [code_rel_def, let_op_def]);

(* value relation *)

val f_rel_def = Define `
  f_rel (a1, e1) (a2, e2) <=>
     a1 = a2 /\ code_rel [e1] [e2]`;

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!i. v_rel (Number i) (Number i)) /\
  (!w. v_rel (Word64 w) (Word64 w)) /\
  (!w. v_rel (ByteVector w) (ByteVector w)) /\
  (!n. v_rel (RefPtr n) (RefPtr n)) /\
  (!tag xs ys.
     LIST_REL v_rel xs ys ==>
       v_rel (Block tag xs) (Block tag ys)) /\
  (!loc args1 args2 env1 env2 num_args e1 e2.
     LIST_REL v_rel env1 env2 /\
     LIST_REL v_rel args1 args2 /\
     code_rel [e1] [e2] ==>
       v_rel (Closure loc args1 env1 num_args e1) (Closure loc args2 env2 num_args e2)) /\
  (!loc args1 args2 env1 env2 k.
     LIST_REL v_rel env1 env2 /\
     LIST_REL v_rel args1 args2 /\
     LIST_REL f_rel funs1 funs2 ==>
       v_rel (Recclosure loc args1 env1 funs1 k) (Recclosure loc args2 env2 funs2 k))`;

val v_rel_simps = save_thm("v_rel_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (Number n) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (Block n p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (Word64 p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (ByteVector p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (RefPtr p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (Closure x1 x2 x3 x4 x5) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel (Recclosure y1 y2 y3 y4 y5) x``,
  prove(``v_rel (Boolv b) x <=> x = Boolv b``,
        Cases_on `b` \\ fs [Boolv_def,Once v_rel_cases]),
  prove(``v_rel Unit x <=> x = Unit``,
        fs [closSemTheory.Unit_def,Once v_rel_cases])])

(* state relation *)

val v_rel_opt_def = Define `
  (v_rel_opt NONE NONE <=> T) /\
  (v_rel_opt (SOME x) (SOME y) <=> v_rel x y) /\
  (v_rel_opt _ _ = F)`;

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL v_rel xs ys ==>
    ref_rel (ValueArray xs) (ValueArray ys))`

val FMAP_REL_def = Define `
  FMAP_REL r f1 f2 <=>
    FDOM f1 = FDOM f2 /\
    !k v. FLOOKUP f1 k = SOME v ==>
          ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2`;

val compile_inc_def = Define `
  compile_inc (e, xs) = (HD (let_op [e]), [])`;

val state_rel_def = Define `
  state_rel (s:('c, 'ffi) closSem$state) (t:('c, 'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    t.max_app = s.max_app /\ 1 <= s.max_app /\
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL v_rel_opt s.globals t.globals /\
    FMAP_REL ref_rel s.refs t.refs /\
    s.compile = pure_cc compile_inc t.compile /\
    t.compile_oracle = pure_co compile_inc o s.compile_oracle`;

(* *)

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y.
      v_rel x y ==>
      !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=>
           (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs []);

val v_rel_IMP_v_to_bytes = prove(
  ``v_rel x y ==> v_to_bytes y = v_to_bytes x``,
  rw [v_to_bytes_def] \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []);

val v_rel_IMP_v_to_words_lemma = prove(
  ``!x y.
      v_rel x y ==>
      !ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
           (v_to_list y = SOME (MAP Word64 ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs []);

val v_rel_IMP_v_to_words = prove(
  ``v_rel x y ==> v_to_words y = v_to_words x``,
  rw [v_to_words_def] \\ drule v_rel_IMP_v_to_words_lemma \\ fs []);


(* *)

val dest_op_SOME_IMP = store_thm("dest_op_SOME_IMP",
  ``!x args opp. dest_op x args = SOME opp ==>
      ?t xs. x = Op t opp xs /\
             var_list 0 xs args``,
  Cases \\ fs [dest_op_def]);


val var_list_IMP_LENGTH = store_thm("var_list_IMP_LENGTH",
  ``!n xs ys. var_list n xs ys ==> LENGTH xs = LENGTH ys``,
  Induct_on `xs` \\ Cases_on `ys` \\ fs [var_list_def]
  THEN1 (Cases_on `h` \\ fs [var_list_def])
  \\ rw []
  \\ Cases_on `h'` \\ fs [var_list_def]
  \\ res_tac);

val var_list_IMP_evaluate = prove(
  ``!a2 a1 xs (ys:closLang$exp list) (s:('c,'ffi) closSem$state) env.
      var_list (LENGTH a1) xs ys /\ LENGTH ys = LENGTH a2 ==>
      evaluate (xs,a1++a2++env,s) = (Rval a2,s)``,
  Induct THEN1 (rw [] \\ imp_res_tac var_list_IMP_LENGTH \\ fs [])
  \\ Cases_on `ys` \\ fs [LENGTH]
  \\ Cases_on `xs` \\ fs [var_list_def]
  \\ Cases_on `h'` \\ fs [var_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [evaluate_def, EL_LENGTH_APPEND] \\ rw []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ first_x_assum (qspec_then `a1 ++ [h']` mp_tac)
  \\ fs [] \\ rw [] \\ res_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]);

val var_list_IMP_evaluate = prove(
  ``!vs xs (ys:closLang$exp list) (s:('c,'ffi) closSem$state) env.
      var_list 0 xs ys /\ LENGTH ys = LENGTH vs ==>
        evaluate (xs, vs ++ env, s) = (Rval vs, s)``,
  rw []
  \\ match_mp_tac (Q.SPECL [`vs`, `[]`] var_list_IMP_evaluate
       |> SIMP_RULE std_ss [APPEND,LENGTH])
  \\ asm_exists_tac \\ fs []);


val lookup_vars_lemma = store_thm("lookup_vars_lemma",
  ``!vs env1 env2. LIST_REL v_rel env1 env2 ==>
    case lookup_vars vs env1 of
      | NONE => lookup_vars vs env2 = NONE
      | SOME l1 => ?l2. LIST_REL v_rel l1 l2 /\ lookup_vars vs env2 = SOME l2``,
  Induct_on `vs` \\ fs [lookup_vars_def]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw []
  \\ res_tac
  \\ Cases_on `lookup_vars vs env1`
  \\ fs []
  \\ fs [LIST_REL_EL_EQN]);

val find_code_lemma = store_thm("find_code_lemma",
  ``!s t p args. state_rel s t ==>
      find_code p args s.code = NONE /\
      find_code p args t.code = NONE``,
  fs [state_rel_def, find_code_def]);


val PUSH_IF = store_thm("PUSH_IF",
  ``!f b x y. (if b then f x else f y) = f (if b then x else y)``,
  METIS_TAC [])

val PUSH_EQ_IF = store_thm("PUSH_EQ_IF",
  ``!b x y z. (if b then x else y) = z <=> (if b then x = z else y = z)``,
  METIS_TAC []);


val dest_closure_SOME_IMP = store_thm("dest_closure_SOME_IMP",
  ``dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)``,
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []);

val dest_closure_SOME_Full_app = store_thm("dest_closure_SOME_Full_app",
  ``v_rel f1 f2 /\ v_rel a1 a2 /\ LIST_REL v_rel args1 args2 /\
    dest_closure max_app loc_opt f1 (a1::args1) = SOME (Full_app exp1 env1 rest_args1) ==>
      ?exp2 env2 rest_args2.
      code_rel [exp1] [exp2] /\
      LIST_REL v_rel env1 env2 /\
      LIST_REL v_rel rest_args1 rest_args2 /\
      dest_closure max_app loc_opt f2 (a2::args2) = SOME (Full_app exp2 env2 rest_args2)``,
   rpt strip_tac
   \\ imp_res_tac dest_closure_SOME_IMP
   \\ rveq \\ fs [] \\ rveq
   \\ imp_res_tac LIST_REL_LENGTH
   \\ qpat_x_assum `_ = SOME _` mp_tac
   THEN1 (rename1 `code_rel [e1] [e2]`
          \\ simp [dest_closure_def]
          \\ IF_CASES_TAC \\ simp []
          \\ strip_tac \\ rveq \\ fs []
          \\ conj_tac
          THEN1 (ntac 2 (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_REVERSE
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp []
                 \\ irule EVERY2_REVERSE \\ simp [])
          \\ irule EVERY2_REVERSE
          \\ irule EVERY2_DROP
          \\ irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_REVERSE \\ simp [])
   \\ rename1 `LIST_REL f_rel fns1 fns2`
   \\ simp [dest_closure_def]
   \\ ntac 2 (pairarg_tac \\ simp [])
   \\ Cases_on `i < LENGTH fns2` \\ simp []
   \\ IF_CASES_TAC \\ simp []
   \\ strip_tac \\ rveq \\ fs []
   \\ bump_assum `LIST_REL f_rel _ _`
   \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
   \\ simp [] \\ disch_then drule
   \\ simp [f_rel_def]
   \\ strip_tac \\ fs []
   \\ conj_tac
   THEN1 (irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_APPEND_suff \\ simp [LIST_REL_GENLIST]
          \\ irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_REVERSE
          \\ irule EVERY2_TAKE
          \\ irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_REVERSE \\ simp [])
   \\ irule EVERY2_REVERSE
   \\ irule EVERY2_DROP
   \\ irule EVERY2_APPEND_suff \\ simp []
   \\ irule EVERY2_REVERSE \\ simp [])

(* evaluate_let_op *)

val evaluate_let_op = store_thm("evaluate_let_op",
  ``(!xs env1 (s1:('c,'ffi) closSem$state) res1 s2 ys env2 t1.
       evaluate (xs, env1, s1) = (res1, s2) /\
       LIST_REL v_rel env1 env2 /\ state_rel s1 t1 /\
       code_rel xs ys ==>
       ?res2 t2.
         evaluate (ys, env2, t1) = (res2, t2) /\
         result_rel (LIST_REL v_rel) v_rel res1 res2 /\
         state_rel s2 t2) /\
    (!loc_opt f1 args1 (s1:('c,'ffi) closSem$state) res1 s2 f2 args2 t1.
       evaluate_app loc_opt f1 args1 s1 = (res1, s2) /\
       v_rel f1 f2 /\ LIST_REL v_rel args1 args2 /\
       state_rel s1 t1 ==>
       ?res2 t2.
         evaluate_app loc_opt f2 args2 t1 = (res2, t2) /\
         result_rel (LIST_REL v_rel) v_rel res1 res2 /\
         state_rel s2 t2)``,

  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac
  \\ imp_res_tac code_rel_IMP_LENGTH \\ fs [LENGTH_EQ_NUM_compute] \\ rveq
  THEN1 (* NIL *)
   (fs [evaluate_def] \\ rw [])
  THEN1 (* CONS *)
   (fs [LENGTH_EQ_NUM] \\ rveq
    \\ fs [evaluate_def]
    \\ imp_res_tac code_rel_CONS_CONS
    \\ reverse (fs [case_eq_thms, pair_case_eq]) 
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [] (* Closes Rerr *)
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [] (* Closes Rval :: Rerr *)
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  THEN1 (* Var *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ rveq \\ fs [])
  THEN1 (* If *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ reverse (fs [case_eq_thms, pair_case_eq])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac
    \\ rveq \\ fs [] (* Closes Rerr *)
    \\ `(Boolv T = HD v' <=> Boolv T = HD vs) /\
        (Boolv F = HD v' <=> Boolv F = HD vs)` by
         (imp_res_tac evaluate_SING
          \\ rveq \\ fs [] \\ rveq
          \\ qpat_x_assum `v_rel _ _` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp [EVAL ``closSem$Boolv T``,EVAL ``closSem$Boolv F``]
          \\ rw [] \\ eq_tac \\ rw []
          \\ fs [Once v_rel_cases])
    \\ ntac 2 (pop_assum (fn th => fs [th]))
    \\ IF_CASES_TAC
    \\ TRY (IF_CASES_TAC)
    \\ fs [] \\ rveq \\ fs [])
  THEN1 (* Let *)
   (fs [code_rel_def, let_op_def]
    \\ fs [case_eq_thms] \\ rveq
    THEN1
     (fs [evaluate_def]
      \\ reverse (fs [pair_case_eq, case_eq_thms])
      \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ strip_tac
      \\ fs [] \\ rveq
      \\ `LIST_REL v_rel (vs ++ env1) (v' ++ env2)`
           by (irule EVERY2_APPEND_suff \\ simp [])
      \\ first_x_assum drule
      \\ disch_then drule
      \\ strip_tac \\ fs [])
    \\ fs [evaluate_def]
    \\ reverse (fs [pair_case_eq, case_eq_thms])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ fs []
    \\ `LIST_REL v_rel (vs ++ env1) (v' ++ env2)`
         by (irule EVERY2_APPEND_suff \\ simp [])
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ fs []
    \\ imp_res_tac dest_op_SOME_IMP
    \\ fs []
    \\ strip_assume_tac (Q.SPEC `x2` let_op_SING)
    \\ fs [] \\ rveq
    \\ fs [evaluate_def]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ drule var_list_IMP_evaluate
    \\ disch_then drule
    \\ disch_then (qspecl_then [`t2`, `env2`] assume_tac)
    \\ fs [])
  THEN1 (* Raise *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]   
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [])
  THEN1 (* Handle *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]   
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs [])
  THEN1 (* Op *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]   
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ IF_CASES_TAC \\ rveq \\ fs []
    THEN1
     (drule EVERY2_REVERSE
      \\ qabbrev_tac `a1 = REVERSE vs`
      \\ qabbrev_tac `a2 = REVERSE v'`
      \\ strip_tac
      \\ qpat_x_assum `_ = (res1, s2)` mp_tac
      \\ simp [Once do_install_def]
      \\ Cases_on `a1`
      THEN1 (fs [do_install_def] \\ rw [] \\ fs [])
      \\ Cases_on `t`
      THEN1 (fs [do_install_def] \\ rw [] \\ fs [])   
      \\ reverse (Cases_on `t'`)
      THEN1 (fs [do_install_def] \\ rw [] \\ fs [])
      \\ fs [] \\ rveq
      \\ rename1 `v_rel x2 y2` \\ pop_assum mp_tac
      \\ drule v_rel_IMP_v_to_bytes \\ strip_tac
      \\ rename1 `v_rel x1 y1` \\ strip_tac
      \\ drule v_rel_IMP_v_to_words \\ strip_tac \\ fs []
      \\ Cases_on `v_to_bytes x1` \\ fs []
      THEN1 (fs [do_install_def] \\ rw [] \\ fs [])
      \\ Cases_on `v_to_words x2` \\ fs []
      THEN1 (fs [do_install_def] \\ rw [] \\ fs [])
      \\ pairarg_tac \\ fs []
      \\ PairCases_on `progs`     
      \\ Cases_on `t2.compile_oracle 0`
      \\ PairCases_on `r`
      \\ `r1 = [] /\ progs1 = []` by
         (fs [state_rel_def] \\ rfs [pure_co_def] \\ fs [compile_inc_def]
          \\ rveq \\ fs [] \\ metis_tac [SND])
      \\ rveq \\ fs []    
      \\ Cases_on `s'.compile cfg (progs0,[])` \\ fs []
      THEN1 (fs [do_install_def] \\ rw []
             \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
             \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def])
      \\ rename1 `_ = SOME xx` \\ PairCases_on `xx` \\ fs []
      \\ reverse IF_CASES_TAC
      THEN1 (fs [do_install_def] \\ rw []
             \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
             \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def]
             \\ IF_CASES_TAC \\ fs [shift_seq_def])
      \\ IF_CASES_TAC
      THEN1 (fs [do_install_def] \\ rw []
             \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
             \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def]
             \\ IF_CASES_TAC \\ fs [shift_seq_def])
      \\ fs [] \\ rveq \\ fs []
      \\ fs [do_install_def] \\ strip_tac
      \\ first_x_assum drule
      \\ qmatch_goalsub_abbrev_tac `Rval (r0, tt)`
      \\ disch_then (qspec_then `tt` mp_tac)
      \\ impl_tac
      THEN1 (qunabbrev_tac `tt`
             \\ fs [state_rel_def, shift_seq_def, FUPDATE_LIST, o_DEF])
      \\ strip_tac \\ fs []
      \\ unabbrev_all_tac \\ fs []
      \\ rw []
      \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
      \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def]
      \\ fs [shift_seq_def]
      \\ rveq \\ fs [])
   \\ cheat (* op <> Install *))
  THEN1 (* Fn *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs []
    \\ IF_CASES_TAC
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ fs [Once case_eq_thms] \\ rveq
    THEN1 (fs [code_rel_def])
    \\ drule (Q.SPEC `vs` lookup_vars_lemma)
    \\ CASE_TAC \\ strip_tac
    \\ fs [] \\ rveq \\ fs [code_rel_def])
  THEN1 (* Letrec *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ qpat_x_assum `_ = (res1, s2)` mp_tac
    \\ fs [evaluate_def]
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs [EVERY_MAP]
    \\ reverse (IF_CASES_TAC \\ IF_CASES_TAC)
    THEN1 (strip_tac \\ fs [] \\ rveq \\ fs [])
    \\ TRY (fs [EXISTS_MEM]
           \\ rename1 `MEM fff fns`
           \\ fs [EVERY_MEM] \\ res_tac
           \\ PairCases_on `fff` \\ fs [])
    \\ strip_tac
    \\ Cases_on `namesopt` \\ fs []
    THEN1 (first_x_assum irule \\ fs []
           \\ irule EVERY2_APPEND_suff \\ fs []
           \\ fs [LIST_REL_GENLIST] \\ rw []
           \\ fs [LIST_REL_EL_EQN] \\ rw []
           \\ fs [EL_MAP]
           \\ pairarg_tac
           \\ fs [f_rel_def, code_rel_def])
    \\ drule (Q.SPEC `x` lookup_vars_lemma)
    \\ CASE_TAC \\ fs [] \\ rveq \\ fs []
    \\ strip_tac \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ irule EVERY2_APPEND_suff \\ fs []
    \\ fs [LIST_REL_GENLIST] \\ rw []
    \\ fs [LIST_REL_EL_EQN] \\ rw []
    \\ fs [EL_MAP]
    \\ pairarg_tac
    \\ fs [f_rel_def, code_rel_def])
  THEN1 (* App *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ fs [LENGTH_let_op]
    \\ reverse IF_CASES_TAC
    \\ fs [] \\ rveq \\ fs []
    \\ reverse (fs [case_eq_thms, pair_case_eq])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ fs [] (* Closes xs => Rerr *)
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ fs [] (* Closes xs => Rval, x1 => Rerr *)
    \\ rename1 `LIST_REL v_rel y1 yy`
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  THEN1 (* Tick *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ fs [dec_clock_def, state_rel_def])
  THEN1 (* Call *)
   (fs [code_rel_def, let_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ fs [Once case_eq_thms, pair_case_eq]
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq
    \\ fs [state_rel_def, find_code_def]
    \\ rveq \\ fs [])
  THEN1 (* evaluate_app NIL *)
   (simp [])
  (* evaluate_app CONS *)
  \\ fs [evaluate_def]
  \\ `s1.max_app = t1.max_app` by fs [state_rel_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  THEN1 (* dest_closure returns NONE *)
   (fs [dest_closure_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [PUSH_IF]
    \\ pairarg_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ Cases_on `i < LENGTH funs2` \\ fs []
    \\ bump_assum `LIST_REL f_rel _ _`
    \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
    \\ fs [] \\ disch_then drule \\ fs [f_rel_def]
    \\ strip_tac \\ fs [])
  THEN1 (* dest_closure returns SOME Partial_app *)
   (imp_res_tac dest_closure_SOME_IMP
    \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ qpat_x_assum `_ = SOME (Partial_app _)` mp_tac
    \\ fs [dest_closure_def]
    \\ TRY (ntac 2 (pairarg_tac \\ fs [])
            \\ Cases_on `i < LENGTH funs2` \\ fs []
            \\ bump_assum `LIST_REL f_rel _ _`
            \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
            \\ fs [] \\ disch_then drule
            \\ fs [f_rel_def]
            \\ strip_tac \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [dec_clock_def, state_rel_def]
    \\ irule EVERY2_APPEND_suff \\ fs [])

  (* dest_closure returns SOME Full_app *)
  \\ bump_assum `v_rel f1 f2`
  \\ drule (GEN_ALL dest_closure_SOME_Full_app)
  \\ pop_assum kall_tac
  \\ ntac 3 (disch_then drule)
  \\ strip_tac \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ `s1.clock = t1.clock` by fs [state_rel_def]
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  THEN1 fs [state_rel_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac `evaluate (xxx2, _, sss2)`
  \\ disch_then (qspecl_then [`xxx2`, `sss2`] mp_tac)
  \\ unabbrev_all_tac \\ simp []
  \\ impl_tac THEN1 fs [dec_clock_def, state_rel_def]
  \\ strip_tac \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []


  (* Alternate version that doesnt use dest_closure_SOME_Full_app *)
  (* dest_closure returns SOME Full_app *)
  \\ imp_res_tac dest_closure_SOME_IMP
  \\ rveq \\ fs [] \\ rveq
  \\ imp_res_tac LIST_REL_LENGTH
  \\ `s1.clock = t1.clock` by fs [state_rel_def]
  \\ qpat_x_assum `_ = SOME _` mp_tac
  \\ fs [dest_closure_def]
  THEN1
   (IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    THEN1 fs [state_rel_def]
    \\ fs [pair_case_eq]
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate (xxx2, eee2, sss2)`
    \\ qmatch_asmsub_abbrev_tac `evaluate (_, eee1, _)`
    \\ `LIST_REL v_rel eee1 eee2`
       by (unabbrev_all_tac
           \\ ntac 2 (irule EVERY2_APPEND_suff \\ fs [])
           \\ irule EVERY2_REVERSE
           \\ irule EVERY2_TAKE
           \\ irule EVERY2_APPEND_suff \\ fs []
           \\ irule EVERY2_REVERSE \\ fs [])
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`xxx2`, `sss2`] mp_tac)
    \\ unabbrev_all_tac
    \\ impl_tac THEN1 fs [dec_clock_def, state_rel_def]
    \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq
    \\ first_x_assum irule \\ fs []
    \\ irule EVERY2_REVERSE
    \\ irule EVERY2_DROP
    \\ irule EVERY2_APPEND_suff \\ simp []
    \\ irule EVERY2_REVERSE \\ simp [])
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ Cases_on `i < LENGTH funs2` \\ fs []
  \\ bump_assum `LIST_REL f_rel _ _`
  \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
  \\ fs [] \\ disch_then drule
  \\ simp [f_rel_def]
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  THEN1 fs [state_rel_def]
  \\ fs [pair_case_eq]
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac `evaluate (xxx2, eee2, sss2)`
  \\ qmatch_asmsub_abbrev_tac `evaluate (_, eee1, _)`
  \\ `LIST_REL v_rel eee1 eee2`
     by (unabbrev_all_tac
         \\ irule EVERY2_APPEND_suff \\ simp []
         \\ irule EVERY2_APPEND_suff \\ simp [LIST_REL_GENLIST]
         \\ irule EVERY2_APPEND_suff \\ simp []
         \\ irule EVERY2_REVERSE
         \\ irule EVERY2_TAKE
         \\ irule EVERY2_APPEND_suff \\ simp []
         \\ irule EVERY2_REVERSE \\ simp [])
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`xxx2`, `sss2`] mp_tac)
  \\ unabbrev_all_tac
  \\ impl_tac THEN1 fs [dec_clock_def, state_rel_def]
  \\ strip_tac
  \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq
  \\ first_x_assum irule \\ simp []
  \\ irule EVERY2_REVERSE
  \\ irule EVERY2_DROP
  \\ irule EVERY2_APPEND_suff \\ simp []
  \\ irule EVERY2_REVERSE \\ simp []
