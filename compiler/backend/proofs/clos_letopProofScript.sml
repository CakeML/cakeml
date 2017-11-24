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
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (Number n)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (Block n p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (Word64 p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (ByteVector p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (RefPtr p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (Closure x1 x2 x3 x4 x5)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel x (Recclosure y1 y2 y3 y4 y5)``,
  prove(``v_rel x (Boolv b) <=> x = Boolv b``,
        Cases_on `b` \\ fs [Boolv_def,Once v_rel_cases]),
  prove(``v_rel x Unit <=> x = Unit``,
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
   (fs [code_rel_def, let_op_def]
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

)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)
  THEN1
   (cheat)

