(* A proof of the clos_mti compiler pass. The theorem is proved using
   a backwards simulation, i.e. against the direction of compilation. *)
open preamble; open closPropsTheory
clos_mtiTheory closSemTheory;

val _ = new_theory "clos_mtiProof";

fun bring_fwd_ctors th ty = map ((fn s=> Parse.bring_to_front_overload s {Name = s,Thy = th}) o term_to_string) (TypeBase.constructors_of ty)

val _ = bring_fwd_ctors "closLang" ``:closLang$exp``

(* well-formed syntax *)

val closLang_exp_size_lemma = prove(
  ``!funs. MEM (p_1,p_2) funs ==> closLang$exp_size p_2 < exp3_size (MAP SND funs)``,
  Induct \\ fs [closLangTheory.exp_size_def,FORALL_PROD]
  \\ rw [] \\ fs []);

val syntax_ok_def = tDefine "syntax_ok" `
  (syntax_ok [] <=> T) ∧
  (syntax_ok (e1::e2::es) <=>
    syntax_ok [e1] /\
    syntax_ok (e2::es)) /\
  (syntax_ok [Var t n] = T) ∧
  (syntax_ok [If t e1 e2 e3] <=>
    syntax_ok [e1] /\
    syntax_ok [e2] /\
    syntax_ok [e3]) ∧
  (syntax_ok [Let t es e] <=>
    syntax_ok es /\
    syntax_ok [e]) ∧
  (syntax_ok [Raise t e] <=>
    syntax_ok [e]) ∧
  (syntax_ok [Handle t e1 e2] <=>
    syntax_ok [e1] /\
    syntax_ok [e2]) ∧
  (syntax_ok [Tick t e] <=>
    syntax_ok [e]) ∧
  (syntax_ok [Call t ticks n es] = F) /\
  (syntax_ok [App t opt e es] <=>
    LENGTH es = 1 /\ opt = NONE /\
    syntax_ok es /\
    syntax_ok [e]) ∧
  (syntax_ok [Fn t opt1 opt2 num_args e] <=>
    num_args = 1 /\ opt1 = NONE /\ opt2 = NONE /\
    syntax_ok [e]) /\
  (syntax_ok [Letrec t opt1 opt2 funs e] <=>
    syntax_ok [e] /\ opt1 = NONE /\ opt2 = NONE /\
    EVERY (\x. FST x = 1 /\ syntax_ok [SND x]) funs) ∧
  (syntax_ok [Op t op es] <=>
    syntax_ok es)`
  (WF_REL_TAC `measure exp3_size` \\ rw []
   \\ imp_res_tac closLang_exp_size_lemma \\ fs []);

val syntax_ok_cons = store_thm("syntax_ok_cons",
  ``syntax_ok (x::xs) <=> syntax_ok [x] /\ syntax_ok xs``,
  Cases_on `xs` \\ fs [syntax_ok_def]);

val syntax_ok_append = store_thm("syntax_ok_append[simp]",
  ``!xs ys. syntax_ok (xs ++ ys) <=> syntax_ok xs /\ syntax_ok ys``,
  Induct \\ fs [syntax_ok_def]
  \\ once_rewrite_tac [syntax_ok_cons]
  \\ fs [syntax_ok_def] \\ rw [] \\ eq_tac \\ rw[]);

(* code relation *)

val code_rel_def = Define `
  code_rel max_app e1 e2 <=>
    syntax_ok e1 /\ (e2 = intro_multi max_app e1)`

val code_rel_IMP_LENGTH = store_thm("code_rel_IMP_LENGTH",
  ``code_rel max_app xs ys ==> LENGTH ys = LENGTH xs``,
  rw [code_rel_def,clos_mtiTheory.intro_multi_length]);

val HD_intro_multi = store_thm("HD_intro_multi[simp]",
  ``[HD (intro_multi max_app [e2])] = intro_multi max_app [e2]``,
  `?x. intro_multi max_app [e2] = [x]` by metis_tac [intro_multi_sing]
  \\ fs []);

val intro_multi_cons = store_thm("intro_multi_cons",
  ``!xs x. intro_multi m (x::xs) = HD (intro_multi m [x]) :: intro_multi m xs``,
  Induct \\ fs[intro_multi_def]);

val code_rel_CONS_CONS = store_thm("code_rel_CONS_CONS",
  ``code_rel m (x1::x2::xs) (y1::y2::ys) <=>
    code_rel m [x1] [y1] /\ code_rel m (x2::xs) (y2::ys)``,
  fs [code_rel_def,syntax_ok_def,intro_multi_def]
  \\ `?t1. intro_multi m [x1] = [t1]` by metis_tac [intro_multi_sing]
  \\ `?t2. intro_multi m [x2] = [t2]` by metis_tac [intro_multi_sing]
  \\ fs [] \\ eq_tac \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [intro_multi_cons] \\ fs []);

(* value relation *)

val mk_Fns_def = Define `
  mk_Fns [] e = e /\
  mk_Fns (t::ts) e = Fn t NONE NONE 1 (mk_Fns ts e)`

val f_rel_def = Define `
  f_rel max_app (a1,e1) (a2,e2) <=>
    ?b1 ts.
      code_rel max_app [b1] [e2] /\ a2 <= max_app /\ syntax_ok [b1] /\
      a1 = 1n /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1`

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!i. v_rel (max_app:num) (Number i) (closSem$Number i)) /\
  (!w. v_rel max_app (Word64 w) (Word64 w)) /\
  (!b. v_rel max_app (ByteVector w) (ByteVector b)) /\
  (!n. v_rel max_app (RefPtr n) (RefPtr n)) /\
  (!tag xs ys.
     LIST_REL (v_rel max_app) xs ys ==>
     v_rel max_app (Block tag xs) (Block tag ys)) /\
  (!args1 args2 env1 env2 arg_count e1 ts e2.
     1 + LENGTH ts + LENGTH args1 = arg_count /\
     code_rel max_app [e1] [e2] /\
     LIST_REL (v_rel max_app) env1 env2 /\
     LIST_REL (v_rel max_app) args1 args2 ==>
     v_rel max_app
       (Closure NONE [] (args1 ++ env1) 1 (mk_Fns ts e1))
       (Closure NONE args2 env2 arg_count e2)) /\
  (!env1 funs1 env2 funs2 n.
     LIST_REL (f_rel max_app) funs1 funs2 /\
     LIST_REL (v_rel max_app) env1 env2 /\
     n < LENGTH funs2 ==>
     v_rel max_app
       (Recclosure NONE [] env1 funs1 n)
       (Recclosure NONE [] env2 funs2 n)) /\
  (!args1 env1 funs1 args2 env2 funs2 n recc ts e1 e2 arg_count.
     LIST_REL (f_rel max_app) funs1 funs2 /\
     LIST_REL (v_rel max_app) env1 env2 /\
     LIST_REL (v_rel max_app) args1 args2 /\ args2 <> [] /\
     n < LENGTH funs2 /\ EL n funs2 = (arg_count,e2) /\
     1 + LENGTH ts + LENGTH args1 = arg_count /\
     code_rel max_app [e1] [e2] /\
     LIST_REL (v_rel max_app) recc
          (GENLIST (Recclosure NONE [] env2 funs2) (LENGTH funs2)) ==>
     v_rel max_app
       (Closure NONE [] (args1 ++ recc ++ env1) 1 (mk_Fns ts e1))
       (Recclosure NONE args2 env2 funs2 n))`

val v_rel_opt_def = Define `
  (v_rel_opt max_app NONE NONE <=> T) /\
  (v_rel_opt max_app (SOME x) (SOME y) <=> v_rel max_app x y) /\
  (v_rel_opt max_app _ _ = F)`;

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel max_app (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL (v_rel max_app) xs ys ==>
    ref_rel max_app (ValueArray xs) (ValueArray ys))`

val FMAP_REL_def = Define `
  FMAP_REL r f1 f2 <=>
    FDOM f1 = FDOM f2 /\
    !k v. FLOOKUP f1 k = SOME v ==>
          ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2`;

(* state relation *)

val state_rel_def = Define `
  state_rel (s:'ffi closSem$state) (t:'ffi closSem$state) <=>
    s.code = FEMPTY /\ t.code = FEMPTY /\
    t.max_app = s.max_app /\ 1 <= s.max_app /\
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL (v_rel_opt s.max_app) s.globals t.globals /\
    FMAP_REL (ref_rel s.max_app) s.refs t.refs`;

(* evaluation theorem *)

val collect_args_IMP = store_thm("collect_args_IMP",
  ``!max_app k e1 num_args e2.
      collect_args max_app k e1 = (num_args,e2) /\ k <= max_app ==>
      k <= num_args /\ num_args <= max_app``,
  recInduct collect_args_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ fs [collect_args_def]
  \\ rw [] \\ fs []);

val collect_args_ok_IMP = store_thm("collect_args_ok_IMP",
  ``!max_app k e num_args e2.
      collect_args max_app k e = (num_args,e2) /\ syntax_ok [e] ==>
      ?ts. e = mk_Fns ts e2 ∧ num_args = k + LENGTH ts /\
           syntax_ok [e2]``,
  recInduct collect_args_ind
  \\ rw [] \\ fs []
  \\ fs [collect_args_def] \\ rveq
  \\ TRY (fs [collect_args_def] \\ rveq
          \\ qexists_tac `[]` \\ fs [mk_Fns_def] \\ NO_TAC)
  \\ FULL_CASE_TAC \\ rveq
  \\ TRY (fs [collect_args_def] \\ rveq
          \\ qexists_tac `[]` \\ fs [mk_Fns_def] \\ NO_TAC)
  \\ first_x_assum drule
  \\ fs [syntax_ok_def] \\ rveq
  \\ strip_tac \\ fs [] \\ rveq
  \\ qexists_tac `t::ts` \\ fs [mk_Fns_def]);

val dest_closure_SOME_IMP = store_thm("dest_closure_SOME_IMP",
  ``dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)``,
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []);

val collect_apps_acc = prove(
  ``!max_app acc e res s.
      collect_apps max_app acc e = (res,s) ==>
      ?other. res = acc ++ other``,
  recInduct collect_apps_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [collect_apps_def]
  \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ res_tac \\ fs []);

val collect_apps_cons_lemma = prove(
  ``!e1 m ys other e2.
      collect_apps (m+LENGTH ys) ys e1 = (ys ++ other,e2) <=>
      collect_apps m [] e1 = (other,e2)``,
  Induct \\ fs [collect_apps_def]
  \\ rw [] \\ Cases_on `o'` \\ fs [collect_apps_def]
  \\ rw [] \\ fs []
  \\ fs [LESS_EQ_EXISTS]
  \\ Cases_on `collect_apps (p + LENGTH l) l e1`
  \\ drule collect_apps_acc
  \\ strip_tac \\ rveq \\ fs []
  \\ Cases_on `collect_apps (p + (LENGTH l + LENGTH ys)) (ys ⧺ l) e1`
  \\ drule collect_apps_acc
  \\ strip_tac \\ rveq \\ fs []
  \\ pop_assum mp_tac
  \\ `(LENGTH l + LENGTH ys) = LENGTH (ys ++ l)` by fs []
  \\ asm_rewrite_tac []
  \\ rfs []);

val collect_apps_cons = prove(
  ``!e1 m x other e2.
      collect_apps m [x] e1 = (x::other,e2) /\ m <> 0 ==>
      collect_apps (m-1) [] e1 = (other,e2)``,
  once_rewrite_tac [collect_apps_cons_lemma |> GSYM
       |> Q.SPECL [`e1`,`m`,`[x]`]
       |> SIMP_RULE std_ss [LENGTH,APPEND]] \\ rw []);

val mk_Apps_def = Define `
  mk_Apps e [] = e /\
  mk_Apps e ((t,other)::ts) = App t NONE (mk_Apps e ts) [other]`

val collect_apps_IMP_mk_Apps = prove(
  ``!es max_app (acc:closLang$exp list) e other e3.
      collect_apps max_app [] e = (other,e3) /\ syntax_ok es /\ es = [e] ==>
      ?ts. e = mk_Apps e3 (ZIP (ts, other)) /\ LENGTH other = LENGTH ts /\
           LENGTH other <= max_app``,
  recInduct (theorem "syntax_ok_ind") \\ fs [] \\ rw []
  \\ fs [collect_apps_def] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def]
          \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [syntax_ok_def] \\ rveq
  \\ fs [collect_apps_def] \\ rveq
  \\ FULL_CASE_TAC \\ fs [] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [syntax_ok_def]
  \\ Cases_on `es` \\ fs [] \\ rveq
  \\ imp_res_tac collect_apps_acc \\ rveq \\ fs []
  \\ drule (GEN_ALL collect_apps_cons) \\ fs []
  \\ strip_tac \\ first_x_assum drule
  \\ strip_tac \\ rveq \\ fs []
  \\ qexists_tac `t::ts` \\ fs [ZIP,mk_Apps_def])
  |> SIMP_RULE std_ss [];

val mk_Apps_err_1 = prove(
  ``∀ts other env1 s1 e3.
      evaluate (other,env1,s1) = (Rerr e2,s2) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e3 (ZIP (ts,other))],env1,s1) = (Rerr e2,s2)``,
  Induct
  \\ fs [evaluate_def]
  \\ Cases_on `other` \\ fs [ZIP,mk_Apps_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ fs [case_eq_thms,pair_case_eq]
  \\ rveq \\ fs [] \\ fs [evaluate_def]);

val mk_Apps_err_2 = prove(
  ``∀ts other env1 s1 e3 vs.
      evaluate ([e3],env1,s2) = (Rerr e2,s2') /\
      evaluate (other,env1,s1) = (Rval vs,s2) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e3 (ZIP (ts,other))],env1,s1) = (Rerr e2,s2')``,
  Induct
  \\ fs [evaluate_def,mk_Apps_def]
  \\ Cases_on `other` \\ fs [ZIP,mk_Apps_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ fs [case_eq_thms,pair_case_eq]
  \\ rveq \\ fs [] \\ fs [evaluate_def]
  \\ imp_res_tac evaluate_SING \\ rveq \\ fs []);

val collect_apps_syntax_ok = store_thm("collect_apps_syntax_ok",
  ``!k aux e res e1.
      collect_apps k aux e = (res,e1) /\
      syntax_ok [e] /\ syntax_ok aux ==>
      syntax_ok res /\ syntax_ok [e1]``,
  recInduct collect_apps_ind
  \\ rw [collect_apps_def] \\ fs []
  \\ fs [syntax_ok_def]);

val evaluate_mk_Apps_err = prove(
  ``!other ts env1 s1 vs.
      evaluate (other,env1,s1) = (Rval vs,s3) /\
      evaluate ([e],env1,s3) = (Rerr e3,s2') /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e (ZIP (ts,other))],env1,s1) = (Rerr e3,s2')``,
  Induct \\ Cases_on `ts` \\ fs [mk_Apps_def]
  \\ fs [evaluate_def]
  \\ simp [Once evaluate_CONS] \\ rw []
  \\ fs [case_eq_thms,pair_case_eq] \\ rveq);

val evaluate_apps_def = Define `
  evaluate_apps f [] s = (Rval [f], s) /\
  evaluate_apps f (x::xs) s =
    case evaluate_apps f xs s of
    | (Rval [v], s1) => evaluate_app NONE v [x] s1
    | res => res`;

val evaluate_mk_Apps_ok = prove(
  ``!other ts env1 s1 vs.
      evaluate ([e],env1,s3) = (Rval [f],s2') /\
      evaluate (other,env1,s1) = (Rval vs,s3) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e (ZIP (ts,other))],env1,s1) =
      evaluate_apps f vs s2'``,
  once_rewrite_tac [CONJ_COMM]
  \\ Induct \\ Cases_on `ts` \\ fs [mk_Apps_def]
  \\ fs [evaluate_def,evaluate_apps_def]
  \\ simp [Once evaluate_CONS] \\ rw []
  \\ fs [case_eq_thms,pair_case_eq] \\ rveq
  \\ first_x_assum (qspec_then `t` mp_tac) \\ fs []
  \\ rpt (disch_then drule)
  \\ strip_tac \\ fs []
  \\ Cases_on `evaluate_apps f vs' s2'` \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs []
  \\ rveq \\ fs []
  \\ fs [evaluate_apps_def]
  \\ Cases_on `q` \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs []
  \\ rveq \\ fs []);

val dest_closure_NONE_IMP_apps = prove(
  ``!xs f1 s1.
      dest_closure s1.max_app NONE f1 [LAST xs] = NONE /\ xs <> [] ==>
      evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)``,
  Induct \\ fs [evaluate_apps_def]
  \\ Cases_on `xs` \\ fs [evaluate_apps_def]
  \\ fs [evaluate_apps_def,evaluate_def]);

val evaluate_apps_SNOC = prove(
  ``!xs x f s.
      evaluate_apps f (SNOC x xs) s =
      case evaluate_app NONE f [x] s of
      | (Rval [v], s) => evaluate_apps v xs s
      | res => res``,
  Induct
  THEN1 (fs [evaluate_apps_def] \\ rw []
         \\ every_case_tac \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ fs [evaluate_apps_def] \\ rw []
  \\ Cases_on `evaluate_app NONE f [x] s` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val evaluate_apps_Clos_timeout = prove(
  ``!ys ts s1 e1 env.
      s1.clock < LENGTH ys /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)``,
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock < LENGTH l` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]);

val evaluate_apps_Clos_timeout_alt = prove(
  ``!ys ts s1 e1 env.
      s1.clock <= LENGTH ts /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)``,
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock <= LENGTH t` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]);

val evaluate_apps_Clos_short = prove(
  ``!ys ts s1 e1 env.
      LENGTH ys <= s1.clock /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
         (Rval [Closure NONE [] (ys ++ env) 1
                   (mk_Fns (DROP (LENGTH ys) ts) e1)],
          dec_clock (LENGTH ys) s1)``,
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC,evaluate_apps_def]
  THEN1 (fs [state_component_equality,dec_clock_def])
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `LENGTH l <= (dec_clock 1 s1).clock` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ disch_then drule
  \\ fs [dec_clock_def,ADD1]);

val evaluate_apps_Clos_long = prove(
  ``!ys ts s1 e1 env.
      LENGTH ts < s1.clock /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
        case evaluate ([e1],REVERSE (TAKE (1+LENGTH ts) (REVERSE ys)) ++ env,
                dec_clock (1+LENGTH ts) s1) of
        | (Rval [v],s) =>
             evaluate_apps v (REVERSE (DROP (1+LENGTH ts) (REVERSE ys))) s
        | res => res``,
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC,evaluate_apps_def]
  \\ fs [evaluate_def,Once dest_closure_def,check_loc_def]
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  THEN1
   (fs [REVERSE_SNOC]
    \\ Cases_on `evaluate ([e1],x::env,dec_clock 1 s1)` \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `a` \\ fs []
    \\ Cases_on `t` \\ fs [])
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `LENGTH t < (dec_clock 1 s1).clock` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ disch_then kall_tac
  \\ fs [REVERSE_SNOC] \\ fs [ADD1]
  \\ fs [dec_clock_def,ADD1]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]);

val LIST_REL_MAP = prove(
  ``!xs. LIST_REL P xs (MAP f xs) <=> EVERY (\x. P x (f x)) xs``,
  Induct \\ fs []);

val LIST_REL_f_rel_IMP = prove(
  ``!fns funs1. LIST_REL (f_rel max_app) funs1 fns ==> !x. ~(MEM (0,x) fns)``,
  Induct \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac
  \\ res_tac \\ fs []
  \\ Cases_on `x` \\ Cases_on `h` \\ fs [f_rel_def]);

val do_app_lemma = store_thm("do_app_lemma",
  ``state_rel s (t:'ffi closSem$state) /\ LIST_REL (v_rel max_app) xs ys ==>
    case do_app opp ys t of
    | Rerr err2 => (?err1. do_app opp xs s = Rerr err1 /\
                           exc_rel (v_rel max_app) err1 err2)
    | Rval (y,t1) => ?x s1. v_rel max_app x y /\ state_rel s1 t1 /\
                            do_app opp xs s = Rval (x,s1)``,
  cheat);

val evaluate_intro_multi = Q.store_thm("evaluate_intro_multi",
  `(!ys env2 (t1:'ffi closSem$state) env1 t2 s1 res2 xs.
     (evaluate (ys,env2,t1) = (res2,t2)) /\
     EVERY2 (v_rel s1.max_app) env1 env2 /\
     state_rel s1 t1 /\ code_rel s1.max_app xs ys ==>
     ?res1 s2.
        (evaluate (xs,env1,s1) = (res1,s2)) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1 res2 /\
        state_rel s2 t2) /\
   (!loc_opt f2 args2 (t1:'ffi closSem$state) res2 t2 f1 args1 s1.
     (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\ loc_opt = NONE /\
     v_rel s1.max_app f1 f2 /\ EVERY2 (v_rel s1.max_app) args1 args2 /\
     state_rel s1 t1 /\ LENGTH args1 <= s1.max_app ==>
     ?res1 s2.
       (evaluate_apps f1 args1 s1 = (res1,s2)) /\
       result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1 res2 /\
       state_rel s2 t2)`,
  HO_MATCH_MP_TAC (evaluate_ind |> Q.SPEC `λ(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac
  \\ TRY (drule code_rel_IMP_LENGTH \\ strip_tac)
  THEN1 (* NIL *)
   (fs [evaluate_def] \\ rveq \\ fs [])
  THEN1 (* CONS *)
   (rename1 `_ = LENGTH zs`
    \\ Cases_on `zs` THEN1 fs [LENGTH]
    \\ Cases_on `t` THEN1 fs [LENGTH]
    \\ fs [evaluate_def,closSemTheory.case_eq_thms,pair_case_eq]
    \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs [code_rel_CONS_CONS]
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ `s1.max_app = s2'.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs [])
  THEN1 (* Var *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs []
    \\ fs [evaluate_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  THEN1 (* If *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs []
    \\ reverse (fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq)
    \\ fs [HD_intro_multi]
    THEN1
     (first_x_assum drule \\ fs []
      \\ disch_then (qspec_then `[e]` mp_tac) \\ fs []
      \\ strip_tac \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ disch_then (qspec_then `[e]` mp_tac) \\ fs []
    \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs []
    \\ rveq \\ fs []
    \\ `(Boolv T = y <=> Boolv T = r1) /\
        (Boolv F = y <=> Boolv F = r1)` by
     (fs [EVAL ``closSem$Boolv T``,EVAL ``closSem$Boolv F``]
      \\ qpat_x_assum `v_rel _ _ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ rw [] \\ eq_tac \\ rw []
      \\ rpt (pop_assum mp_tac)
      \\ simp [Once v_rel_cases])
    \\ ntac 2 (pop_assum (fn th => fs [th]))
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ `s1.max_app = s2.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs[])
  THEN1 (* Let *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [evaluate_def,HD_intro_multi]
    \\ reverse (fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq)
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ fs []
    \\ disch_then (qspec_then `l` mp_tac) \\ fs []
    \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ `s1.max_app = s2.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ first_x_assum match_mp_tac
    \\ fs [] \\ metis_tac [EVERY2_APPEND])
  THEN1 (* Raise *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs []
    \\ fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq
    \\ fs [HD_intro_multi]
    \\ first_x_assum drule \\ fs []
    \\ disch_then (qspec_then `[e]` mp_tac) \\ fs []
    \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rw [])
  THEN1 (* Handle *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [evaluate_def,HD_intro_multi]
    \\ reverse (fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq)
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ fs []
    \\ disch_then (qspec_then `[e]` mp_tac) \\ fs []
    \\ strip_tac \\ fs [PULL_EXISTS]
    \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs[]
    \\ `s1.max_app = s2.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ first_x_assum match_mp_tac)
  THEN1 (* Op *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [evaluate_def,HD_intro_multi]
    \\ reverse (fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq)
    \\ first_x_assum drule
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[] \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ `LIST_REL (v_rel s1.max_app) (REVERSE a) (REVERSE vs)` by
           (match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ drule (GEN_ALL do_app_lemma)
    \\ disch_then drule
    \\ rename1 `do_app opp _ _ = _`
    \\ disch_then (qspec_then `opp` mp_tac) \\ fs []
    \\ rw [] \\ fs [])
  THEN1 (* Fn *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [] \\ rveq
    \\ `1 <= s1.max_app` by fs [state_rel_def]
    \\ fs [evaluate_def]
    \\ drule (GEN_ALL collect_args_IMP) \\ fs [] \\ strip_tac
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def] \\ fs []
    \\ rveq \\ fs []
    \\ once_rewrite_tac [v_rel_cases] \\ fs [code_rel_def]
    \\ rename1 `_ = (_,e2)` \\ qexists_tac `e2`
    \\ fs [HD_intro_multi]
    \\ drule collect_args_ok_IMP \\ fs [])
  THEN1 (* Letrec *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ reverse IF_CASES_TAC
    THEN1
     (fs [EXISTS_MEM] \\ rename1 `MEM eee l`
      \\ fs [EVERY_MEM] \\ res_tac
      \\ PairCases_on `eee` \\ fs []
      \\ fs [state_rel_def])
    \\ fs [AND_IMP_INTRO,PULL_FORALL]
    \\ first_x_assum match_mp_tac
    \\ conj_asm1_tac
    THEN1
     (fs [EVERY_MAP] \\ fs [EVERY_MEM,FORALL_PROD]
      \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ drule collect_args_IMP
      \\ res_tac \\ fs [] \\ rveq
      \\ fs [state_rel_def])
    \\ fs []
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs [LIST_REL_GENLIST]
    \\ rw [] \\ simp [Once v_rel_cases]
    \\ fs [LIST_REL_MAP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ drule collect_args_IMP
    \\ res_tac \\ fs [] \\ rveq \\ rw [f_rel_def]
    \\ drule collect_args_ok_IMP \\ fs []
    \\ strip_tac \\ fs [code_rel_def]
    \\ asm_exists_tac \\ fs []
    \\ qexists_tac `ts` \\ fs [])
  THEN1 (* App *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [intro_multi_length]
    \\ fs [DECIDE ``n > 0n <=> n <> 0``]
    \\ imp_res_tac collect_apps_acc \\ rveq
    \\ `?x. l = [x]` by (Cases_on `l` \\ fs [] \\ Cases_on `t`) \\ rveq \\ fs []
    \\ `syntax_ok other /\ syntax_ok (x::other) /\ syntax_ok [e']` by
     (drule collect_apps_syntax_ok \\ fs []
      \\ once_rewrite_tac [syntax_ok_cons] \\ fs [])
    \\ drule collect_apps_cons
    \\ impl_tac THEN1 fs [state_rel_def] \\ strip_tac
    \\ drule collect_apps_IMP_mk_Apps \\ fs []
    \\ strip_tac \\ rveq \\ fs [GSYM mk_Apps_def]
    \\ fs [evaluate_def]
    \\ fs [intro_multi_length]
    \\ fs [DECIDE ``n > 0n <=> n <> 0``]
    \\ reverse (fs [closSemTheory.case_eq_thms,pair_case_eq])
    \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ disch_then (qspec_then `x::other` mp_tac) \\ fs []
    \\ strip_tac \\ Cases_on `res1` \\ fs [] \\ rveq
    \\ rewrite_tac [GSYM ZIP]
    THEN1
     (drule (GEN_ALL mk_Apps_err_1)
      \\ disch_then (qspec_then `t::ts` mp_tac) \\ fs [])
    THEN1
     (rename1 `_ = (Rval vs, s3)`
      \\ first_x_assum (qspecl_then [`env1`,`s3`,`[e']`] mp_tac)
      \\ impl_tac THEN1 (imp_res_tac evaluate_const \\ fs [])
      \\ strip_tac \\ rveq
      \\ drule (GEN_ALL mk_Apps_err_2)
      \\ disch_then (qspec_then `t::ts` mp_tac) \\ fs []
      \\ disch_then drule
      \\ fs [] \\ imp_res_tac evaluate_const \\ fs [])
    \\ rename1 `_ = (Rval vs, s3)`
    \\ first_x_assum (qspecl_then [`env1`,`s3`,`[e']`] mp_tac)
    \\ impl_tac THEN1 (imp_res_tac evaluate_const \\ fs [])
    \\ strip_tac \\ rveq
    \\ Cases_on `res1` \\ fs []
    \\ drule evaluate_SING \\ strip_tac \\ rveq
    \\ drule (GEN_ALL evaluate_mk_Apps_ok)
    \\ disch_then drule
    \\ disch_then (qspec_then `t::ts` assume_tac) \\ rfs []
    \\ rveq \\ fs []
    \\ `s1.max_app = s2'.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ `s3.max_app = s2'.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [GSYM CONJ_ASSOC]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ impl_tac \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [intro_multi_length]
    \\ fs [state_rel_def])
  THEN1 (* Tick *)
   (`t1.clock = s1.clock` by fs [state_rel_def]
    \\ Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs []
    \\ fs [evaluate_def,case_eq_thms]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ `LIST_REL (v_rel (dec_clock 1 s1).max_app) env1 env2` by fs [dec_clock_def]
    \\ first_x_assum drule
    \\ fs [dec_clock_def]
    \\ disch_then (qspec_then `[e]` mp_tac)
    \\ fs [HD_intro_multi]
    \\ impl_tac \\ fs []
    \\ fs [state_rel_def])
  THEN1 (* Call *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [syntax_ok_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [])
  THEN1 (* app NIL *)
   (fs [evaluate_def,evaluate_apps_def] \\ rveq \\ fs [])
  (* app CONS *)
  \\ fs [evaluate_def] \\ rveq \\ fs []
  \\ fs [case_eq_thms] \\ fs [] \\ rveq
  THEN1 (* dest_closure returns NONE *)
   (`?y. dest_closure s1.max_app NONE f1 (x::xs) = NONE` by
     (fs [dest_closure_def,case_eq_thms]
      \\ qpat_x_assum `v_rel _ f1 f2` mp_tac
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      THEN1
       (strip_tac \\ fs [] \\ rveq \\ fs [check_loc_def]
        \\ imp_res_tac LIST_REL_LENGTH \\ fs [state_rel_def]
        \\ CCONTR_TAC \\ fs []
        \\ every_case_tac \\ fs [])
      THEN1
       (strip_tac \\ fs [] \\ rveq \\ fs [check_loc_def]
        \\ imp_res_tac LIST_REL_LENGTH \\ fs [state_rel_def]
        \\ CCONTR_TAC \\ fs []
        \\ every_case_tac \\ fs [])
      \\ Cases_on `EL i fns` \\ fs []
      \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) =
                              SOME (if b then x else y)``]
      \\ strip_tac \\ fs [] \\ rveq \\ fs [check_loc_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs [state_rel_def]
      \\ CCONTR_TAC \\ fs []
      \\ every_case_tac \\ fs []
      \\ Cases_on `EL i funs1` \\ fs []
      \\ imp_res_tac EL_MEM
      \\ imp_res_tac LIST_REL_f_rel_IMP \\ rfs [] \\ fs [])
    \\ `dest_closure s1.max_app NONE f1 [LAST (x::xs)] = NONE` by
     (pop_assum mp_tac
      \\ simp [dest_closure_def,case_eq_thms,UNCURRY] \\ rw []
      \\ qpat_x_assum `v_rel _ f1 f2` mp_tac
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ strip_tac \\ fs [] \\ rveq \\ fs [check_loc_def]
      \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) =
                              SOME (if b then x else y)``])
    \\ drule dest_closure_NONE_IMP_apps \\ fs [])
  THEN1 (* dest_closure returns Patrial_app *)
   (qpat_x_assum `v_rel _ f1 f2` mp_tac
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ drule dest_closure_SOME_IMP \\ strip_tac \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    THEN1
     (qpat_x_assum `_ = SOME (Partial_app _)` mp_tac
      \\ simp [Once dest_closure_def]
      \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs []
      \\ fs [dest_closure_def,check_loc_def,ADD1]
      \\ `s1.clock = t1.clock` by fs [state_rel_def] \\ fs []
      \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
      \\ `LENGTH xs < LENGTH ts` by fs []
      \\ Cases_on `t1.clock < LENGTH xs + 1` \\ fs [] \\ rveq \\ fs []
      THEN1
       (qexists_tac `s1 with clock := 0`
        \\ reverse conj_tac THEN1 fs [state_rel_def]
        \\ match_mp_tac (GEN_ALL evaluate_apps_Clos_timeout) \\ fs [])
      \\ fs [evaluate_apps_Clos_short,ADD1]
      \\ reverse conj_tac THEN1 fs [state_rel_def,ADD1,dec_clock_def]
      \\ simp [Once v_rel_cases]
      \\ qexists_tac `x::xs ++ args1`
      \\ qexists_tac `env1` \\ fs []
      \\ qexists_tac `e1` \\ fs []
      \\ qexists_tac `(DROP (LENGTH xs + 1) ts)` \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH
      \\ imp_res_tac LIST_REL_APPEND_EQ \\ fs [])
    THEN1
     (qpat_x_assum `_ = SOME (Partial_app _)` mp_tac
      \\ simp [Once dest_closure_def]
      \\ pairarg_tac \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs []
      \\ fs [dest_closure_def,check_loc_def,ADD1]
      \\ `s1.clock = t1.clock` by fs [state_rel_def] \\ fs []
      \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
      \\ rename1 `EL i fns = (num_args,e)`
      \\ `f_rel s1.max_app (EL i funs1) (EL i fns)` by fs [LIST_REL_EL_EQN]
      \\ `?y ys. x::xs = SNOC y ys` by metis_tac [NOT_CONS_NIL,SNOC_CASES]
      \\ simp [evaluate_apps_SNOC]
      \\ `LENGTH (x::xs) = LENGTH (SNOC y ys)` by asm_rewrite_tac []
      \\ fs [evaluate_def,dest_closure_def,check_loc_def]
      \\ Cases_on `EL i funs1` \\ fs [] \\ rfs [f_rel_def]
      \\ IF_CASES_TAC \\ fs[] \\ rveq
      THEN1 (fs [state_rel_def])
      \\ Cases_on `t1.clock < LENGTH ys + 1` \\ fs [] \\ rveq \\ fs []
      THEN1
       (qexists_tac `s1 with clock := 0`
        \\ reverse conj_tac THEN1 fs [state_rel_def]
        \\ `(dec_clock 1 s1).clock < LENGTH ys` by fs [dec_clock_def]
        \\ drule (GEN_ALL evaluate_apps_Clos_timeout)
        \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
        \\ `LENGTH ys <= LENGTH t` by fs []
        \\ disch_then drule
        \\ fs [dec_clock_def])
      \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
      \\ `1 ≤ (dec_clock 1 s1).max_app` by rfs [state_rel_def,dec_clock_def]
      \\ fs []
      \\ `LENGTH ys <= (dec_clock 1 s1).clock` by fs [dec_clock_def]
      \\ drule (GEN_ALL evaluate_apps_Clos_short) \\ fs []
      \\ `LENGTH ys <= LENGTH t` by fs []
      \\ disch_then drule \\ fs [] \\ disch_then kall_tac
      \\ reverse conj_tac THEN1 fs [state_rel_def,ADD1,dec_clock_def]
      \\ simp [Once v_rel_cases,ADD1]
      \\ qexists_tac `ys ++ [y]`
      \\ qexists_tac `env1` \\ fs []
      \\ qexists_tac `funs1` \\ fs []
      \\ qexists_tac `DROP (LENGTH ys) t` \\ fs []
      \\ qexists_tac `b1` \\ fs []
      \\ qpat_x_assum `x::xs = _` (fn th => simp [GSYM th])
      \\ fs [LIST_REL_GENLIST] \\ rw []
      \\ simp [Once v_rel_cases,ADD1])
    THEN1
     (qpat_x_assum `_ = SOME (Partial_app _)` mp_tac
      \\ simp [Once dest_closure_def]
      \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs []
      \\ fs [dest_closure_def,check_loc_def,ADD1]
      \\ `s1.clock = t1.clock` by fs [state_rel_def] \\ fs []
      \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
      \\ `LENGTH xs < LENGTH ts` by fs []
      \\ Cases_on `t1.clock < LENGTH xs + 1` \\ fs [] \\ rveq \\ fs []
      THEN1
       (qexists_tac `s1 with clock := 0`
        \\ reverse conj_tac THEN1 fs [state_rel_def]
        \\ match_mp_tac (GEN_ALL evaluate_apps_Clos_timeout) \\ fs [])
      \\ fs [evaluate_apps_Clos_short,ADD1]
      \\ reverse conj_tac THEN1 fs [state_rel_def,ADD1,dec_clock_def]
      \\ simp [Once v_rel_cases]
      \\ qexists_tac `x::xs ++ args1`
      \\ qexists_tac `env1` \\ fs []
      \\ qexists_tac `funs1` \\ fs []
      \\ qexists_tac `(DROP (LENGTH xs + 1) ts)` \\ fs []
      \\ qexists_tac `e1` \\ fs []
      \\ fs [LIST_REL_APPEND_EQ]))
  (* dest_closure returns Full_app *)
  \\ qpat_x_assum `v_rel _ f1 f2` mp_tac
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ drule dest_closure_SOME_IMP \\ strip_tac \\ fs []
  \\ strip_tac \\ fs [] \\ rveq
  \\ qpat_x_assum `_ = SOME _` mp_tac
  \\ simp [Once dest_closure_def]
  THEN1
   (Cases_on `t1.clock < SUC (LENGTH v69) − LENGTH rest_args` \\ fs []
    THEN1
     (IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [NOT_LESS]
      \\ qexists_tac `s1 with clock := 0`
      \\ reverse conj_tac THEN1 fs [state_rel_def]
      \\ match_mp_tac evaluate_apps_Clos_timeout_alt
      \\ fs [check_loc_def,state_rel_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs [ADD1])
    \\ simp [check_loc_def,ADD1]
    \\ qmatch_goalsub_abbrev_tac `Full_app e e5 e6`
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [NOT_LESS]
    \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
    \\ `LENGTH e6 = LENGTH xs - LENGTH ts` by simp [Abbr `e6`] \\ fs []
    \\ `LENGTH ts < s1.clock` by fs [state_rel_def]
    \\ `LENGTH ts < LENGTH (x::xs)` by fs []
    \\ drule evaluate_apps_Clos_long \\ simp []
    \\ disch_then drule \\ fs []
    \\ disch_then kall_tac \\ fs [ADD1]
    \\ qmatch_goalsub_abbrev_tac `([_],e7,_)`
    \\ Cases_on `evaluate ([e],e5,dec_clock (LENGTH ts + 1) t1)` \\ fs []
    \\ `LIST_REL (v_rel (dec_clock (LENGTH ts + 1) s1).max_app) e7 e5` by
     (unabbrev_all_tac
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_REVERSE
      \\ match_mp_tac EVERY2_TAKE
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ first_x_assum drule
    \\ disch_then (qspec_then `[e1]` mp_tac)
    \\ fs [EVAL ``(dec_clock n s).max_app``]
    \\ impl_tac THEN1 fs [state_rel_def,dec_clock_def]
    \\ strip_tac \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ Cases_on `a` \\ fs [] \\ rveq
    \\ Cases_on `t` \\ fs [] \\ rveq \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate_apps _ e8`
    \\ rename1 `v_rel s1.max_app f1 f2`
    \\ `v_rel s2.max_app f1 f2` by
        (imp_res_tac evaluate_const \\ fs [dec_clock_def])
    \\ first_x_assum drule
    \\ `LIST_REL (v_rel s2.max_app) e8 e6` by
     (unabbrev_all_tac
      \\ match_mp_tac EVERY2_REVERSE
      \\ match_mp_tac EVERY2_DROP
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ imp_res_tac evaluate_const \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs []
      \\ imp_res_tac evaluate_const \\ fs [dec_clock_def])
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_const
    \\ fs [dec_clock_def])
  THEN1
   (Cases_on `EL i fns` \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [NOT_LESS,ADD1]
    \\ `s1.clock = t1.clock` by fs [state_rel_def] \\ fs []
    \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
    \\ rename1 `EL i fns = (num_args,e)`
    \\ `f_rel s1.max_app (EL i funs1) (EL i fns)` by fs [LIST_REL_EL_EQN]
    \\ `?y ys. x::xs = SNOC y ys` by metis_tac [NOT_CONS_NIL,SNOC_CASES]
    \\ simp [evaluate_apps_SNOC]
    \\ `LENGTH (x::xs) = LENGTH (SNOC y ys)` by asm_rewrite_tac [] \\ fs []
    \\ rename1 `v_rel _ x v`
    \\ rename1 `LIST_REL (v_rel _) xs vs`
    \\ `?z zs. v::vs = SNOC z zs` by metis_tac [NOT_CONS_NIL,SNOC_CASES]
    \\ `LENGTH (v::vs) = LENGTH (SNOC z zs)` by asm_rewrite_tac [] \\ fs []
    \\ fs [evaluate_def,dest_closure_def,check_loc_def]
    \\ `v_rel s1.max_app y z /\
        LIST_REL (v_rel s1.max_app) ys zs` by
          (Cases_on `ys` \\ Cases_on `zs` \\ fs [])
    \\ Cases_on `EL i funs1` \\ fs [] \\ rfs [f_rel_def]
    \\ IF_CASES_TAC \\ fs[] \\ rveq
    THEN1 (fs [state_rel_def])
    \\ `1 <= (dec_clock 1 s1).max_app` by fs [dec_clock_def, state_rel_def]
    \\ Cases_on `t1.clock < LENGTH ts + 1` \\ fs [] \\ rveq \\ fs []
    THEN1
     (qexists_tac `s1 with clock := 0`
      \\ reverse conj_tac THEN1 fs [state_rel_def]
      \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
      \\ `(dec_clock 1 s1).clock <= LENGTH t` by fs [dec_clock_def]
      \\ drule (GEN_ALL evaluate_apps_Clos_timeout_alt)
      \\ fs [dec_clock_def])
    \\ `REVERSE vs ⧺ [v] = z::REVERSE zs` by
        metis_tac [REVERSE_SNOC,REVERSE,SNOC_APPEND] \\ fs []
    \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
    THEN1
     (Cases_on `evaluate ([e], z::
               (GENLIST (Recclosure NONE [] clo_env fns)
                  (LENGTH funs1) ⧺ clo_env),dec_clock 1 t1)`
      \\ fs [PULL_EXISTS]
      \\ helperLib.SEP_I_TAC "evaluate"
      \\ rfs [EVAL ``(dec_clock 1 s1).max_app``]
      \\ pop_assum mp_tac \\ impl_tac
      THEN1
       (reverse conj_tac THEN1 fs [state_rel_def,dec_clock_def]
        \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
        \\ fs [LIST_REL_GENLIST] \\ rw []
        \\ simp [Once v_rel_cases])
      \\ strip_tac \\ fs []
      \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
      \\ rename1 `state_rel s9 t9`
      \\ `s1.max_app = s9.max_app` by
               (imp_res_tac evaluate_const \\ fs [dec_clock_def])
      \\ fs [] \\ first_x_assum match_mp_tac \\ fs [])
    \\ simp [check_loc_def,ADD1]
    \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
    \\ `LENGTH t < (dec_clock 1 s1).clock` by fs [state_rel_def,dec_clock_def]
    \\ drule evaluate_apps_Clos_long \\ simp []
    \\ disch_then kall_tac \\ fs [ADD1]
    \\ qmatch_goalsub_abbrev_tac `([_],e7,_)`
    \\ qpat_x_assum `_ = (res2,t2)` mp_tac
    \\ qmatch_goalsub_abbrev_tac `([_],e8,_)`
    \\ Cases_on `evaluate ([e],e8,dec_clock (LENGTH t + 2) t1)` \\ fs []
    \\ `LIST_REL (v_rel (dec_clock (LENGTH t + 2) s1).max_app) e7 e8` by
     (unabbrev_all_tac \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ reverse conj_tac
      THEN1 (fs [LIST_REL_GENLIST] \\ simp [Once v_rel_cases])
      \\ match_mp_tac EVERY2_REVERSE
      \\ match_mp_tac EVERY2_TAKE
      \\ match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ first_x_assum drule
    \\ disch_then (qspec_then `[b1]` mp_tac)
    \\ fs [EVAL ``(dec_clock n s).max_app``]
    \\ impl_tac THEN1 fs [state_rel_def,dec_clock_def]
    \\ strip_tac \\ fs [] \\ strip_tac
    \\ fs [dec_clock_def] \\ rfs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ drule evaluate_SING \\ strip_tac \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `s1.max_app = s2.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ first_x_assum match_mp_tac \\ fs []
    \\ match_mp_tac EVERY2_REVERSE
    \\ match_mp_tac EVERY2_DROP
    \\ match_mp_tac EVERY2_REVERSE \\ fs [])
  THEN1
   (IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq \\ fs [NOT_LESS,ADD1]
    \\ `s1.clock = t1.clock` by fs [state_rel_def] \\ fs []
    \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
    \\ `f_rel s1.max_app (EL i funs1) (EL i fns)` by fs [LIST_REL_EL_EQN]
    \\ `1 <= s1.max_app` by fs [dec_clock_def, state_rel_def]
    \\ Cases_on `t1.clock < LENGTH ts + 1` \\ fs [] \\ rveq \\ fs []
    THEN1
     (qexists_tac `s1 with clock := 0`
      \\ reverse conj_tac THEN1 fs [state_rel_def]
      \\ `s1.clock <= LENGTH ts` by fs [dec_clock_def]
      \\ drule (GEN_ALL evaluate_apps_Clos_timeout_alt)
      \\ `LENGTH ts < LENGTH (x::xs)` by fs [dec_clock_def]
      \\ disch_then drule \\ fs [])
    \\ rename1 `v_rel _ x v`
    \\ rename1 `LIST_REL (v_rel _) xs vs`
    \\ qabbrev_tac `xxs = x::xs`
    \\ qabbrev_tac `vvs = v::vs`
    \\ `REVERSE vs ⧺ [v] = REVERSE vvs` by fs [Abbr`vvs`] \\ fs []
    \\ simp [check_loc_def,ADD1]
    \\ imp_res_tac (GSYM LIST_REL_LENGTH) \\ fs []
    \\ `LENGTH ts < s1.clock` by fs [state_rel_def,dec_clock_def]
    \\ `LENGTH ts < LENGTH xxs` by fs [Abbr `xxs`]
    \\ drule evaluate_apps_Clos_long \\ simp []
    \\ disch_then kall_tac \\ fs [ADD1]
    \\ qmatch_goalsub_abbrev_tac `([_],e7,_)`
    \\ qpat_x_assum `_ = (res2,t2)` mp_tac
    \\ qmatch_goalsub_abbrev_tac `([_],e8,_)`
    \\ Cases_on `evaluate ([e2],e8,dec_clock (LENGTH ts + 1) t1)` \\ fs []
    \\ `LIST_REL (v_rel (dec_clock (LENGTH ts + 1) s1).max_app) e7 e8` by
     (unabbrev_all_tac \\ fs [dec_clock_def]
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ match_mp_tac EVERY2_REVERSE
      \\ match_mp_tac EVERY2_TAKE
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
      \\ match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ first_x_assum drule
    \\ disch_then (qspec_then `[e1]` mp_tac)
    \\ fs [EVAL ``(dec_clock n s).max_app``]
    \\ impl_tac THEN1 fs [state_rel_def,dec_clock_def]
    \\ strip_tac \\ fs [] \\ strip_tac
    \\ fs [dec_clock_def] \\ rfs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ drule evaluate_SING \\ strip_tac \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `s1.max_app = s2.max_app` by (imp_res_tac evaluate_const \\ fs [])
    \\ fs [] \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [Abbr `xxs`,Abbr`vvs`]
    \\ match_mp_tac EVERY2_REVERSE
    \\ match_mp_tac EVERY2_DROP
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
    \\ match_mp_tac EVERY2_REVERSE \\ fs []));

val intro_multi_correct = store_thm("intro_multi_correct",
  ``!xs env1 s1 res1 s2 env2 t2 t1.
      evaluate (xs,env1,s1) = (res1,s2) /\ syntax_ok xs /\
      LIST_REL (v_rel s1.max_app) env1 env2 /\ state_rel s1 t1 ==>
      ?res2 t2.
        evaluate (intro_multi s1.max_app xs,env2,t1) = (res2,t2) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1
          res2 /\ state_rel s2 t2``,
  rpt gen_tac
  \\ Cases_on `evaluate (intro_multi s1.max_app xs,env2,t1)` \\ fs []
  \\ drule (CONJUNCT1 evaluate_intro_multi)
  \\ ntac 2 strip_tac \\ first_x_assum drule
  \\ fs [code_rel_def] \\ disch_then drule \\ fs []);




(*

(* TODO: move (also move the same in clos_removeProof if necessary) *)
val option_CASE_NONE_T = Q.store_thm(
  "option_CASE_NONE_T",
  `option_CASE x T f ⇔ x = NONE ∨ ∃y. x = SOME y ∧ f y`,
  Cases_on `x` >> simp[]);

val DISJ_CONG = Q.prove(
  `(~q ⇒ (p = p')) ⇒ (~p' ⇒ (q = q')) ⇒ (p ∨ q ⇔ p' ∨ q')`,
  DECIDE_TAC);

val nonnil_length = Q.prove(
  `v ≠ [] ⇒ LENGTH v ≠ 0`,
  Cases_on `v` >> simp[]);

val DROP_TAKE_APPEND_DROP = Q.store_thm(
  "DROP_TAKE_APPEND_DROP",
  `∀l n m. n ≤ m ⇒ DROP n (TAKE m l) ++ DROP m l = DROP n l`,
  Induct >> simp[] >> Cases_on`n`>>rw[]);

val EVERY_HD = Q.prove(
  `EVERY P l ∧ l ≠ [] ⇒ P (HD l)`,
  Cases_on `l` >> simp[]);

(* -- *)

val collect_args_correct = Q.prove (
`!max_app num_args e num_args' e' e'' t t'.
  collect_args max_app num_args e = (num_args', e') ∧
  exp_rel (:'ffi) max_app [e'] [e'']
  ⇒
  exp_rel (:'ffi) max_app [Fn t NONE NONE num_args e] [Fn t' NONE NONE num_args' e'']`,
 ho_match_mp_tac collect_args_ind >>
 srw_tac[][collect_args_def]
 >- metis_tac [fn_add_arg, exp_rel_trans, exp_rel_refl] >>
 metis_tac [compat]);

val collect_apps_correct = Q.prove (
`!max_app args e args' e' e''.
  collect_apps max_app args e = (args', e') ∧
  exp_rel (:'ffi) max_app [e'] [e''] ∧
  exp_rel (:'ffi) max_app args' args''
  ⇒
  exp_rel (:'ffi) max_app [App t NONE e args] [App t' NONE e'' args'']`,
 ho_match_mp_tac collect_apps_ind >>
 srw_tac[][collect_apps_def]
 >- (
   `exp_rel (:'ffi) max_app [App t NONE (App tra NONE e es) args] [App t NONE e (args++es)]`
   by (
     match_mp_tac app_combine >>
     simp [exp_rel_refl]) >>
   metis_tac [exp_rel_trans]) >>
 metis_tac [compat]);

val collect_args_max_app = Q.store_thm(
  "collect_args_max_app",
  `∀e e' n n'. n ≤ max_app ∧ collect_args max_app n e = (n', e') ⇒ n' ≤ max_app`,
  Induct >> simp[collect_args_def] >> rpt gen_tac >>
  rename1 `Fn t opt1 opt2 nn body` >>
  Cases_on `opt1` >> Cases_on `opt2` >>
  simp[collect_args_def] >> rw[] >> metis_tac[]);

val collect_args_never_decreases = Q.store_thm(
  "collect_args_never_decreases",
  `∀e e' n n'. collect_args max_app n e = (n', e') ⇒ n ≤ n'`,
  Induct >> simp[collect_args_def] >> rpt gen_tac >>
  rename1 `Fn t opt1 opt2 nn body` >>
  Cases_on `opt1` >> Cases_on `opt2` >>
  simp[collect_args_def] >> rw[] >> res_tac >> simp[]);

val check_loc_NONE_increases = Q.store_thm(
  "check_loc_NONE_increases",
  `check_loc max_app locopt NONE n m p ∧ n ≤ n' ⇒ check_loc max_app locopt NONE n' m p`,
  Cases_on `locopt` >> simp[closSemTheory.check_loc_def]);

val check_loc_second_NONE = Q.store_thm(
  "check_loc_second_NONE",
  `check_loc max_app locopt NONE nps nargs sofar ⇔ locopt = NONE ∧ nargs ≤ max_app`,
  Cases_on `locopt` >> simp[closSemTheory.check_loc_def]);

val dest_closure_Recclosure_EQ_NONE = Q.store_thm(
  "dest_closure_Recclosure_EQ_NONE",
  `dest_closure max_app locopt (Recclosure loc argE cloE fns i) args = NONE ⇔
     LENGTH fns ≤ i ∨ FST (EL i fns) ≤ LENGTH argE ∨
     ¬check_loc max_app locopt (lift ($+ (2*i)) loc) (FST (EL i fns))
         (LENGTH args) (LENGTH argE)`,
  simp[dest_closure_def, UNCURRY] >> rw[] >>
  Cases_on `LENGTH fns ≤ i` >> simp[] >>
  Cases_on `FST (EL i fns) ≤ LENGTH argE` >> simp[]);


(*

(* play with a concrete intro_multi example and their respective evaluations *)
val e1 = ``Letrec NONE NONE [(1, Fn NONE NONE 1 (Op (Const 3) []))] (Var 0)``
val intro_multi_e2 = EVAL ``intro_multi [^e1]``

val exp_rel = ASSUME ``exp_rel (:'ffi) [^e1] ^(rhs (concl intro_multi_e2))``

val result =
    exp_rel |> SIMP_RULE (srw_ss()) [exp_rel_def]
            |> Q.SPEC `i`
            |> Q.SPECL [`env`, `env`, `s`, `s`]
            |> SIMP_RULE (srw_ss()) [val_rel_refl, state_rel_refl]
            |> SIMP_RULE (srw_ss()) [exec_rel_rw, evaluate_ev_def]
            |> Q.SPEC `i`
            |> SIMP_RULE (srw_ss() ++ ARITH_ss)
                  [evaluate_def, LET_THM, closLangTheory.max_app_def]
            |> SIMP_RULE (srw_ss())
                 [res_rel_rw, state_rel_refl, val_rel_rw, is_closure_def,
                  check_closures_def, clo_can_apply_def,
                  clo_to_num_params_def, clo_to_partial_args_def,
                  rec_clo_ok_def, clo_to_loc_def, option_CASE_NONE_T]
            |> Q.SPECL [`j`, `[v1;v2]`, `[v1;v2]`, `s2`, `s2`]
            |> SIMP_RULE (srw_ss())
                 [val_rel_refl, state_rel_refl,
                  option_case_NONE_F, dest_closure_Recclosure_EQ_NONE,
                  check_loc_second_NONE, closLangTheory.max_app_def]
            |> SIMP_RULE (srw_ss()) [dest_closure_def, LET_THM,
                                     check_loc_second_NONE,
                                     closLangTheory.max_app_def,
                                     exec_rel_rw, evaluate_ev_def]
            |> UNDISCH_ALL
            |> Q.SPEC `0`
            |> SIMP_RULE (srw_ss()) [evaluate_def, closLangTheory.max_app_def,
                                     dest_closure_def, check_loc_second_NONE]
*)


(* IH is unhelpful here because of the way application to multiple arguments
   gets split across two evaluations in the evaluate_ev-Exp1 case:
     1. the body gets evaluated in an environment including the other
        recursive functions
     2. if the function now has more arguments, then these are available when
        the body is evaluated, and less are available when the evaluate_app
        gets called.
     3. The IH saying that the recclosure bodies are exp-related is not
        pertinent because the respective bodies are evaluated in environments
        of different lengths
*)
val dest_addarg_Fn_def = Define`
  (dest_addarg_Fn max_app n (Fn _ NONE NONE m body) =
     if n + m ≤ max_app (* ∧ 0 < m *) then SOME (m, body) else NONE) ∧
  (dest_addarg_Fn _ _ _ = NONE)
`;
val _ = augment_srw_ss [rewrites [dest_addarg_Fn_def]]

val dest_addarg_Fn_EQ_SOME = Q.store_thm(
  "dest_addarg_Fn_EQ_SOME",
  `dest_addarg_Fn max_app n e = SOME (m, body) ⇔
    ∃t. e = Fn t NONE NONE m body ∧ n + m ≤ max_app (* ∧ 0 < m *)`,
  Cases_on `e` >> simp[] >> rename1 `Fn t opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> simp[] >> metis_tac[ADD_COMM]);

val app_rw_closure = save_thm(
  "app_rw_closure",
  prove(
    mk_imp(``0n < numargs ∧ LENGTH (cargs:closSem$v list) < numargs``,
           concl evaluate_app_rw
                 |> strip_forall |> #2 |> rand
                 |> Term.subst [``f:closSem$v`` |->
                                  ``Closure NONE cargs clo numargs b``,
                                ``loc_opt : num option`` |->
                                   ``NONE : num option``]),
    Cases_on `args`
    >- simp[evaluate_def, dest_closure_def, check_loc_second_NONE,
            dec_clock_def] >>
    simp[evaluate_app_rw]))

val exp_rel_exec_rel_Exp1 = Q.store_thm(
  "exp_rel_exec_rel_Exp1",
  `state_rel i w s1 s2 ∧ LIST_REL (val_rel (:'a) i w) E1 E2 ∧
   LIST_REL (val_rel (:'a) i w) A1 A2 ∧
   exp_rel (:'a) w [e1] [e2] ⇒
   exec_rel i w (Exp1 NONE e1 E1 A1 n, (s1:'a closSem$state))
                (Exp1 NONE e2 E2 A2 n, s2)`,
  strip_tac >>
  simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `k` >> strip_tac >>
  reverse (rw[])
  >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n≤x``, val_rel_mono]) >>
  qpat_x_assum `exp_rel (:'a) _ _ _` mp_tac >> simp[exp_rel_thm] >>
  disch_then
    (qspecl_then [`i`, `E1`, `E2`, `s1`, `s2`, `k - (n - 1)`] mp_tac) >>
  simp[]>>
  simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
  >- (imp_res_tac evaluate_SING >> fs[] >>
      Cases_on `A1 = []`
      >- fs[evaluate_def, res_rel_rw] >>
      irule res_rel_evaluate_app >> simp[] >> imp_res_tac evaluate_clock >>
      fs[] >> irule val_rel_mono_list >> qexists_tac `i` >> simp[])
  >- simp[res_rel_rw])

val recClosure_add_arg0 = Q.prove(
  `LIST_REL (λ(n,e) (n',e').
               case dest_addarg_Fn max_app n e of
                   SOME(m,e0) => exp_rel (:'ffi) max_app [e0] [e'] ∧ n' = n + m
                 | NONE => n = n' ∧ exp_rel (:'ffi) max_app [e] [e'])
            fns1 fns2 ⇒
   ∀j i CE1 CE2 AE1 AE2.
     j ≤ i ∧
     LIST_REL (val_rel (:'ffi) i max_app) CE1 CE2 ∧
     LIST_REL (val_rel (:'ffi) i max_app) AE1 AE2
    ⇒
     LIST_REL (val_rel (:'ffi) j max_app)
        (GENLIST (Recclosure NONE AE1 CE1 fns1) (LENGTH fns1))
        (GENLIST (Recclosure NONE AE2 CE2 fns2) (LENGTH fns1)) ∧
     (∀pfx1 sfx1 vs2 fidx m fina1 fib01 fina2 fib2 t.
        fidx < LENGTH fns1 ∧ EL fidx fns1 = (fina1, Fn t NONE NONE m fib01) ∧
        fina1 + m ≤ max_app ∧ LENGTH pfx1 < m ∧
        EL fidx fns2 = (fina2, fib2) ∧
        LENGTH sfx1 + LENGTH AE1 = fina1 ∧
        LIST_REL (val_rel (:'ffi) i max_app) (pfx1 ++ sfx1) vs2 ⇒
        val_rel (:'ffi) j max_app
          (Closure NONE pfx1
                   (sfx1 ++ AE1 ++
                    GENLIST (Recclosure NONE [] CE1 fns1) (LENGTH fns1) ++
                    CE1)
                   m
                   fib01)
          (Recclosure NONE (vs2 ++ AE2) CE2 fns2 fidx))`,
  strip_tac >> completeInduct_on `j` >> rpt strip_tac
  >- (simp[LIST_REL_EL_EQN] >> qx_gen_tac `fidx` >> strip_tac >>
      `∃fina1 fib1 fina2 fib2.
          EL fidx fns1 = (fina1,fib1) ∧ EL fidx fns2 = (fina2,fib2)`
        by metis_tac[pair_CASES] >>
      `LENGTH fns2 = LENGTH fns1 ∧ LENGTH AE2 = LENGTH AE1 ∧
       LENGTH CE2 = LENGTH CE1` by fs[LIST_REL_EL_EQN] >>
      `fina1 ≤ fina2`
        by (qpat_x_assum `LIST_REL _ fns1 fns2` mp_tac >> simp[LIST_REL_EL_EQN] >>
            disch_then (qspec_then `fidx` mp_tac) >> simp[] >>
            `dest_addarg_Fn max_app fina1 fib1 = NONE ∨
                ∃m b. dest_addarg_Fn max_app fina1 fib1 = SOME(m,b)`
              by metis_tac[option_CASES, pair_CASES] >> simp[]) >>
      simp[val_rel_rw] >> conj_tac
      >- simp[check_closures_def, clo_can_apply_def] >>
      simp[dest_closure_def, revdroprev, revtakerev, check_loc_second_NONE] >>
      qx_genl_tac [`k`, `vs1`, `vs2`, `s1`, `s2`, `locopt`] >>
      Cases_on `locopt` >> simp[] >> strip_tac >>
      `LENGTH vs2 = LENGTH vs1` by fs[LIST_REL_EL_EQN] >>
      Cases_on `LENGTH vs1 ≤ s1.max_app` >> simp[] >>
      Cases_on `LENGTH AE1 < fina1` >> simp[] >>
      Cases_on `LENGTH AE1 + LENGTH vs1 < fina1` >> simp[]
      >- (imp_res_tac state_rel_max_app >>
          simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
          reverse (rw[]) >> simp[res_rel_rw]
          >- metis_tac[val_rel_mono, DECIDE ``0n ≤ x``] >>
          reverse conj_tac
          >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >>
              simp[]) >>
          first_x_assum (qspec_then `kk - (LENGTH vs1 - 1)` mp_tac) >> simp[] >>
          disch_then
            (qspecl_then [`k`, `CE1`, `CE2`, `vs1 ++ AE1`, `vs2 ++ AE2`]
                         mp_tac) >>
          simp[] >> impl_tac
          >- (conj_tac
              >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[]) >>
              irule EVERY2_APPEND_suff >> simp[] >> irule val_rel_mono_list >>
              qexists_tac `i` >> simp[]) >>
          simp[LIST_REL_EL_EQN]) >>
      Cases_on `LENGTH AE1 + LENGTH vs1 < fina2` >> simp[]
      >- ((* recursive closure 2 is still partially applied *)
          imp_res_tac state_rel_max_app >>
          simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
          reverse (Cases_on `fina1 ≤ kk + (LENGTH AE1 + 1)`) >> simp[]
          >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, DECIDE ``0n≤x``]) >>
          `fina1 < fina2` by simp[] >>
          qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
          `UNCURRY Rf (fina1,fib1) (fina2,fib2)`
            by metis_tac[LIST_REL_EL_EQN] >>
          pop_assum mp_tac >> simp[Abbr`Rf`, option_case_NONE_F] >>
          simp[dest_addarg_Fn_EQ_SOME, FORALL_PROD, PULL_EXISTS] >>
          rpt strip_tac >> rename1 `fina2 = fina1 + m` >>
          rename1 `exp_rel (:'ffi) _ [fib01] [fib2]` >>
          simp[evaluate_def] >> reverse (Cases_on `LENGTH vs1 ≤ kk + 1`) >>
          simp[]
          >- (simp[evaluate_app_rw, TAKE_EQ_NIL, dest_closure_def,
                   check_loc_second_NONE] >>
              simp[res_rel_rw] >> metis_tac[val_rel_mono, DECIDE ``0n≤x``]) >>
          simp[app_rw_closure, dest_closure_def, check_loc_second_NONE,
               dec_clock_def] >>
          simp[res_rel_rw] >> reverse conj_tac
          >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >>
              simp[]) >>
          `0 < LENGTH vs1` by (Cases_on `vs1` >> fs[]) >>
          first_x_assum (qspec_then `kk + 1 - LENGTH vs1` mp_tac) >> simp[] >>
          disch_then (qspecl_then [`k`, `CE1`, `CE2`, `AE1`, `AE2`] mp_tac) >>
          simp[] >> impl_tac
          >- (`k ≤ i` by decide_tac >> metis_tac [val_rel_mono_list]) >>
          disch_then (irule o CONJUNCT2) >> simp[TAKE_DROP]) >>
      imp_res_tac state_rel_max_app >>
      simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
      reverse (Cases_on `fina1 ≤ kk + (LENGTH AE1 + 1)`) >> simp[]
      >- (simp[res_rel_rw] >> metis_tac[DECIDE``0n≤x``,val_rel_mono]) >>
      Cases_on `fina2 = fina1`
      >- (rveq >> simp[] >>
          qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
          `UNCURRY Rf (fina1,fib1) (fina1,fib2)`
            by metis_tac[LIST_REL_EL_EQN] >>
          pop_assum mp_tac >> simp[Abbr`Rf`] >>
          `dest_addarg_Fn s1.max_app fina1 fib1 = NONE ∨
             ∃m fib0. dest_addarg_Fn s1.max_app fina1 fib1 = SOME(m,fib0)`
            by metis_tac[pair_CASES,option_CASES]
          >- (simp[] >> simp[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
              disch_then
               (qspecl_then [`k`,
                             `DROP (LENGTH AE1 + LENGTH vs1 - fina1) vs1 ++
                              AE1 ++
                              GENLIST (Recclosure NONE [] CE1 fns1)
                                      (LENGTH fns1) ++
                              CE1`,
                             `DROP (LENGTH AE1 + LENGTH vs1 - fina1) vs2 ++
                              AE2 ++
                              GENLIST (Recclosure NONE [] CE2 fns2)
                                      (LENGTH fns1) ++
                              CE2`, `s1`, `s2`] mp_tac) >>
              simp[] >> impl_tac
              >- (rpt (irule EVERY2_APPEND_suff)
                  >- (irule EVERY2_DROP >> simp[])
                  >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list])
                  >- (fs[PULL_FORALL, IMP_CONJ_THM] >> fs[FORALL_AND_THM] >>
                      first_x_assum irule >> simp[] >> qexists_tac `i` >>
                      simp[])
                  >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list])) >>
              disch_then (qspec_then `kk + (LENGTH AE1 + 1) - fina1` mp_tac) >>
              simp[] >> simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >>
              simp[]
              >- (imp_res_tac evaluate_SING >> fs[] >>
                  qmatch_abbrev_tac `res_rel _ (evaluate_app _ _ args1 _) _` >>
                  Cases_on `args1 = []`
                  >- (fs[Abbr`args1`, TAKE_EQ_NIL]
                      >- (`fina1 = LENGTH AE1 + LENGTH vs1` by simp[] >> fs[] >>
                          simp[res_rel_rw]) >>
                      fs[]) >>
                  fs[Abbr`args1`, TAKE_EQ_NIL] >> rw[] >>
                  irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
                  irule EVERY2_TAKE >> irule val_rel_mono_list >>
                  qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >>
                  fs[])
              >- simp[res_rel_rw]) >>
          simp[] >> fs[dest_addarg_Fn_EQ_SOME] >>
          strip_tac >> `m = 0` by simp[] >> rveq >> fs[] >>
          simp[evaluate_def]) >>
      `fina1 < fina2` by simp[] >>
      qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
      `UNCURRY Rf (fina1,fib1) (fina2,fib2)`
        by metis_tac[LIST_REL_EL_EQN] >>
      pop_assum mp_tac >> simp[Abbr`Rf`, option_case_NONE_F] >>
      simp[dest_addarg_Fn_EQ_SOME, FORALL_PROD, PULL_EXISTS] >>
      rpt strip_tac >> rename1 `fina2 = fina1 + m` >>
      rename1 `fib1 = Fn t NONE NONE m fib01` >>
      simp[evaluate_def, evaluate_app_rw, TAKE_EQ_NIL, dest_closure_def,
           check_loc_second_NONE, revtakerev, revdroprev] >>
      Cases_on `kk + (LENGTH AE1 + 1) < fina1 + m` >> simp[]
      >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n≤x``,val_rel_mono]) >>
      simp[TAKE_TAKE, DROP_TAKE_APPEND_DROP] >>
      qpat_x_assum `exp_rel (:'ffi) _ _ _` mp_tac >>
      simp[exp_rel_thm, dec_clock_def] >>
      qabbrev_tac `N = LENGTH AE1 + LENGTH vs1 - (fina1 + m)` >>
      qabbrev_tac `
        Recs = λce fns. GENLIST (Recclosure NONE [] ce fns) (LENGTH fns1)` >>
      simp[] >>
      disch_then (qspecl_then [`k`, `DROP N vs1 ++ AE1 ++ Recs CE1 fns1 ++ CE1`,
                               `DROP N vs2 ++ AE2 ++ Recs CE2 fns2 ++ CE2`,
                               `s1`, `s2`,
                               `kk + (LENGTH AE1 + 1) - (fina1 + m)`]
                              mp_tac) >> simp[] >>
      impl_tac
      >- (rpt (irule EVERY2_APPEND_suff) >> simp[EVERY2_DROP]
          >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[])
          >- (simp[Abbr`Recs`] >> first_x_assum (qspec_then `k` mp_tac) >>
              simp[] >> disch_then (qspec_then `i` mp_tac) >> simp[])
          >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[])) >>
      simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
      >- (imp_res_tac evaluate_SING >> fs[] >>
          Cases_on `TAKE N vs1 = []` >> fs[TAKE_EQ_NIL]
          >- simp[res_rel_rw]
          >- fs[]
          >- (irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
              irule EVERY2_TAKE >> irule val_rel_mono_list >>
              qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >> fs[]))
      >- simp[res_rel_rw]) >>
  `LENGTH fns2 = LENGTH fns1 ∧ LENGTH CE2 = LENGTH CE1 ∧
   LENGTH AE2 = LENGTH AE1` by fs[LIST_REL_EL_EQN] >>
  simp[val_rel_rw, check_closures_def, clo_can_apply_def] >>
  `LENGTH vs2 = LENGTH pfx1 + LENGTH sfx1` by fs[LIST_REL_EL_EQN] >> simp[] >>
  `fina2 = fina1 + m ∧ exp_rel (:'ffi) max_app [fib01] [fib2]`
     by (qpat_x_assum `LIST_REL _ fns1 fns2` mp_tac >>
         simp[LIST_REL_EL_EQN] >>
         disch_then (qspec_then `fidx` mp_tac) >> simp[]) >> simp[] >>
  qx_genl_tac [`k`, `vv1`, `vv2`, `s1`, `s2`, `locopt`] >>
  Cases_on `locopt` >>
  simp[dest_closure_def, check_loc_second_NONE] >> strip_tac >>
  `LENGTH vv2 = LENGTH vv1` by fs[LIST_REL_EL_EQN] >>
  Cases_on `LENGTH vv1 ≤ s1.max_app` >>
  simp[revtakerev, revdroprev] >>
  Cases_on `LENGTH pfx1 + LENGTH vv1 < m` >> simp[]
  >- (imp_res_tac state_rel_max_app >>
      simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
      reverse (rw[res_rel_rw])
      >- metis_tac[val_rel_mono, DECIDE``0n≤x``]
      >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >> simp[]) >>
      simp[] >> first_x_assum (qspec_then `kk - (LENGTH vv1 - 1)` mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`k`, `CE1`, `CE2`, `AE1`, `AE2`] mp_tac) >>
      simp[] >> impl_tac
      >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list]) >>
      disch_then (irule o CONJUNCT2) >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >> irule EVERY2_APPEND_suff >> simp[] >>
      `k ≤ i` by simp[] >> metis_tac[val_rel_mono_list]) >>
  imp_res_tac state_rel_max_app >>
  simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
  rveq >> simp[] >> reverse (Cases_on `m ≤ kk + (LENGTH pfx1 + 1)`) >>
  simp[res_rel_rw] >- metis_tac[DECIDE ``0n≤x``, val_rel_mono] >>
  qpat_x_assum `exp_rel (:'ffi) _ _ _` mp_tac >>
  simp[exp_rel_thm, dec_clock_def] >>
  qabbrev_tac `N = LENGTH pfx1 + LENGTH vv1 - m` >>
  qabbrev_tac `
    Recs = λce fns. GENLIST (Recclosure NONE [] ce fns) (LENGTH fns1)` >>
  simp[] >>
  disch_then
    (qspecl_then [`k`,
                  `DROP N vv1 ++ pfx1 ++ sfx1 ++ AE1 ++ Recs CE1 fns1 ++ CE1`,
                  `DROP N vv2 ++ vs2 ++ AE2 ++ Recs CE2 fns2 ++ CE2`,
                  `s1`, `s2`,
                   `kk + (LENGTH pfx1 + 1) - m`]
                 mp_tac) >> simp[] >>
  impl_tac
  >- (`k ≤ i` by simp[] >> reverse (irule EVERY2_APPEND_suff)
      >- metis_tac[val_rel_mono_list] >>
      reverse (irule EVERY2_APPEND_suff)
      >- (simp[Abbr`Recs`] >> first_x_assum (qspec_then `k` mp_tac) >>
          simp[] >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
      reverse (irule EVERY2_APPEND_suff)
      >- metis_tac[val_rel_mono_list] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >> irule EVERY2_APPEND_suff >>
      simp[EVERY2_DROP] >> metis_tac[val_rel_mono_list]) >>
  simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
  >- (imp_res_tac evaluate_SING >> fs[] >>
      Cases_on `TAKE N vv1 = []` >> fs[TAKE_EQ_NIL]
      >- simp[res_rel_rw]
      >- fs[]
      >- (irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
          irule EVERY2_TAKE >> irule val_rel_mono_list >>
          qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >> fs[]))
  >- simp[res_rel_rw])

val recClosure_add_arg_lem = save_thm(
  "recClosure_add_arg_lem",
  recClosure_add_arg0 |> UNDISCH
                      |> SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]
                      |> CONJUNCT1 |> DISCH_ALL
                      |> SIMP_RULE bool_ss [PULL_FORALL, AND_IMP_INTRO])

val recClosure_add_arg = Q.store_thm(
  "recClosure_add_arg",
  `LIST_REL
       (λ(n,e) (n',e').
          case dest_addarg_Fn max_app n e of
            NONE => n = n' ∧ exp_rel (:'ffi) max_app [e] [e']
          | SOME (m,e0) => exp_rel (:'ffi) max_app [e0] [e'] ∧ n' = n + m) fns1
       fns2 ∧
   exp_rel (:'ffi) max_app [body1] [body2] ⇒
   exp_rel (:'ffi) max_app [Letrec t NONE NONE fns1 body1] [Letrec t' NONE NONE fns2 body2]`,
  strip_tac >> simp[exp_rel_thm, evaluate_def] >> rpt strip_tac >>
  reverse (Cases_on `EVERY (λ(n,e). n ≤ s.max_app ∧ n ≠ 0) fns1`) >> simp[] >>
  imp_res_tac state_rel_max_app >>
  `EVERY (λ(n,e). n ≤ max_app ∧ n ≠ 0) fns2`
    by (fs[EVERY_MEM, MEM_EL, LIST_REL_EL_EQN, FORALL_PROD, PULL_EXISTS] >>
        rfs[] >> rpt gen_tac >> strip_tac >>
        rename1 `(n2,b2) = EL fidx fns2` >>
        qpat_x_assum `(n2,b2) = _` (assume_tac o SYM) >>
        `∃n1 b1. EL fidx fns1 = (n1,b1)` by metis_tac[pair_CASES] >>
        `n1 ≠ 0 ∧ n1 ≤ max_app` by metis_tac[] >>
        last_x_assum (qspec_then `fidx` mp_tac) >> simp[] >>
        `dest_addarg_Fn max_app n1 b1 = NONE ∨
            ∃m1 b01. dest_addarg_Fn max_app n1 b1 = SOME(m1,b01)`
          by metis_tac[pair_CASES, option_CASES] >> simp[] >>
        fs[dest_addarg_Fn_EQ_SOME]) >>
  simp[] >> qpat_x_assum `exp_rel (:'ffi) _ _ _` mp_tac >>
  simp[exp_rel_thm] >> disch_then irule >> qexists_tac `i` >> simp[] >>
  irule EVERY2_APPEND_suff >> simp[] >>
  `LENGTH fns2 = LENGTH fns1` by (imp_res_tac LIST_REL_LENGTH >> simp[]) >>
  simp[] >> irule recClosure_add_arg_lem >> simp[] >> qexists_tac `i` >> simp[])

val mti_letrec1_def = Define`
  (mti_letrec1 max_app (m, Fn t NONE NONE n b) =
     if m + n ≤ max_app then (m + n, b)
     else (m, Fn t NONE NONE n b)) ∧
  (mti_letrec1 _ me = me)
`;
val _ = export_rewrites ["mti_letrec1_def"]

val mti_letrec1_size_decrease = Q.store_thm(
  "mti_letrec1_size_decrease",
  `∀m b n b'.
     mti_letrec1 max_app (m, b) = (n,b') ∧ (m ≠ n ∨ b' ≠ b) ⇒ exp_size b' < exp_size b`,
  Cases_on `b` >> simp[Cong DISJ_CONG] >>
  rename1 `Fn t opt1 opt2` >> Cases_on `opt1` >> Cases_on `opt2` >>
  dsimp[bool_case_eq]);

val mti_letrec1_size_LEQ = Q.store_thm(
  "mti_letrec1_size_LEQ",
  `exp_size (SND (mti_letrec1 max_app (n,b))) ≤ exp_size b`,
  Cases_on `b` >> simp[] >> rename1 `Fn t opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> simp[] >> rw[] >>
  simp[closLangTheory.exp_size_def]);

val mti_letrec1_unchangedE_unchangedN = Q.store_thm(
  "mti_letrec1_unchangedE_unchangedN",
  `mti_letrec1 max_app (n,b) = (m,b) ⇒ n = m`,
  Cases_on `b` >> simp[] >> rename1 `Fn t opt1 opt2` >>
  map_every Cases_on [`opt1`, `opt2`] >> simp[] >> rw[] >>
  pop_assum (mp_tac o AP_TERM ``closLang$exp_size``) >>
  simp[closLangTheory.exp_size_def]);

val mti_letrec_def = tDefine "mti_letrec" `
  mti_letrec max_app m b =
   let (n',b') = mti_letrec1 max_app (m, b)
   in
     if b = b' then (m,b) else mti_letrec max_app n' b'`
  (WF_REL_TAC `measure (exp_size o SND o SND)` >>
   metis_tac[SND, mti_letrec1_size_decrease])

val collect_args_mti_letrec = Q.store_thm(
  "collect_args_mti_letrec",
  `∀max_app n e. collect_args max_app n e = mti_letrec max_app n e`,
  ho_match_mp_tac collect_args_ind >> simp[collect_args_def] >> rpt conj_tac >>
  simp[Once mti_letrec_def] >> rpt strip_tac >> rw[] >> fs[]
  >- (simp[Once mti_letrec_def, SimpRHS] >> rw[] >>
      pop_assum (mp_tac o AP_TERM ``closLang$exp_size``) >>
      simp[closLangTheory.exp_size_def]) >>
  simp[Once mti_letrec_def]);

val mti_letrec1_correct = Q.store_thm(
  "mti_letrec1_correct",
  `exp_rel (:'ffi) max_app
    [Letrec t NONE NONE fns b]
    [Letrec t' NONE NONE (MAP (mti_letrec1 max_app) fns) b]`,
  irule recClosure_add_arg >> simp[exp_rel_refl] >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> qx_gen_tac `n` >> strip_tac >>
  Cases_on `EL n fns` >> simp[] >> rename1 `mti_letrec1 max_app (m, e)` >>
  Cases_on `e` >> simp[exp_rel_refl] >> rename1 `Fn t opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> rw[exp_rel_refl])

val exp_size_MAP_mti_letrec1 = Q.store_thm(
  "exp_size_MAP_mti_letrec1",
  `exp3_size (MAP SND (MAP (mti_letrec1 max_app) fns)) ≤ exp3_size (MAP SND fns)`,
  Induct_on `fns` >> simp[FORALL_PROD, closLangTheory.exp_size_def] >>
  qx_genl_tac [`n`, `b`] >> assume_tac mti_letrec1_size_LEQ >> simp[]);

val mti_letrec_row_def = tDefine "mti_letrec_row" `
  mti_letrec_row max_app fns =
    let fns' = MAP (mti_letrec1 max_app) fns
    in
      if fns' = fns then fns
      else mti_letrec_row max_app fns'`
  (WF_REL_TAC `measure (closLang$exp3_size o MAP SND o SND)` >>
   simp[LIST_EQ_REWRITE, PULL_EXISTS] >> csimp[EL_MAP] >> Induct >>
   simp[closLangTheory.exp_size_def] >> rpt gen_tac >> rename1 `i < SUC _` >>
   Cases_on `i` >> simp[] >> strip_tac
   >- (rename1 `mti_letrec1 _ me = me` >> Cases_on `me` >> simp[] >>
       rename1 `mti_letrec1 _ (n,e)` >>
       `∃n' e'. mti_letrec1 max_app (n,e) = (n',e')` by metis_tac[pair_CASES] >>
       `exp_size e' < exp_size e`
         by (fs[] >> metis_tac[mti_letrec1_size_decrease]) >> fs[] >>
       `exp3_size (MAP SND (MAP (mti_letrec1 max_app) fns)) ≤ exp3_size (MAP SND fns)`
         by metis_tac[exp_size_MAP_mti_letrec1] >>
       simp[]) >>
   rename1 `mti_letrec1 _ me` >> Cases_on `me` >>
   rename1 `mti_letrec1 _ (m,e)` >> simp[] >> res_tac >>
   `exp_size (SND (mti_letrec1 max_app (m,e))) ≤ exp_size e`
     by metis_tac[mti_letrec1_size_LEQ] >> simp[])

val mti_letrec_expanded = Q.store_thm(
  "mti_letrec_expanded",
  `UNCURRY (mti_letrec max_app) x = UNCURRY (mti_letrec max_app) (mti_letrec1 max_app x)`,
  Cases_on `x` >> simp[] >> simp[SimpLHS, Once mti_letrec_def] >>
  rename1 `mti_letrec1 _ (n,b)` >> Cases_on `mti_letrec1 max_app (n,b)` >> simp[] >>
  rw[] >> imp_res_tac mti_letrec1_unchangedE_unchangedN >> rw[] >>
  simp[Once mti_letrec_def]);

val mti_letrec_mti_letrec_row = Q.store_thm(
  "mti_letrec_mti_letrec_row",
  `∀max_app fns. MAP (UNCURRY (mti_letrec max_app)) fns = mti_letrec_row max_app fns`,
  ho_match_mp_tac (theorem "mti_letrec_row_ind") >> simp[] >> rpt strip_tac >>
  simp[Once mti_letrec_row_def] >> rw[] >> fs[]
  >- (fs[LIST_EQ_REWRITE, EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
      Cases_on `EL i fns` >> simp[Once mti_letrec_def] >>
      rename1 `mti_letrec1 max_app (m,b)` >>
      `mti_letrec1 max_app (m,b) = (m,b)` by metis_tac[] >> simp[]) >>
  first_x_assum (SUBST_ALL_TAC o SYM) >>
  simp[MAP_MAP_o] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> simp[Once mti_letrec_expanded, SimpLHS])

val mti_letrec_row_correct = Q.store_thm(
  "mti_letrec_row_correct",
  `∀max_app funs.
    exp_rel (:'ffi) max_app
      [Letrec t NONE NONE funs e]
      [Letrec t' NONE NONE (mti_letrec_row max_app funs) e]`,
  ho_match_mp_tac (theorem "mti_letrec_row_ind") >> simp[] >> rpt strip_tac >>
  simp[Once mti_letrec_row_def] >> rw[exp_rel_refl] >> fs[] >>
  metis_tac[mti_letrec1_correct, exp_rel_trans]);

val intro_multi_alternative_rhs = Q.store_thm(
  "intro_multi_alternative_rhs",
  `MAP (λ(n,e). let (n',e') = collect_args max_app n e
                in
                  (n', f e')) fns =
   MAP (I ## f) (mti_letrec_row max_app fns)`,
  simp[GSYM mti_letrec_mti_letrec_row, MAP_MAP_o, UNCURRY, o_DEF,
       PAIR_MAP] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM, FORALL_PROD, collect_args_mti_letrec]);

val UNCURRY_mti_letrec_UNCURRY_collect_args = Q.store_thm(
  "UNCURRY_mti_letrec_UNCURRY_collect_args",
  `UNCURRY (mti_letrec max_app) = UNCURRY (collect_args max_app)`,
  simp[FUN_EQ_THM, FORALL_PROD, collect_args_mti_letrec]);

val intro_multi_correct = Q.store_thm ("intro_multi_correct",
`!max_app es. exp_rel (:'ffi) max_app es (intro_multi max_app es)`,
 ho_match_mp_tac intro_multi_ind >>
 srw_tac[][intro_multi_def, compat_nil, compat_var]
 >- metis_tac [compat_cons, intro_multi_sing, HD]
 >- metis_tac [compat_if, intro_multi_sing, HD]
 >- metis_tac [compat_let, intro_multi_sing, HD]
 >- metis_tac [compat_raise, intro_multi_sing, HD]
 >- metis_tac [compat_handle, intro_multi_sing, HD]
 >- metis_tac [compat_tick, intro_multi_sing, HD]
 >- metis_tac [compat_call, intro_multi_sing, HD]
 >- metis_tac [collect_apps_correct, intro_multi_sing, HD]
 >- metis_tac [compat_app, intro_multi_sing, HD]
 >- metis_tac [collect_args_correct, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 (* Letrec with loc = NONE *)
 >- (simp[intro_multi_alternative_rhs] >>
     irule exp_rel_trans >>
     qexists_tac `[Letrec t NONE NONE (mti_letrec_row max_app funs) e]` >>
     reverse conj_tac
     >- (reverse (irule compat_letrec)
         >- metis_tac[HD, intro_multi_sing] >>
         simp[LIST_REL_EL_EQN, GSYM mti_letrec_mti_letrec_row, EL_MAP] >>
         simp[UNCURRY_mti_letrec_UNCURRY_collect_args] >> qx_gen_tac `i` >>
         strip_tac >>
         `∃n b. EL i funs = (n,b)` by metis_tac[pair_CASES] >> simp[] >>
         `∃n' b'. collect_args max_app n b = (n',b')` by metis_tac[pair_CASES] >>
         simp[] >> metis_tac[HD, intro_multi_sing, MEM_EL]) >>
    simp[mti_letrec_row_correct])
 >- (reverse (irule compat_letrec)
     >- metis_tac[intro_multi_sing, HD] >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >>
     rename1 `EL mm fns` >>
     Cases_on `EL mm fns` >> simp[exp_rel_refl])
 >- (reverse (irule compat_letrec)
     >- metis_tac[intro_multi_sing, HD] >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >>
     rename1 `EL mm fns` >> Cases_on `EL mm fns` >>
     simp[exp_rel_refl])
 >- metis_tac [compat_op, intro_multi_sing, HD]);

val compile_correct = Q.store_thm("compile_correct",
  `!do_mti es. exp_rel (:'ffi) max_app es (clos_mti$compile do_mti max_app es)`,
  Cases>>fs[clos_mtiTheory.compile_def]>>
  metis_tac[intro_multi_correct,exp_rel_refl])

val HD_intro_multi = Q.prove(
  `[HD (intro_multi max_app [e])] = intro_multi max_app [e]`,
  metis_tac[intro_multi_sing,HD])

val contains_App_SOME_collect_args = Q.store_thm("contains_App_SOME_collect_args",
  `∀m x y a b. collect_args m x y = (a,b) ⇒
    (contains_App_SOME m [y] ⇔ contains_App_SOME m [b])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def]);

val contains_App_SOME_collect_apps = Q.store_thm("contains_App_SOME_collect_apps",
  `∀max_app x y a b. collect_apps max_app x y = (a,b) ⇒
    (max_app < LENGTH x ∨ contains_App_SOME max_app x ∨ contains_App_SOME max_app [y] ⇔
     max_app < LENGTH a ∨ contains_App_SOME max_app a ∨ contains_App_SOME max_app [b])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`max_app < LENGTH x`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  Cases_on`max_app < LENGTH es`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >> srw_tac[][] >>
  rpt (pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] >>
  metis_tac[]);

val contains_App_SOME_intro_multi = Q.store_thm("contains_App_SOME_intro_multi[simp]",
  `∀max_app es. contains_App_SOME max_app (intro_multi max_app es) ⇔ contains_App_SOME max_app es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def,contains_App_SOME_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi] >>
  full_simp_tac(srw_ss())[contains_App_SOME_def,HD_intro_multi,intro_multi_length]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] )
  >- metis_tac[contains_App_SOME_collect_apps]
  >- metis_tac[contains_App_SOME_collect_args]
  >- (
    simp[MAP_MAP_o,UNCURRY,o_DEF] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    pop_assum kall_tac >>
    Induct_on`funs`>>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    REWRITE_TAC[HD_intro_multi] >>
    rpt(pop_assum mp_tac) >>
    ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    metis_tac[contains_App_SOME_collect_args,SND,PAIR]));

val contains_App_SOME_compile = Q.store_thm("contains_App_SOME_compile[simp]",
  `∀do_mti es. contains_App_SOME max_app (clos_mti$compile do_mti max_app es) ⇔ contains_App_SOME max_app es`,
  Cases>>fs[clos_mtiTheory.compile_def]);

val every_Fn_vs_NONE_collect_apps = Q.prove(
  `∀max_app es e x y. collect_apps max_app es e = (x,y) ⇒
  (every_Fn_vs_NONE x ∧ every_Fn_vs_NONE [y] ⇔
   every_Fn_vs_NONE es ∧ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >> full_simp_tac(srw_ss())[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[][] >> metis_tac[])

val every_Fn_vs_NONE_collect_args = Q.prove(
  `∀max_app es e x y. collect_args max_app es e = (x,y) ⇒
    (every_Fn_vs_NONE [y] ⇔ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >> full_simp_tac(srw_ss())[])

val every_Fn_vs_NONE_intro_multi = Q.store_thm("every_Fn_vs_NONE_intro_multi[simp]",
  `∀max_app es. every_Fn_vs_NONE (intro_multi max_app es) = every_Fn_vs_NONE es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >> srw_tac[][] )
  >- metis_tac[every_Fn_vs_NONE_collect_apps]
  >- metis_tac[every_Fn_vs_NONE_collect_args] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY] >>
  qmatch_abbrev_tac `_ ∧ P ⇔ _ ∧ P` >>
  Cases_on `P` >> simp[] >>
  ntac 2 (pop_assum kall_tac) >>
  Induct_on`funs`>>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  rpt(pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  metis_tac[every_Fn_vs_NONE_collect_args,SND,PAIR]);

val every_Fn_vs_NONE_compile = Q.store_thm("every_Fn_vs_NONE_compile[simp]",
  `∀do_mti es. every_Fn_vs_NONE (clos_mti$compile do_mti max_app es) = every_Fn_vs_NONE es`,
  Cases>>fs[clos_mtiTheory.compile_def]);

val intro_multi_EQ_NIL = Q.store_thm(
  "intro_multi_EQ_NIL[simp]",
  `∀max_app es. intro_multi max_app es = [] ⇔ es = []`,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind >>
  simp[clos_mtiTheory.intro_multi_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]))

val compile_EQ_NIL = Q.store_thm(
  "compile_EQ_NIL[simp]",
  `∀do_mti es. clos_mti$compile do_mti max_app es = [] ⇔ es = []`,
  Cases>>fs[clos_mtiTheory.compile_def])

val collect_apps_preserves_set_globals = Q.store_thm(
  "collect_apps_preserves_set_globals",
  `∀max_app es e es' e'.
     collect_apps max_app es e = (es',e') ⇒
     elist_globals es ⊎ set_globals e = elist_globals es' ⊎ set_globals e'`,
  ho_match_mp_tac clos_mtiTheory.collect_apps_ind >>
  simp[clos_mtiTheory.collect_apps_def, bool_case_eq] >> rpt strip_tac
  >- (pop_assum (assume_tac o SYM) >> fs[elist_globals_append] >>
      metis_tac[bagTheory.COMM_BAG_UNION, bagTheory.ASSOC_BAG_UNION])
  >- (rveq >> simp[]))

val collect_apps_preserves_esgc_free = Q.store_thm(
  "collect_apps_preserves_esgc_free",
  `∀max_app es e es' e'.
     collect_apps max_app es e = (es',e') ∧ EVERY esgc_free es ∧ esgc_free e ⇒
     EVERY esgc_free es' ∧ esgc_free e'`,
  ho_match_mp_tac clos_mtiTheory.collect_apps_ind >>
  simp[clos_mtiTheory.collect_apps_def, bool_case_eq] >> rw[] >>
  simp[] >> metis_tac[]);

val collect_args_preserves_set_globals = Q.store_thm(
  "collect_args_preserves_set_globals",
  `∀max_app n e n' e'. collect_args max_app n e = (n',e') ⇒ set_globals e' = set_globals e`,
  ho_match_mp_tac clos_mtiTheory.collect_args_ind >>
  simp[clos_mtiTheory.collect_args_def, bool_case_eq] >> dsimp[] >>
  rpt strip_tac >> pop_assum (assume_tac o SYM) >> fs[]);

val collect_args_preserves_esgc_free = Q.store_thm(
  "collect_args_preserves_esgc_free",
  `∀max_app n e n' e'. collect_args max_app n e = (n',e') ∧ esgc_free e ⇒ esgc_free e'`,
  ho_match_mp_tac clos_mtiTheory.collect_args_ind >>
  simp[clos_mtiTheory.collect_args_def, bool_case_eq] >> dsimp[] >>
  rpt strip_tac >> metis_tac[set_globals_empty_esgc_free]);

val intro1_pat = ``intro_multi max_app [e]``
fun intro_sing th =
  case gen_find_term
         (fn (bvs,t) => if can (match_term intro1_pat) t andalso
                           null (intersect bvs (free_vars t))
                        then SOME t
                        else NONE)
                     (concl th)
   of
      SOME t => strip_assume_tac
                  (PART_MATCH (lhs o #2 o dest_exists)
                              clos_mtiTheory.intro_multi_sing t)
    | NONE => NO_TAC

val intro_multi_preserves_elist_globals = Q.store_thm(
  "intro_multi_preserves_elist_globals",
  `∀max_app es. elist_globals (intro_multi max_app es) = elist_globals es`,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind >>
  simp[] >> rpt conj_tac >> simp[clos_mtiTheory.intro_multi_def] >>
  rpt strip_tac >> fs[] >>
  TRY (rpt (first_assum intro_sing >> fs[] >> pop_assum mp_tac) >> NO_TAC)
  >- (pairarg_tac >> fs[] >> first_assum intro_sing >> fs[] >>
      imp_res_tac collect_apps_preserves_set_globals >>
      metis_tac[bagTheory.COMM_BAG_UNION])
  >- (pairarg_tac >> fs[] >> first_assum intro_sing >> fs[] >>
      imp_res_tac collect_args_preserves_set_globals)
  >- (first_assum intro_sing >> fs[] >> simp[elist_globals_FOLDR] >>
      irule FOLDR_CONG >> simp[] >>
      simp[LIST_EQ_REWRITE] >> simp[EL_MAP] >> rpt strip_tac >>
      rpt (pairarg_tac >> fs[]) >>
      imp_res_tac collect_args_preserves_set_globals >>
      rename1 `HD (intro_multi max_app [e3])` >>
      `∃e3'. intro_multi max_app [e3] = [e3']`
        by metis_tac[clos_mtiTheory.intro_multi_sing] >> simp[] >>
      rename1`EL n fns = (nn,e2)` >> `MEM (nn,e2) fns` by metis_tac[MEM_EL] >>
      res_tac >> rfs[]))

val intro_multi_preserves_esgc_free = Q.store_thm(
  "intro_multi_preserves_esgc_free",
  `∀max_app es. EVERY esgc_free es ⇒ EVERY esgc_free (intro_multi max_app es)`,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind >>
  simp[] >> rpt conj_tac >> simp[clos_mtiTheory.intro_multi_def] >>
  rpt strip_tac >> fs[] >> simp[EVERY_HD]
  >- (pairarg_tac >> fs[] >>
      imp_res_tac collect_apps_preserves_esgc_free >> fs[EVERY_HD])
  >- (pairarg_tac >> fs[] >> imp_res_tac collect_args_preserves_set_globals >>
      rename1`HD (intro_multi max_app [e1])` >>
      `elist_globals [e1] = {||}` by simp[] >>
      `elist_globals (intro_multi max_app [e1]) = {||}`
         by metis_tac[intro_multi_preserves_elist_globals] >>
      first_assum intro_sing >> fs[])
  >- (first_assum intro_sing >> fs[] >> rename1`intro_multi max_app [e0]` >>
      qspecl_then [`max_app`,`[e0]`] mp_tac intro_multi_preserves_elist_globals >>
      simp[])
  >- (first_assum intro_sing >> fs[] >> rename1`intro_multi max_app [e0]` >>
      qspecl_then [`max_app`,`[e0]`] mp_tac intro_multi_preserves_elist_globals >>
      simp[])
  >- (rpt (pairarg_tac >> fs[]) >> fs[elist_globals_FOLDR] >>
      qpat_x_assum `FOLDR _ _ _ = {||}`
        (fn th => CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) >>
      irule FOLDR_CONG >> simp[] >> simp[LIST_EQ_REWRITE] >>
      rpt strip_tac >> simp[EL_MAP] >> rpt (pairarg_tac >> fs[]) >>
      rename1`HD (intro_multi max_app [e2])` >>
      `∃e2'. intro_multi max_app [e2] = [e2']`
        by metis_tac[clos_mtiTheory.intro_multi_sing] >>
      simp[] >>
      `elist_globals [e2'] = elist_globals [e2]`
        by metis_tac[intro_multi_preserves_elist_globals] >>
      fs[] >> metis_tac[collect_args_preserves_set_globals]))

val compile_preserves_elist_globals = Q.store_thm(
  "compile_preserves_elist_globals",
  `∀do_mti es. elist_globals (clos_mti$compile do_mti max_app es) = elist_globals es`,
  Cases>>fs[clos_mtiTheory.compile_def,intro_multi_preserves_elist_globals])

val compile_preserves_esgc_free = Q.store_thm(
  "compile_preserves_esgc_free",
  `∀do_mti es. EVERY esgc_free es ⇒ EVERY esgc_free (clos_mti$compile do_mti max_app es)`,
  Cases>>fs[clos_mtiTheory.compile_def,intro_multi_preserves_esgc_free])

*)

val _ = export_theory();
