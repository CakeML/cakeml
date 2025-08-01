(*
  Correctness proof for the clos_mti compiler pass. The theorem is
  proved using a backwards simulation, i.e. against the direction of
  compilation.
*)
open preamble backendPropsTheory closPropsTheory
clos_mtiTheory closSemTheory helperLib;

val _ = new_theory "clos_mtiProof";
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

fun bring_fwd_ctors th ty = map ((fn s=> Parse.bring_to_front_overload s {Name = s,Thy = th}) o term_to_string) (TypeBase.constructors_of ty)

val _ = bring_fwd_ctors "closLang" ``:closLang$exp``

(* code relation *)

Theorem no_mti_def = closPropsTheory.no_mti_def
    |> CONV_RULE (DEPTH_CONV ETA_CONV)

Definition code_rel_def:
  code_rel max_app e1 e2 <=>
    EVERY no_mti e1 /\ (e2 = intro_multi max_app e1)
End

Theorem code_rel_IMP_LENGTH:
   code_rel max_app xs ys ==> LENGTH ys = LENGTH xs
Proof
  rw [code_rel_def,clos_mtiTheory.intro_multi_length]
QED

Theorem HD_intro_multi[simp]:
   [HD (intro_multi max_app [e2])] = intro_multi max_app [e2]
Proof
  `?x. intro_multi max_app [e2] = [x]` by metis_tac [intro_multi_sing]
  \\ fs []
QED

Theorem intro_multi_cons:
   !xs x. intro_multi m (x::xs) = HD (intro_multi m [x]) :: intro_multi m xs
Proof
  Induct \\ fs[intro_multi_def]
QED

Theorem code_rel_CONS_CONS:
   code_rel m (x1::x2::xs) (y1::y2::ys) <=>
    code_rel m [x1] [y1] /\ code_rel m (x2::xs) (y2::ys)
Proof
  fs [code_rel_def,intro_multi_def]
  \\ `?t1. intro_multi m [x1] = [t1]` by metis_tac [intro_multi_sing]
  \\ `?t2. intro_multi m [x2] = [t2]` by metis_tac [intro_multi_sing]
  \\ fs [] \\ eq_tac \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [intro_multi_cons] \\ fs []
QED

(* value relation *)

Definition mk_Fns_def:
  mk_Fns [] e = e /\
  mk_Fns (t::ts) e = Fn t NONE NONE 1 (mk_Fns ts e)
End

Definition f_rel_def:
  f_rel max_app (a1,e1) (a2,e2) <=>
    ?b1 ts.
      code_rel max_app [b1] [e2] /\ a2 <= max_app /\ no_mti b1 /\
      a1 = 1n /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1
End

Inductive v_rel:
  (!i. v_rel (max_app:num) (Number i) (closSem$Number i)) /\
  (!w. v_rel max_app (Word64 w) (Word64 w)) /\
  (!w. v_rel max_app (ByteVector w) (ByteVector w)) /\
  (!n b. v_rel max_app (RefPtr b n) (RefPtr b n)) /\
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
       (Recclosure NONE args2 env2 funs2 n))
End

Definition v_rel_opt_def:
  (v_rel_opt max_app NONE NONE <=> T) /\
  (v_rel_opt max_app (SOME x) (SOME y) <=> v_rel max_app x y) /\
  (v_rel_opt max_app _ _ = F)
End

Inductive ref_rel:
  (!bs. ref_rel max_app (ByteArray bs) (ByteArray bs)) /\
  (!xs ys.
    LIST_REL (v_rel max_app) xs ys ==>
    ref_rel max_app (ValueArray xs) (ValueArray ys))
End

Definition FMAP_REL_def:
  FMAP_REL r f1 f2 <=>
    FDOM f1 = FDOM f2 /\
    !k v. FLOOKUP f1 k = SOME v ==>
          ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2
End

(* state relation *)

Theorem SND_compile_inc[simp]:
   SND (clos_mti$compile_inc max_app p) = []
Proof
  Cases_on`p` \\ EVAL_TAC
QED

Definition state_rel_def:
  state_rel (s:('c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = [] /\
         EVERY no_mti (FST (SND (s.compile_oracle n)))) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    t.max_app = s.max_app /\ 1 <= s.max_app /\
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL (v_rel_opt s.max_app) s.globals t.globals /\
    FMAP_REL (ref_rel s.max_app) s.refs t.refs /\
    s.compile = pure_cc (clos_mti$compile_inc s.max_app) t.compile /\
    t.compile_oracle = pure_co (clos_mti$compile_inc s.max_app) o s.compile_oracle
End

(* evaluation theorem *)

Theorem collect_args_IMP:
   !max_app k e1 num_args e2.
      collect_args max_app k e1 = (num_args,e2) /\ k <= max_app ==>
      k <= num_args /\ num_args <= max_app
Proof
  recInduct collect_args_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ fs [collect_args_def]
  \\ rw [] \\ fs []
QED

Theorem collect_args_ok_IMP:
   !max_app k e num_args e2.
      collect_args max_app k e = (num_args,e2) /\ no_mti e ==>
      ?ts. e = mk_Fns ts e2 ∧ num_args = k + LENGTH ts /\ no_mti e2
Proof
  recInduct collect_args_ind
  \\ rw [] \\ fs []
  \\ fs [collect_args_def] \\ rveq
  \\ TRY (fs [collect_args_def] \\ rveq
          \\ qexists_tac `[]` \\ fs [mk_Fns_def] \\ NO_TAC)
  \\ NORM_TAC (srw_ss()) []
  \\ gvs [no_mti_def,mk_Fns_def]
  \\ qexists_tac `t::ts` \\ rw [mk_Fns_def]
QED

Theorem dest_closure_SOME_IMP:
   dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)
Proof
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []
QED

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

Definition mk_Apps_def:
  mk_Apps e [] = e /\
  mk_Apps e ((t,other)::ts) = App t NONE (mk_Apps e ts) [other]
End

Theorem collect_apps_IMP_mk_Apps:
  !e max_app (acc:closLang$exp list) other e3.
      collect_apps max_app [] e = (other,e3) /\ no_mti e ==>
      ?ts. e = mk_Apps e3 (ZIP (ts, other)) /\ LENGTH other = LENGTH ts /\
           LENGTH other <= max_app
Proof
  Induct \\ fs [] \\ rw []
  \\ fs [collect_apps_def] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def]
          \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [no_mti_def] \\ rveq
  \\ fs [collect_apps_def] \\ rveq
  \\ FULL_CASE_TAC \\ fs [] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [no_mti_def]
  \\ imp_res_tac collect_apps_acc \\ rveq \\ fs []
  \\ Cases_on ‘l’ \\ gvs []
  \\ drule (GEN_ALL collect_apps_cons) \\ fs []
  \\ strip_tac \\ first_x_assum drule
  \\ strip_tac \\ rveq \\ fs []
  \\ qexists_tac `t::ts` \\ fs [ZIP,mk_Apps_def]
QED

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

Theorem collect_apps_no_mti:
   !k aux e res e1.
      collect_apps k aux e = (res,e1) /\
      no_mti e /\ EVERY no_mti aux ==>
      EVERY no_mti res /\ no_mti e1
Proof
  recInduct collect_apps_ind
  \\ rw [collect_apps_def] \\ fs []
  \\ fs [no_mti_def, ETA_THM]
QED

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

Definition evaluate_apps_def:
  evaluate_apps f [] s = (Rval [f], s) /\
  evaluate_apps f (x::xs) s =
    case evaluate_apps f xs s of
    | (Rval [v], s1) => evaluate_app NONE v [x] s1
    | res => res
End

Triviality evaluate_mk_Apps_ok:
  !other ts env1 s1 vs.
      evaluate ([e],env1,s3) = (Rval [f],s2') /\
      evaluate (other,env1,s1) = (Rval vs,s3) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e (ZIP (ts,other))],env1,s1) =
      evaluate_apps f vs s2'
Proof
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
  \\ rveq \\ fs []
QED

Triviality dest_closure_NONE_IMP_apps:
  !xs f1 s1.
      dest_closure s1.max_app NONE f1 [LAST xs] = NONE /\ xs <> [] ==>
      evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)
Proof
  Induct \\ fs [evaluate_apps_def]
  \\ Cases_on `xs` \\ fs [evaluate_apps_def]
  \\ fs [evaluate_apps_def,evaluate_def]
QED

Triviality evaluate_apps_SNOC:
  !xs x f s.
      evaluate_apps f (SNOC x xs) s =
      case evaluate_app NONE f [x] s of
      | (Rval [v], s) => evaluate_apps v xs s
      | res => res
Proof
  Induct
  THEN1 (fs [evaluate_apps_def] \\ rw []
         \\ every_case_tac \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ fs [evaluate_apps_def] \\ rw []
  \\ Cases_on `evaluate_app NONE f [x] s` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []
QED

Triviality evaluate_apps_Clos_timeout:
  !ys ts s1 e1 env.
      s1.clock < LENGTH ys /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock < LENGTH l` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]
QED

Triviality evaluate_apps_Clos_timeout_alt:
  !ys ts s1 e1 env.
      s1.clock <= LENGTH ts /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_SNOC]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock <= LENGTH t` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]
QED

Triviality evaluate_apps_Clos_short:
  !ys ts s1 e1 env.
      LENGTH ys <= s1.clock /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
         (Rval [Closure NONE [] (ys ++ env) 1
                   (mk_Fns (DROP (LENGTH ys) ts) e1)],
          dec_clock (LENGTH ys) s1)
Proof
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
  \\ fs [dec_clock_def,ADD1]
QED

Triviality evaluate_apps_Clos_long:
  !ys ts s1 e1 env.
      LENGTH ts < s1.clock /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
        case evaluate ([e1],REVERSE (TAKE (1+LENGTH ts) (REVERSE ys)) ++ env,
                dec_clock (1+LENGTH ts) s1) of
        | (Rval [v],s) =>
             evaluate_apps v (REVERSE (DROP (1+LENGTH ts) (REVERSE ys))) s
        | res => res
Proof
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
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

Triviality LIST_REL_f_rel_IMP:
  !fns funs1. LIST_REL (f_rel max_app) funs1 fns ==> !x. ~(MEM (0,x) fns)
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac
  \\ res_tac \\ fs []
  \\ Cases_on `x` \\ Cases_on `h` \\ fs [f_rel_def]
QED

Theorem v_rel_simps[simp] =
  LIST_CONJ ([
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (Number n)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (Block n p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (Word64 p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (ByteVector p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (RefPtr b p)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (Closure x1 x2 x3 x4 x5)``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel max_app x (Recclosure y1 y2 y3 y4 y5)``,
  prove(``v_rel max_app x (Boolv b) <=> x = Boolv b``,
        Cases_on `b` \\ fs [Boolv_def,Once v_rel_cases]),
  prove(``v_rel max_app x Unit <=> x = Unit``,
        fs [closSemTheory.Unit_def,Once v_rel_cases])]
  |> map GEN_ALL)

val v_rel_opt_thm = prove(
  ``v_rel_opt m = OPTREL (v_rel m)``,
  fs [FUN_EQ_THM] \\ Cases  \\ Cases \\ fs [OPTREL_def,v_rel_opt_def]);

Theorem simple_val_rel:
  simple_val_rel (v_rel max_app_n)
Proof
  fs [simple_val_rel_def] \\ rpt strip_tac \\ fs []
QED

Theorem simple_state_rel:
   simple_state_rel (v_rel max_app_n)
     (\s t. s.max_app = max_app_n ∧ state_rel s t)
Proof
  fs [simple_state_rel_def,state_rel_def] \\ rw []
  \\ fs [FMAP_REL_def,FLOOKUP_DEF] \\ rfs []
  \\ res_tac \\ fs [v_rel_opt_thm]
  THEN1
   (Cases_on `s.refs ' ptr` \\ fs []
    \\ Cases_on `t.refs ' ptr` \\ fs [ref_rel_cases]
    \\ fs [] \\ rveq \\ fs [])
  THEN1
   (Cases_on `s'.refs ' ptr` \\ fs []
    \\ Cases_on `t.refs ' ptr` \\ fs [ref_rel_cases]
    \\ fs [] \\ rveq \\ fs [])
  THEN
   (rpt gen_tac \\ Cases_on `k = p` \\ fs []
    THEN1 (fs [ref_rel_cases])
    \\ fs [FAPPLY_FUPDATE_THM])
QED

val do_app_inst =
  simple_val_rel_do_app_rev
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> INST_TYPE [``:'a``|->``:'c``]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`]
  |> SIMP_RULE std_ss [simple_val_rel, simple_state_rel]

Theorem do_app_lemma:
  state_rel s (t:('c,'ffi) closSem$state) /\ LIST_REL (v_rel s.max_app) xs ys ==>
    case do_app opp ys t of
    | Rerr err2 => (?err1. do_app opp xs s = Rerr err1 /\
                           exc_rel (v_rel s.max_app) err1 err2)
    | Rval (y,t1) => ?x s1. v_rel s.max_app x y /\ state_rel s1 t1 /\
                            do_app opp xs s = Rval (x,s1)
Proof
  mp_tac do_app_inst \\ fs [] \\ EVERY_CASE_TAC \\ metis_tac []
QED

val v_rel_IMP_v_to_bytes = prove(
  ``v_rel max_app x y ==> v_to_bytes y = v_to_bytes x``,
  metis_tac [simple_val_rel, simple_val_rel_v_to_bytes]);

val v_rel_IMP_v_to_words = prove(
  ``v_rel max_app x y ==> v_to_words y = v_to_words x``,
  metis_tac [simple_val_rel, simple_val_rel_v_to_words]);

val do_install_inst =
  simple_val_rel_do_install
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`,
        `cr`|->`code_rel s.max_app`]
  |> SIMP_RULE bool_ss [simple_val_rel, simple_state_rel]
  |> Q.SPEC `clos_mti$compile_inc s.max_app`

val do_install_lemma = prove(
  ``state_rel s t /\ LIST_REL (v_rel s.max_app) xs ys ==>
    case do_install xs s of
      | (Rerr err1, s1) => ?err2 t1. do_install ys t = (Rerr err2, t1) /\
                            exc_rel (v_rel s.max_app) err1 err2 /\
                            s1.max_app = s.max_app /\ state_rel s1 t1
      | (Rval exps1, s1) => ?exps2 t1. (s1.max_app = s.max_app /\
                               state_rel s1 t1) /\ (~ (exps1 = [])) /\
                               code_rel s.max_app exps1 exps2 /\
                               do_install ys t = (Rval exps2, t1)``,
  strip_tac
  \\ irule do_install_inst
  \\ fs [simple_compile_state_rel_def, simple_state_rel]
  \\ qexists_tac `s`
  \\ fs [compile_inc_def, pairTheory.FORALL_PROD,
            clos_mtiTheory.intro_multi_length, code_rel_def, state_rel_def]
  \\ rw [shift_seq_def, backendPropsTheory.pure_co_def, FUN_EQ_THM] \\ rfs []
  \\ fs [PAIR_FST_SND_EQ] \\ rveq \\ fs []
  );

Theorem intro_multi_EQ_NIL[simp]:
   ∀max_app es. intro_multi max_app es = [] ⇔ es = []
Proof
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind >>
  simp[clos_mtiTheory.intro_multi_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[])
QED

Theorem intro_multi_nil:
   intro_multi x [] = []
Proof
metis_tac[intro_multi_EQ_NIL]
QED

Theorem result_rel_Rval2:
  result_rel P P' x (Rval v') = (?v. x = Rval v /\ P v v')

Proof
  Cases_on `x` \\ fs []
QED

Theorem evaluate_intro_multi:
   (!ys env2 (t1:('c,'ffi) closSem$state) env1 t2 s1 res2 xs.
     (evaluate (ys,env2,t1) = (res2,t2)) /\
     EVERY2 (v_rel s1.max_app) env1 env2 /\
     state_rel s1 t1 /\ code_rel s1.max_app xs ys ==>
     ?res1 s2.
        (evaluate (xs,env1,s1) = (res1,s2)) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1 res2 /\
        state_rel s2 t2) /\
   (!loc_opt f2 args2 (t1:('c,'ffi) closSem$state) res2 t2 f1 args1 s1.
     (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\ loc_opt = NONE /\
     v_rel s1.max_app f1 f2 /\ EVERY2 (v_rel s1.max_app) args1 args2 /\
     state_rel s1 t1 /\ LENGTH args1 <= s1.max_app ==>
     ?res1 s2.
       (evaluate_apps f1 args1 s1 = (res1,s2)) /\
       result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1 res2 /\
       state_rel s2 t2)
Proof
  ho_match_mp_tac (evaluate_ind |> Q.SPEC `λ(x1,x2,x3). P0 x1 x2 x3`
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs []
    \\ fs [evaluate_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  THEN1 (* If *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [evaluate_def,HD_intro_multi]
    \\ reverse (fs [evaluate_def,case_eq_thms,pair_case_eq] \\ rveq)
    \\ first_x_assum drule
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[] \\ strip_tac \\ fs []
    \\ rename1 `(if opp = _ then _ else _) = _`
    \\ Cases_on `opp = Install` \\ fs [] \\ rveq
    THEN1 (* Op = Install *)
    ( fs [result_rel_Rval2]
      \\ drule (GEN_ALL do_install_lemma)
      \\ imp_res_tac evaluate_const \\ fs []
      \\ drule EVERY2_REVERSE \\ disch_tac
      \\ disch_then drule
      \\ fs [CaseEq "prod"]
      \\ TOP_CASE_TAC
      \\ TOP_CASE_TAC \\ rw [] \\ fs [] \\ rveq \\ fs []
      \\ fs [code_rel_def]
      \\ fs [CaseEq "prod", CaseEq "result"] \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ rw []
      \\ fs [result_rel_Rval2]
      \\ ho_match_mp_tac LIST_REL_LAST
      \\ fs []
      \\ CCONTR_TAC
      \\ fs [])
    (* do_app *)
    \\ Cases_on `res1` \\ fs []
    \\ imp_res_tac evaluate_const \\ fs []
    \\ drule (GEN_ALL do_app_lemma)
    \\ imp_res_tac evaluate_const \\ fs []
    \\ `LIST_REL (v_rel s1.max_app) (REVERSE a) (REVERSE vs)` by
           (match_mp_tac EVERY2_REVERSE \\ fs [])
    \\ disch_then drule
    \\ disch_then (qspec_then `opp` mp_tac) \\ fs []
    \\ rw [] \\ fs []
    \\ Cases_on `do_app opp (REVERSE vs) s'` \\ fs []
    \\ rveq \\ fs []
    \\ rename1 `_ = Rval aa` \\ Cases_on `aa` \\ fs [] \\ rveq \\ fs [])
  THEN1 (* Fn *)
   (Cases_on `xs` \\ fs [] \\ rveq
    \\ Cases_on `h` \\ fs [code_rel_def,intro_multi_def] \\ rveq \\ fs []
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [EVERY2_MAP]
    \\ match_mp_tac EVERY2_refl
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [intro_multi_length]
    \\ fs [DECIDE ``n > 0n <=> n <> 0``]
    \\ imp_res_tac collect_apps_acc \\ rveq
    \\ `?x. l = [x]` by (Cases_on `l` \\ fs [] \\ Cases_on `t`) \\ rveq \\ fs []
    \\ `EVERY no_mti other /\ no_mti x /\ no_mti e'` by
     (drule collect_apps_no_mti \\ fs [])
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
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
    \\ fs [no_mti_def] \\ rveq \\ fs [intro_multi_def]
    \\ TRY pairarg_tac \\ fs [])
  THEN1 (* app NIL *)
   (fs [evaluate_def,evaluate_apps_def] \\ rveq \\ fs [])
  (* app CONS *)
  \\ fs [evaluate_def] \\ rveq \\ fs []
  \\ fs [case_eq_thms] \\ fs [] \\ rveq
  THEN1 (* dest_closure returns NONE *)
   (`?y. dest_closure s1.max_app NONE f1 (x::xs) = NONE` by
     (fs [dest_closure_def,case_eq_thms]
      \\ qpat_x_assum `v_rel _ f1 f2` mp_tac \\ fs []
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
      \\ qpat_x_assum `v_rel _ f1 f2` mp_tac \\ fs []
      \\ strip_tac \\ fs [] \\ rveq \\ fs [check_loc_def]
      \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) =
                              SOME (if b then x else y)``])
    \\ drule dest_closure_NONE_IMP_apps \\ fs [])
  THEN1 (* dest_closure returns Patrial_app *)
   (qpat_x_assum `v_rel _ f1 f2` mp_tac \\ fs []
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
      \\ simp [ADD1]
      \\ qexists_tac `ys ++ [y]`
      \\ qexists_tac `env1` \\ fs []
      \\ qexists_tac `funs1` \\ fs []
      \\ qexists_tac `DROP (LENGTH ys) t` \\ fs []
      \\ qexists_tac `b1` \\ fs []
      \\ simp[GSYM SNOC_APPEND]
      \\ qpat_x_assum `x::xs = _` (fn th => simp [GSYM th])
      \\ fs [LIST_REL_GENLIST] \\ rw []
      \\ simp [ADD1])
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
  \\ rename1 `LIST_REL (v_rel s1.max_app) xs ysss`
  THEN1
   (Cases_on `t1.clock < SUC (LENGTH ysss) − LENGTH rest_args` \\ fs []
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
        metis_tac [REVERSE_SNOC,REVERSE_DEF,SNOC_APPEND] \\ fs []
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
        \\ simp [])
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
      THEN1 (fs [LIST_REL_GENLIST] \\ simp [])
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
    \\ match_mp_tac EVERY2_DROP \\ fs [])
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
      \\ match_mp_tac EVERY2_TAKE
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs [])
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
    \\ match_mp_tac EVERY2_DROP \\ fs []
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs [])
QED

Theorem intro_multi_correct:
   !xs env1 (s1:('c,'ffi) closSem$state) res1 s2 env2 t2 t1.
      evaluate (xs,env1,s1) = (res1,s2) /\ EVERY no_mti xs /\
      LIST_REL (v_rel s1.max_app) env1 env2 /\ state_rel s1 t1 ==>
      ?res2 t2.
        evaluate (intro_multi s1.max_app xs,env2,t1) = (res2,t2) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res1
          res2 /\ state_rel s2 t2
Proof
  rpt gen_tac
  \\ Cases_on `evaluate (intro_multi s1.max_app xs,env2,t1)` \\ fs []
  \\ drule (CONJUNCT1 evaluate_intro_multi)
  \\ ntac 2 strip_tac \\ first_x_assum drule
  \\ fs [code_rel_def] \\ disch_then drule \\ fs []
QED

(* syntax well-formedness *)

Theorem contains_App_SOME_collect_args:
   ∀m x y a b. collect_args m x y = (a,b) ⇒
    (contains_App_SOME m [y] ⇔ contains_App_SOME m [b])
Proof
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def]
QED

Theorem contains_App_SOME_collect_apps:
   ∀max_app x y a b. collect_apps max_app x y = (a,b) ⇒
    (max_app < LENGTH x ∨ contains_App_SOME max_app x ∨ contains_App_SOME max_app [y] ⇔
     max_app < LENGTH a ∨ contains_App_SOME max_app a ∨ contains_App_SOME max_app [b])
Proof
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`max_app < LENGTH x`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  Cases_on`max_app < LENGTH es`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >> srw_tac[][] >>
  rpt (pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] >>
  metis_tac[]
QED

Theorem contains_App_SOME_intro_multi[simp]:
   ∀max_app es. contains_App_SOME max_app (intro_multi max_app es) ⇔ contains_App_SOME max_app es
Proof
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
    metis_tac[contains_App_SOME_collect_args,SND,PAIR])
QED

Theorem contains_App_SOME_compile[simp]:
   ∀do_mti es. contains_App_SOME max_app (clos_mti$compile do_mti max_app es) ⇔ contains_App_SOME max_app es
Proof
  Cases>>fs[clos_mtiTheory.compile_def]
QED

Theorem collect_args_preserves_esgc_free:
   ∀max_app n e n' e'. collect_args max_app n e = (n',e') ∧
                       esgc_free e ⇒ esgc_free e'
Proof
  ho_match_mp_tac clos_mtiTheory.collect_args_ind >>
  simp[clos_mtiTheory.collect_args_def, bool_case_eq] >> dsimp[] >>
  rpt strip_tac >> metis_tac[set_globals_empty_esgc_free]
QED

Triviality every_Fn_vs_NONE_collect_apps:
  ∀max_app es e x y. collect_apps max_app es e = (x,y) ⇒
  (every_Fn_vs_NONE x ∧ every_Fn_vs_NONE [y] ⇔
   every_Fn_vs_NONE es ∧ every_Fn_vs_NONE [e])
Proof
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >> full_simp_tac(srw_ss())[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[][] >> metis_tac[]
QED

Triviality every_Fn_vs_NONE_collect_args:
  ∀max_app es e x y. collect_args max_app es e = (x,y) ⇒
    (every_Fn_vs_NONE [y] ⇔ every_Fn_vs_NONE [e])
Proof
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >> full_simp_tac(srw_ss())[]
QED

Theorem every_Fn_vs_NONE_intro_multi[simp]:
   ∀max_app es. every_Fn_vs_NONE (intro_multi max_app es) = every_Fn_vs_NONE es
Proof
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi]
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
  metis_tac[every_Fn_vs_NONE_collect_args,SND,PAIR]
QED

Theorem compile_EQ_NIL[simp]:
   ∀do_mti es. clos_mti$compile do_mti max_app es = [] ⇔ es = []
Proof
  Cases>>fs[clos_mtiTheory.compile_def]
QED

Theorem compile_length[simp]:
   LENGTH (clos_mti$compile do_mti max_app es) = LENGTH es
Proof
  Cases_on`do_mti` \\ rw[clos_mtiTheory.compile_def, clos_mtiTheory.intro_multi_length]
QED

Triviality EVERY_HD:
  EVERY P l ∧ l ≠ [] ⇒ P (HD l)
Proof
  Cases_on `l` >> simp[]
QED

Theorem collect_apps_preserves_set_globals:
   ∀max_app es e es' e'.
     collect_apps max_app es e = (es',e') ⇒
     elist_globals es ⊎ set_globals e = elist_globals es' ⊎ set_globals e'
Proof
  ho_match_mp_tac clos_mtiTheory.collect_apps_ind >>
  simp[clos_mtiTheory.collect_apps_def, bool_case_eq] >> rpt strip_tac
  >- (fs[elist_globals_append] >>
      metis_tac[bagTheory.COMM_BAG_UNION, bagTheory.ASSOC_BAG_UNION])
  >- (rveq >> simp[])
QED

Theorem collect_apps_preserves_esgc_free:
   ∀max_app es e es' e'.
     collect_apps max_app es e = (es',e') ∧ EVERY esgc_free es ∧ esgc_free e ⇒
     EVERY esgc_free es' ∧ esgc_free e'
Proof
  ho_match_mp_tac clos_mtiTheory.collect_apps_ind >>
  simp[clos_mtiTheory.collect_apps_def, bool_case_eq] >> rw[] >>
  simp[] >> metis_tac[]
QED

Theorem collect_args_preserves_set_globals:
   ∀max_app n e n' e'. collect_args max_app n e = (n',e') ⇒ set_globals e' = set_globals e
Proof
  ho_match_mp_tac clos_mtiTheory.collect_args_ind >>
  simp[clos_mtiTheory.collect_args_def, bool_case_eq] >> dsimp[] >>
  rpt strip_tac >> pop_assum (assume_tac o SYM) >> fs[]
QED

val intro1_pat = ``intro_multi max_app [e]``
fun intro_sing th =
  case gen_find_term
         (fn (bvs,t) => if can (match_term intro1_pat) t andalso
                           null (op_intersect aconv bvs (free_vars t))
                        then SOME t
                        else NONE)
                     (concl th)
   of
      SOME t => strip_assume_tac
                  (PART_MATCH (lhs o #2 o dest_exists)
                              clos_mtiTheory.intro_multi_sing t)
    | NONE => NO_TAC

Theorem intro_multi_preserves_elist_globals:
   ∀max_app es. elist_globals (intro_multi max_app es) = elist_globals es
Proof
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
      res_tac >> rfs[])
QED

Theorem intro_multi_preserves_esgc_free:
   ∀max_app es. EVERY esgc_free es ⇒ EVERY esgc_free (intro_multi max_app es)
Proof
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
      fs[] >> metis_tac[collect_args_preserves_set_globals])
QED

Theorem compile_preserves_elist_globals:
   ∀do_mti es. elist_globals (clos_mti$compile do_mti max_app es) = elist_globals es
Proof
  Cases>>fs[clos_mtiTheory.compile_def,intro_multi_preserves_elist_globals]
QED

Theorem compile_preserves_esgc_free:
   ∀do_mti es. EVERY esgc_free es ⇒
               EVERY esgc_free (clos_mti$compile do_mti max_app es)
Proof
  Cases>>fs[clos_mtiTheory.compile_def,intro_multi_preserves_esgc_free]
QED

Theorem EVERY_intro_multi:
  !m xs. EVERY P (intro_multi m xs) = EVERY (\x. P (HD (intro_multi m [x]))) xs
Proof
  ho_match_mp_tac intro_multi_ind
  \\ simp [intro_multi_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem intro_multi_obeys_max_app:
   !m xs. m ≠ 0 /\ EVERY no_mti xs ==>
   EVERY (obeys_max_app m) (intro_multi m xs)
Proof
  ho_match_mp_tac intro_multi_ind \\ rw []
  \\ fs [intro_multi_def,no_mti_def]
  \\ fs [EVERY_intro_multi]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [EVERY_intro_multi, intro_multi_length]
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs []
    \\ imp_res_tac collect_apps_acc \\ rveq \\ fs []
    \\ drule collect_apps_cons \\ fs [] \\ strip_tac
    \\ drule collect_apps_IMP_mk_Apps \\ fs [] \\ strip_tac
    \\ rveq \\ fs []
    \\ drule collect_apps_no_mti \\ fs [no_mti_def]
    \\ `∃x.  intro_multi m [e']  = [x]` by fs [intro_multi_sing] \\ fs [])
  THEN1
   (drule collect_args_ok_IMP \\ fs []
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ `∃x0. intro_multi m [e'] = [x0]` by fs [clos_mtiTheory.intro_multi_sing]
    \\ fs [])
  \\ `∃x.  intro_multi m [e] = [x]` by fs [clos_mtiTheory.intro_multi_sing]
  \\ fs []
  \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ rw [] \\ rveq
  \\ rpt (first_x_assum drule) \\ pairarg_tac \\ fs []
  \\ rveq \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ rename [`_ = (_,e2)`]
  \\ `∃x.  intro_multi m [e2] = [x]` by fs [clos_mtiTheory.intro_multi_sing] \\ fs []
  \\ drule collect_args_ok_IMP \\ fs []
  \\ strip_tac \\ fs []
QED

Theorem collect_apps_no_Labels:
   !m es e es' e'.
      collect_apps m es e = (es',e') /\ EVERY no_Labels es /\ no_Labels e ==>
      EVERY no_Labels es' /\ no_Labels e'
Proof
  ho_match_mp_tac collect_apps_ind \\ fs [collect_apps_def] \\ rw [] \\ fs []
QED

Theorem collect_args_no_Labels:
   !m na e es' e'.
      collect_args m na e = (es',e') /\ no_Labels e ==> no_Labels e'
Proof
  ho_match_mp_tac collect_args_ind \\ fs [] \\ rw [collect_args_def] \\ fs []
QED

Theorem intro_multi_no_Labels:
   !m xs. EVERY no_Labels xs ==> EVERY no_Labels (intro_multi m xs)
Proof
  ho_match_mp_tac intro_multi_ind \\ rw []
  \\ fs [intro_multi_def,no_Labels_def]
  \\ TRY
   (`∃x. intro_multi m [e]  = [x]` by fs [intro_multi_sing]
    \\ `∃x1. intro_multi m [e1] = [x1]` by fs [intro_multi_sing]
    \\ `∃x2. intro_multi m [e2] = [x2]` by fs [intro_multi_sing]
    \\ `∃x3. intro_multi m [e3] = [x3]` by fs [intro_multi_sing]
    \\ fs [] \\ NO_TAC)
  \\ TRY pairarg_tac \\ fs []
  \\ `∃x. intro_multi m [e']  = [x]` by fs [intro_multi_sing] \\ fs []
  THEN1 (imp_res_tac collect_apps_no_Labels \\ fs [])
  THEN1 (imp_res_tac collect_args_no_Labels \\ fs [])
  \\ `∃x. intro_multi m [e]  = [x]` by fs [intro_multi_sing] \\ fs []
  \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ rw [] \\ rveq
  \\ rpt (first_x_assum drule) \\ pairarg_tac \\ fs []
  \\ rveq \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ rename [`_ = (_,e2)`]
  \\ `∃x.  intro_multi m [e2] = [x]` by fs [clos_mtiTheory.intro_multi_sing] \\ fs []
  \\ imp_res_tac collect_args_no_Labels \\ fs []
QED

(* preservation of observable semantics *)

Theorem semantics_intro_multi:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (clos_mti$compile_inc max_app) cc) xs <> Fail ==>
   (∀n. SND (SND (co n)) = [] ∧ EVERY no_mti (FST (SND (co n)))) ∧
   1 <= max_app /\ EVERY no_mti xs ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (pure_co (compile_inc max_app) ∘ co) cc
     (intro_multi max_app xs) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (clos_mti$compile_inc max_app) cc) xs
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule (intro_multi_correct |> SIMP_RULE std_ss [])
  \\ fs []
  \\ disch_then (qspec_then `initial_state ffi max_app FEMPTY
       (pure_co (clos_mti$compile_inc max_app) ∘ co) cc k` mp_tac)
  \\ impl_tac
  THEN1 (fs [state_rel_def,initial_state_def,FMAP_REL_def, v_rel_opt_def])
  \\ strip_tac \\ fs []
  \\ qexists_tac `0`
  \\ fs [] \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []
QED

Theorem semantics_compile:
   semantics ffi max_app FEMPTY co cc1 xs ≠ Fail ∧
   cc1 = (if do_mti then pure_cc (clos_mti$compile_inc max_app) else I) cc ∧
   co1 = (if do_mti then pure_co (clos_mti$compile_inc max_app) else I) o co ∧
   (do_mti ⇒ (∀n. SND (SND (co n)) = [] ∧ EVERY no_mti (FST (SND (co n)))) ∧
        1 ≤ max_app ∧ EVERY no_mti xs) ⇒
   semantics ffi max_app FEMPTY co1 cc (compile do_mti max_app xs) =
   semantics ffi max_app FEMPTY co cc1 xs
Proof
  strip_tac
  \\ Cases_on`do_mti` \\ fs[compile_def]
  \\ irule semantics_intro_multi
  \\ fs[]
QED

val _ = export_theory();
