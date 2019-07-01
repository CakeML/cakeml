(*
  Correctness proof for clos_labels
*)
open preamble closLangTheory clos_labelsTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_labelsProof";

val _ = set_grammar_ancestry ["closLang","clos_labels","closSem","closProps","backend_common"]

Theorem LENGTH_remove_dests:
   !dests xs. LENGTH (remove_dests dests xs) = LENGTH xs
Proof
  recInduct remove_dests_ind \\ simp [remove_dests_def] \\ rw []
QED

Theorem remove_dests_SING:
   !x. ?y. remove_dests dests [x] = [y]
Proof
  Induct \\ fs [remove_dests_def] \\ rw[]
  \\ rename1`App _ opt`
  \\ Cases_on`opt` \\ rw[remove_dests_def]
QED

Theorem HD_remove_dests_SING[simp]:
   !x. [HD (remove_dests dests [x])] = remove_dests dests [x] ∧
       LENGTH (remove_dests dests [x]) = 1
Proof
  strip_tac \\ strip_assume_tac (Q.SPEC `x` remove_dests_SING) \\ simp []
QED

Theorem EVERY_remove_dests_SING:
   EVERY P (remove_dests dests [x]) ⇔ P (HD (remove_dests dests [x]))
Proof
  strip_assume_tac(SPEC_ALL remove_dests_SING) \\ rw[]
QED

Theorem remove_dests_cons:
   ∀x ys. remove_dests ds (x::ys) = remove_dests ds [x] ++ remove_dests ds ys
Proof
  gen_tac \\ Cases \\ rw[remove_dests_def]
QED

val code_rel_def = Define `
  code_rel dests e1 e2 <=>
    e2 = remove_dests dests e1`;

Theorem code_rel_IMP_LENGTH:
   !xs ys. code_rel dests xs ys ==> LENGTH xs = LENGTH ys
Proof
  fs [code_rel_def, LENGTH_remove_dests]
QED

Theorem code_rel_CONS_CONS:
   code_rel dests (x1::x2::xs) (y1::y2::ys) ==>
      code_rel dests [x1] [y1] /\ code_rel dests (x2::xs) (y2::ys)
Proof
  simp [code_rel_def, remove_dests_def]
QED

(* value relation *)

val f_rel_def = Define `
  f_rel ds (a1, e1) (a2, e2) <=>
     a1 = a2 /\ code_rel ds [e1] [e2]`;

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!i. v_rel ds (Number i) (Number i)) /\
  (!w. v_rel ds (Word64 w) (Word64 w)) /\
  (!w. v_rel ds (ByteVector w) (ByteVector w)) /\
  (!n. v_rel ds (RefPtr n) (RefPtr n)) /\
  (!tag xs ys.
     LIST_REL (v_rel ds) xs ys ==>
       v_rel ds (Block tag xs) (Block tag ys)) /\
  (!loc args1 args2 env1 env2 num_args e1 e2.
     LIST_REL (v_rel ds) env1 env2 /\
     LIST_REL (v_rel ds) args1 args2 /\
     code_rel ds [e1] [e2] /\
     set (code_locs [e1]) ⊆ domain ds ∧
     { l |l| loc = SOME l } SUBSET domain ds ==>
       v_rel ds (Closure loc args1 env1 num_args e1)
                (Closure loc args2 env2 num_args e2)) /\
  (!loc args1 args2 env1 env2 k.
     LIST_REL (v_rel ds) env1 env2 /\
     LIST_REL (v_rel ds) args1 args2 /\
     LIST_REL (f_rel ds) funs1 funs2 /\
     set (code_locs (MAP SND funs1)) ⊆ domain ds ∧
     { l + 2 * k |l,k| loc = SOME l /\ k < LENGTH funs1 } SUBSET domain ds
     ==>
       v_rel ds (Recclosure loc args1 env1 funs1 k)
                (Recclosure loc args2 env2 funs2 k))`;

val v_rel_simps = save_thm("v_rel_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (Number n) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (Block n p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (Word64 p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (ByteVector p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (RefPtr p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (Closure x1 x2 x3 x4 x5) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel ds (Recclosure y1 y2 y3 y4 y5) x``,
  prove(``v_rel ds (Boolv b) x <=> x = Boolv b``,
        Cases_on `b` \\ fs [Boolv_def,Once v_rel_cases]),
  prove(``v_rel ds Unit x <=> x = Unit``,
        fs [closSemTheory.Unit_def,Once v_rel_cases])])

(* state relation *)

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel ds (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL (v_rel ds) xs ys ==>
    ref_rel ds (ValueArray xs) (ValueArray ys))`

val state_rel_def = Define `
  state_rel ds (s:('c, 'ffi) closSem$state) (t:('c, 'ffi) closSem$state) <=>
    t.max_app = s.max_app /\ (* 1 <= s.max_app /\ *)
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL (v_rel ds)) s.globals t.globals /\
    fmap_rel (ref_rel ds) s.refs t.refs ∧
    fmap_rel (f_rel ds) s.code t.code`;

(* *)

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y.
      v_rel ds x y ==>
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
  ``v_rel ds x y ==> v_to_bytes y = v_to_bytes x``,
  rw [v_to_bytes_def] \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []);

val v_rel_IMP_v_to_words_lemma = prove(
  ``!x y.
      v_rel ds x y ==>
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
  ``v_rel ds x y ==> v_to_words y = v_to_words x``,
  rw [v_to_words_def] \\ drule v_rel_IMP_v_to_words_lemma \\ fs []);


(* *)

Theorem lookup_vars_lemma:
   !vs env1 env2. LIST_REL (v_rel ds) env1 env2 ==>
    case lookup_vars vs env1 of
      | NONE => lookup_vars vs env2 = NONE
      | SOME l1 => ?l2. LIST_REL (v_rel ds) l1 l2 /\ lookup_vars vs env2 = SOME l2
Proof
  Induct_on `vs` \\ fs [lookup_vars_def]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw []
  \\ res_tac
  \\ Cases_on `lookup_vars vs env1`
  \\ fs []
  \\ fs [LIST_REL_EL_EQN]
QED

Theorem dest_closure_SOME_IMP:
   dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)
Proof
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []
QED

Theorem dest_closure_SOME_Full_app:
   v_rel ds f1 f2 /\ v_rel ds a1 a2 /\ LIST_REL (v_rel ds) args1 args2 /\
    dest_closure max_app loc_opt f1 (a1::args1) = SOME (Full_app exp1 env1 rest_args1) ==>
      ?exp2 env2 rest_args2.
      code_rel ds [exp1] [exp2] /\
      LIST_REL (v_rel ds) env1 env2 /\
      LIST_REL (v_rel ds) rest_args1 rest_args2 /\
      dest_closure max_app loc_opt f2 (a2::args2) = SOME (Full_app exp2 env2 rest_args2)
Proof
   rpt strip_tac
   \\ imp_res_tac dest_closure_SOME_IMP
   \\ rveq \\ fs [] \\ rveq
   \\ imp_res_tac LIST_REL_LENGTH
   \\ qpat_x_assum `_ = SOME _` mp_tac
   THEN1 (rename1 `code_rel _ [e1] [e2]`
          \\ simp [dest_closure_def]
          \\ IF_CASES_TAC \\ simp []
          \\ strip_tac \\ rveq \\ fs []
          \\ conj_tac
          THEN1 (ntac 2 (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ irule EVERY2_DROP
          \\ irule EVERY2_APPEND_suff \\ simp [])
   \\ rename1 `LIST_REL (f_rel _) fns1 fns2`
   \\ simp [dest_closure_def]
   \\ ntac 2 (pairarg_tac \\ simp [])
   \\ Cases_on `i < LENGTH fns2` \\ simp []
   \\ IF_CASES_TAC \\ simp []
   \\ strip_tac \\ rveq \\ fs []
   \\ qpat_x_assum `LIST_REL (f_rel _) _ _` assume_tac
   \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
   \\ simp [] \\ disch_then drule
   \\ simp [f_rel_def]
   \\ strip_tac \\ fs [] \\ rveq \\ fs[]
   \\ conj_tac
   THEN1 (irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_APPEND_suff \\ simp [LIST_REL_GENLIST]
          \\ irule EVERY2_APPEND_suff \\ simp []
          \\ irule EVERY2_TAKE
          \\ irule EVERY2_APPEND_suff \\ simp [])
   \\ irule EVERY2_DROP
   \\ irule EVERY2_APPEND_suff \\ simp []
QED

val do_app_lemma = prove(
  ``state_rel ds s t /\ LIST_REL (v_rel ds) xs ys ==>
    case do_app opp xs s of
      | Rerr err1 => ?err2. do_app opp ys t = Rerr err2 /\
                            exc_rel (v_rel ds) err1 err2
      | Rval (x, s1) => ?y t1. v_rel ds x y /\ state_rel ds s1 t1 /\
                               do_app opp ys t = Rval (y, t1)``,
  match_mp_tac simple_val_rel_do_app
  \\ conj_tac THEN1 (fs [simple_val_rel_def] \\ rw [] \\ fs [v_rel_cases])
  \\ fs [simple_state_rel_def, state_rel_def]
  \\ rw [] \\ fs [fmap_rel_def, FLOOKUP_DEF] \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);

(* evaluate level correctness *)

val evaluate_code_const_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          (s1.code = s.code))`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (_,s1) =>
          (s1.code = x4.code))`;

val evaluate_code_const_lemma = prove(
  evaluate_code_const_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_code_const_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC do_app_const
  \\ full_simp_tac(srw_ss())[dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem evaluate_code_const:
   (evaluate (xs,env,s) = (res,s1)) ==>
      (s1.code = s.code)
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_code_const_lemma |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`env`,`s`] mp_tac)
  \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_remove_dests:
   (!xs env1 (s1:('c,'ffi) closSem$state) res1 s2 ys env2 t1.
      evaluate (xs, env1, s1) = (res1, s2) /\
      LIST_REL (v_rel ds) env1 env2 /\ state_rel ds s1 t1 /\
      FDOM s1.code ⊆ domain ds ∧ set (code_locs xs) ⊆ domain ds ∧
      BIGUNION (IMAGE (λ(_,e). set (code_locs [e])) (FRANGE s1.code)) ⊆ domain ds ∧
      code_rel ds xs ys ==>
      ?res2 t2.
        evaluate (ys, env2, t1) = (res2, t2) /\
        result_rel (LIST_REL (v_rel ds)) (v_rel ds) res1 res2 /\
        state_rel ds s2 t2) /\
   (!loc_opt f1 args1 (s1:('c,'ffi) closSem$state) res1 s2 f2 args2 t1.
      evaluate_app loc_opt f1 args1 s1 = (res1, s2) /\
      v_rel ds f1 f2 /\ LIST_REL (v_rel ds) args1 args2 /\
      { l | l | loc_opt = SOME l } ⊆ domain ds ∧
      BIGUNION (IMAGE (λ(_,e). set (code_locs [e])) (FRANGE s1.code)) ⊆ domain ds ∧
      state_rel ds s1 t1 ∧ FDOM s1.code ⊆ domain ds
      ==>
      ?res2 t2.
        evaluate_app loc_opt f2 args2 t1 = (res2, t2) /\
        result_rel (LIST_REL (v_rel ds)) (v_rel ds) res1 res2 /\
        state_rel ds s2 t2)
Proof
  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ conj_tac
  >- (
    rw[evaluate_def]
    \\ imp_res_tac code_rel_IMP_LENGTH
    \\ fs[LENGTH_EQ_NUM_compute] )
  \\ conj_tac
  >- (
    rw[evaluate_def]
    \\ imp_res_tac code_rel_IMP_LENGTH
    \\ fs[ADD1]
    \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[ADD_SYM])
    \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\ fs[]
    \\ imp_res_tac code_rel_CONS_CONS
    \\ fs[evaluate_def]
    \\ reverse (fs [case_eq_thms, pair_case_eq, code_locs_def])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [PULL_EXISTS] (* Closes Rerr *)
    \\ imp_res_tac evaluate_code_const \\ fs[]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [] (* Closes Rval :: Rerr *)
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  \\ conj_tac THEN1 (* Var *) (
    rw[evaluate_def, remove_dests_def, code_rel_def]
    \\ res_tac \\ rfs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ simp[do_app_def])
  \\ conj_tac THEN1 (* If *)
   (rw [code_rel_def, remove_dests_def] \\ rveq
    \\ fs [evaluate_def]
    \\ reverse (fs [case_eq_thms, pair_case_eq, code_locs_def])
    \\ rveq \\ fsrw_tac[DNF_ss] [PULL_EXISTS]
    \\ imp_res_tac evaluate_code_const \\ fs[]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac
    \\ `(Boolv T = HD v' <=> Boolv T = HD vs) /\
        (Boolv F = HD v' <=> Boolv F = HD vs)` by
         (imp_res_tac evaluate_SING
          \\ rveq \\ fs [] \\ rveq
          \\ qpat_x_assum `v_rel _ _ _` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp [EVAL ``closSem$Boolv T``,EVAL ``closSem$Boolv F``]
          \\ rw [] \\ eq_tac \\ rw []
          \\ fs [Once v_rel_cases])
    \\ ntac 2 (pop_assum (fn th => fs [th]))
    \\ IF_CASES_TAC
    \\ TRY (IF_CASES_TAC)
    \\ fs [] \\ rveq \\ fs [])
  \\ conj_tac THEN1 (* Let *)
   (fs [code_rel_def, remove_dests_def]
    \\ rw[evaluate_def]
    \\ fsrw_tac[DNF_ss][CaseEq"prod",code_locs_def]
    \\ imp_res_tac evaluate_code_const \\ fs[]
    \\ first_x_assum drule
    \\ rpt(disch_then drule \\ fs[])
    \\ strip_tac \\ fs[]
    \\ fsrw_tac[DNF_ss][case_eq_thms] \\ rveq \\ fs[LENGTH_remove_dests]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[]
    \\ first_x_assum irule \\ simp[]
    \\ irule EVERY2_APPEND_suff \\ fs[])
  \\ conj_tac THEN1 (* Raise *)
   (fs [code_rel_def, remove_dests_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq,code_locs_def]
    \\ imp_res_tac evaluate_code_const \\ fs[]
    \\ first_x_assum drule
    \\ rpt(disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [])
  \\ conj_tac THEN1 (* Handle *)
   (fs [code_rel_def, remove_dests_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq, code_locs_def]
    \\ imp_res_tac evaluate_code_const
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ fsrw_tac[DNF_ss][ADD1])
  \\ conj_tac THEN1 (* Op *)
   (fs [code_rel_def, remove_dests_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq, code_locs_def]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ IF_CASES_TAC \\ rveq \\ fs []
    THEN1 (* Op = Install *)
      (rveq \\ fs[])
    (* op <> Install *)
    \\ drule EVERY2_REVERSE \\ disch_tac
    \\ drule (GEN_ALL do_app_lemma)
    \\ disch_then drule
    \\ disch_then (qspec_then `op` mp_tac)
    \\ fs [case_eq_thms, pair_case_eq]
    \\ rveq \\ fs []
    \\ strip_tac \\ fs [])
  \\ conj_tac THEN1 (* Fn *)
   (fs [code_rel_def, remove_dests_def] \\ rveq
    \\ rw [evaluate_def]
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs []
    \\ rveq \\ fs [] \\ rveq \\ fs [code_locs_def]
    \\ fs [Once case_eq_thms] \\ rveq \\ fs[]
    THEN1 (fs [code_rel_def, SUBSET_DEF] \\ rw[] \\ fs[])
    \\ drule (Q.SPEC `vs` lookup_vars_lemma)
    \\ CASE_TAC \\ strip_tac
    \\ fs [] \\ rveq \\ fs [code_rel_def]
    \\ imp_res_tac lookup_vars_SOME \\ fs[]
    \\ rw[SUBSET_DEF] \\ fs[])
  \\ conj_tac THEN1 (* Letrec *)
   (rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs[code_rel_def, remove_dests_def] \\ rveq
    \\ fs[evaluate_def, EVERY_MAP, LAMBDA_PROD]
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      fs[CaseEq"bool"] \\ rveq \\ fs[]
      \\ fs[EVERY_MEM, EXISTS_MEM]
      \\ res_tac \\ fs[] )
    \\ fs[CaseEq"option", code_locs_def] \\ rveq \\ fs[]
    >- (
      imp_res_tac lookup_vars_lemma
      \\ pop_assum(qspec_then`names`mp_tac)
      \\ simp[] )
    >- (
      first_x_assum irule \\ simp[]
      \\ irule EVERY2_APPEND_suff \\ fs[]
      \\ fs[LIST_REL_GENLIST]
      \\ fs[LIST_REL_EL_EQN, EL_MAP]
      \\ fs[SUBSET_DEF] \\ rw[]
      >- (
        pairarg_tac \\ fs[f_rel_def]
        \\ fs[code_rel_def] )
      \\ fs[MEM_GENLIST, PULL_EXISTS]
      \\ rpt(first_x_assum(qspec_then`k`mp_tac))
      \\ rw[] )
    >- (
      imp_res_tac lookup_vars_lemma
      \\ pop_assum(qspec_then`names`mp_tac)
      \\ simp[] \\ strip_tac \\ fs[]
      \\ imp_res_tac lookup_vars_SOME \\ fs[]
      \\ first_x_assum irule \\ simp[]
      \\ irule EVERY2_APPEND_suff \\ fs[]
      \\ fs[LIST_REL_GENLIST]
      \\ fs[LIST_REL_EL_EQN, EL_MAP]
      \\ fs[SUBSET_DEF] \\ rw[]
      >- (
        pairarg_tac \\ fs[f_rel_def]
        \\ fs[code_rel_def] )
      \\ fs[MEM_GENLIST, PULL_EXISTS]
      \\ rpt(first_x_assum(qspec_then`k`mp_tac))
      \\ rw[] ) )
  \\ conj_tac THEN1 (* App *) (
    rpt gen_tac \\ strip_tac
    \\ Cases_on`loc_opt` \\ fs[remove_dests_def, code_rel_def, evaluate_def, code_locs_def]
    >- (
      rw[] \\ fs[LENGTH_remove_dests]
      \\ fs[CaseEq"prod"]
      \\ first_x_assum drule
      \\ rpt(disch_then drule) \\ rw[]
      \\ fs[case_eq_thms, PULL_EXISTS, CaseEq"prod"] \\ rveq \\ fs[]
      \\ fsrw_tac[DNF_ss][]
      \\ imp_res_tac evaluate_code_const \\ fs[]
      \\ first_x_assum drule
      \\ rpt(disch_then drule) \\ rw[]
      \\ imp_res_tac evaluate_SING \\ fs[])
    \\ rpt gen_tac
    \\ strip_tac
    \\ IF_CASES_TAC
    >- (
      rw[] \\ fs[LENGTH_remove_dests, evaluate_def]
      \\ rw[] \\ fs[] \\ rw[]
      \\ fs[CaseEq"prod"]
      \\ first_x_assum drule
      \\ rpt(disch_then drule) \\ rw[]
      \\ fs[case_eq_thms, PULL_EXISTS, CaseEq"prod"] \\ rveq \\ fs[]
      \\ fsrw_tac[DNF_ss][]
      \\ imp_res_tac evaluate_code_const \\ fs[]
      \\ first_x_assum drule
      \\ rpt(disch_then drule) \\ rw[]
      \\ imp_res_tac evaluate_SING \\ fs[]
      \\ rveq \\ fs[]
      \\ first_x_assum irule \\ fs[]
      \\ fs[domain_lookup, IS_SOME_EXISTS])
    \\ Cases_on`NULL xs` \\ simp[evaluate_def, do_app_def]
    >- ( fs[NULL_EQ] \\ rw[])
    \\ simp[evaluate_append]
    \\ `LENGTH xs > 0` by (CCONTR_TAC \\ fs[NULL_EQ, NOT_GREATER]) \\ fs[]
    \\ fs[CaseEq"prod"] \\ fs[]
    \\ reverse(fs[case_eq_thms, CaseEq"prod"] \\ rveq \\ fs[PULL_EXISTS])
    >- ( first_x_assum drule \\ disch_then drule \\ rw[] \\ rw[] )
    >- (
      first_x_assum drule
      \\ disch_then drule \\ rw[] \\ fs[]
      \\ first_x_assum drule
      \\ disch_then drule \\ rw[] \\ fs[]
      \\ fsrw_tac[DNF_ss][]
      \\ disj2_tac \\ first_x_assum irule
      \\ imp_res_tac evaluate_code_const \\ fs[])
    \\ first_x_assum drule
    \\ rpt(disch_then drule) \\ rw[]
    \\ imp_res_tac evaluate_code_const
    \\ imp_res_tac evaluate_SING \\ fs[] \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ rpt(disch_then drule) \\ rw[] \\ fs[]
    \\ Cases_on`y2 = []` >- (
      imp_res_tac LIST_REL_LENGTH
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs[] )
    \\ fs[evaluate_app_rw]
    \\ fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ imp_res_tac dest_closure_SOME_IMP
    \\ fs[dest_closure_def, CaseEq"bool"] \\ rveq \\ fs[check_loc_def]
    \\ rveq \\ fs[domain_lookup]
    \\ pairarg_tac \\ fs[]
    \\ rveq \\ fs[]
    \\ fs[SUBSET_DEF, PULL_EXISTS, NOT_LESS_EQUAL]
    \\ fs[domain_lookup]
    \\ res_tac \\ fs[])
  \\ conj_tac THEN1 (* Tick *)
   (fs [code_rel_def, remove_dests_def, code_locs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ fs [dec_clock_def, state_rel_def])
  \\ conj_tac THEN1 (* Call *)
   (fs [code_rel_def, remove_dests_def, code_locs_def] \\ rveq
    \\ rpt gen_tac \\ strip_tac
    \\ simp [evaluate_def]
    \\ rpt gen_tac \\ strip_tac
    \\ fs[CaseEq"prod"]
    \\ IF_CASES_TAC
    >- (
      fs[evaluate_def, case_eq_thms] \\ rveq \\ fs[]
      \\ first_x_assum drule \\ disch_then drule
      \\ rw[] \\ fs[]
      >- (
        imp_res_tac LIST_REL_LENGTH
        \\ PURE_TOP_CASE_TAC \\ fs[]
        \\ fs[find_code_def]
        \\ fs[state_rel_def]
        \\ fs[fmap_rel_def]
        \\ fs[FLOOKUP_DEF] \\ rfs[]
        \\ fs[CaseEq"bool",CaseEq"option",CaseEq"prod"]
        \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ simp[f_rel_def] )
      \\ fs[CaseEq"prod"] \\ rveq
      \\ fs[find_code_def]
      \\ fs[CaseEq"option", CaseEq"prod"]
      \\ qmatch_assum_rename_tac`state_rel ds x2 t2`
      \\ `fmap_rel (f_rel ds) x2.code t2.code` by fs[state_rel_def]
      \\ drule fmap_rel_FLOOKUP_imp
      \\ strip_tac
      \\ first_x_assum drule
      \\ strip_tac \\ simp[]
      \\ Cases_on`v2` \\ fs[f_rel_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
      \\ `t2.clock = x2.clock` by fs[state_rel_def]
      \\ fs[]
      \\ IF_CASES_TAC \\ fs[] \\ rveq \\ fs[]
      >- fs[state_rel_def]
      \\ first_x_assum drule
      \\ disch_then(qspec_then`(dec_clock (ticks+1) t2)`mp_tac)
      \\ fs[code_rel_def]
      \\ disch_then irule
      \\ imp_res_tac evaluate_code_const \\ fs[dec_clock_def]
      \\ reverse conj_tac >- fs[state_rel_def, dec_clock_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, IN_FRANGE_FLOOKUP, FORALL_PROD]
      \\ metis_tac[])
    \\ Cases_on`NULL xs` \\ simp[evaluate_def, do_app_def]
    >- (
      fs[NULL_EQ, remove_dests_def, evaluate_def] \\ rveq \\ fs[]
      \\ fs[find_code_def]
      \\ `FLOOKUP s.code dest = NONE`
      by (
        fs[SUBSET_DEF, FLOOKUP_DEF, domain_lookup]
        \\ strip_tac \\ res_tac \\ fs[] )
      \\ fs[] \\ rveq \\ fs[] )
    \\ fs[]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ fs[]
    \\ fs[Once case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rveq \\ fs[]
    \\ rveq \\ fs[]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ imp_res_tac LIST_REL_LENGTH
    \\ qmatch_goalsub_rename_tac`REVERSE ws`
    \\ CASE_TAC \\ fs[]
    \\ fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ fs[CaseEq"prod"] \\ rveq \\ fs[]
    \\ fs[find_code_def]
    \\ imp_res_tac evaluate_code_const \\ fs[]
    \\ fs[CaseEq"option"]
    \\ fs[FLOOKUP_DEF, SUBSET_DEF, domain_lookup]
    \\ res_tac \\ fs[] )
  \\ conj_tac THEN1 (* evaluate_app NIL *)
   (simp [])
  (* evaluate_app CONS *)
  \\ rw [evaluate_def]
  \\ `s1.max_app = t1.max_app` by fs [state_rel_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  THEN1 (* dest_closure returns NONE *) (
    rw[evaluate_def]
    \\ fs [dest_closure_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs[]
    >- (
      rw[] \\ fs[CaseEq"bool"]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs [] )
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ simp[Once COND_RAND]
    \\ Cases_on`i < LENGTH fns` \\ fs[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[f_rel_def] \\ rveq
    \\ strip_tac \\ fs[] )
  THEN1 (* dest_closure returns SOME Partial_app *)
   (imp_res_tac dest_closure_SOME_IMP
    \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ fs[CaseEq"bool"] \\ fs[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rw[evaluate_def] \\ fs[]
    \\ qpat_x_assum `_ = SOME (Partial_app _)` mp_tac
    \\ fs [dest_closure_def]
    \\ TRY (ntac 2 (pairarg_tac \\ fs [])
            \\ Cases_on `i < LENGTH fns` \\ fs []
            \\ qpat_x_assum `LIST_REL (f_rel _) _ _` assume_tac
            \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
            \\ strip_tac
            \\ first_x_assum drule
            \\ simp [f_rel_def]
            \\ strip_tac \\ fs [])
    \\ rpt (pairarg_tac \\ fs[]) \\ rw[]
    \\ fs [dec_clock_def, state_rel_def]
    \\ irule EVERY2_APPEND_suff \\ fs [])
  (* dest_closure returns SOME Full_app *)
  \\ qpat_x_assum `v_rel _ f1 f2` assume_tac
  \\ drule (GEN_ALL dest_closure_SOME_Full_app)
  \\ strip_tac
  \\ qpat_x_assum `v_rel _ f1 f2` mp_tac
  \\ first_x_assum drule
  \\ ntac 2 (disch_then drule)
  \\ ntac 2 strip_tac \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ `s1.clock = t1.clock` by fs [state_rel_def]
  \\ rw[evaluate_def] \\ fs[] \\ rveq \\ fs[]
  THEN1 fs [state_rel_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac `evaluate (xxx2, _, sss2)`
  \\ disch_then (qspecl_then [`xxx2`, `sss2`] mp_tac)
  \\ unabbrev_all_tac \\ simp []
  \\ impl_tac THEN1 (
    fs [dec_clock_def, state_rel_def]
    \\ imp_res_tac dest_closure_SOME_IMP
    \\ fs[dest_closure_def,CaseEq"bool"] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fs[CaseEq"bool"]
    \\ rveq
    \\ fs[code_locs_map, SUBSET_DEF, PULL_EXISTS, MEM_FLAT, MEM_MAP, FORALL_PROD]
    \\ fs[NOT_LESS_EQUAL]
    \\ fs[LIST_REL_EL_EQN]
    \\ rfs[] \\ first_x_assum drule
    \\ Cases_on`EL i fns'`
    \\ simp[f_rel_def] \\ rw[]
    \\ fs[code_rel_def] \\ rfs[]
    \\ metis_tac[MEM_EL] )
  \\ strip_tac \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ first_x_assum irule \\ fs[]
  \\ imp_res_tac evaluate_code_const \\ fs[dec_clock_def]
QED

Theorem add_code_locs_code_locs:
   ∀ds es. domain (add_code_locs ds es) = domain ds ∪ set (code_locs es)
Proof
  recInduct add_code_locs_ind
  \\ rw[add_code_locs_def, code_locs_def, UNION_ASSOC]
  >- ( CASE_TAC \\ rw[EXTENSION] \\ metis_tac[] )
  >- (
    simp[EXTENSION, domain_list_insert]
    \\ metis_tac[])
QED

val code_code_locs_def = Define`
  code_code_locs fm =
    FDOM fm ∪ BIGUNION (IMAGE (λ(_,e). set (code_locs [e])) (FRANGE fm))`;

Theorem remove_dests_correct:
   !xs env1 (s1:('c,'ffi) closSem$state) res1 s2 env2 t1 ds.
       evaluate (xs, env1, s1) = (res1, s2) /\
       LIST_REL (v_rel ds) env1 env2 /\ state_rel ds s1 t1 /\
       code_code_locs s1.code ⊆ domain ds ∧
       set (code_locs xs) ⊆ domain ds
       ==>
       ?res2 t2.
         evaluate (remove_dests ds xs, env2, t1) = (res2, t2) /\
         result_rel (LIST_REL (v_rel ds)) (v_rel ds) res1 res2 /\
         state_rel ds s2 t2
Proof
  rpt strip_tac \\ drule (CONJUNCT1 evaluate_remove_dests)
  \\ disch_then drule
  \\ disch_then drule
  \\ fs [code_rel_def, code_code_locs_def]
QED

(* preservation of observational semantics *)

val compile_inc_def = Define ` (* this is probably wrong *)
  compile_inc (es,aux) =
    ( let ds = list_insert (MAP FST aux) LN in
      let ds = add_code_locs ds (MAP (SND o SND) aux) in
     remove_dests ds es,
     clos_labels$compile aux)`;

Theorem semantics_compile:
   semantics (ffi:'ffi ffi$ffi_state) max_app (alist_to_fmap aux)
     co (pure_cc (compile_inc) cc) xs <> ffi$Fail ==>
   set (code_locs xs) ⊆ code_code_locs (alist_to_fmap aux) ==>
   semantics (ffi:'ffi ffi$ffi_state) max_app
     (alist_to_fmap (clos_labels$compile aux))
     (pure_co (compile_inc) o co) cc
     (remove_dests (add_code_locs
       (list_insert (MAP FST aux) LN) (MAP (SND o SND) aux)) xs) =
   semantics (ffi:'ffi ffi$ffi_state) max_app (alist_to_fmap aux)
     co (pure_cc (compile_inc) cc) xs
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule remove_dests_correct
  \\ simp []
  \\ disch_then (qspec_then `initial_state ffi max_app (alist_to_fmap (clos_labels$compile aux))
                               (pure_co (compile_inc) o co) cc k` mp_tac)
  \\ qmatch_goalsub_abbrev_tac`remove_dests ds`
  \\ disch_then(qspec_then`ds`mp_tac)
  \\ impl_tac
  THEN1 (
    fs [state_rel_def, initial_state_def]
    \\ simp[fmap_rel_OPTREL_FLOOKUP, OPTREL_def, EXISTS_PROD, f_rel_def, code_rel_def]
    \\ simp[compile_def]
    \\ Q.ISPEC_THEN`λp. (FST p, HD(remove_dests ds[SND p]))`(Q.ISPEC_THEN`aux`mp_tac) ALOOKUP_MAP
    \\ simp[Once LAMBDA_PROD] \\ disch_then kall_tac
    \\ conj_tac
    >- (
      qx_gen_tac`a`
      \\ Cases_on`ALOOKUP aux a` \\ simp[]
      \\ PairCases_on`x` \\ fs[] )
    \\ simp[Abbr`ds`, add_code_locs_code_locs]
    \\ fs[code_code_locs_def, domain_list_insert, SUBSET_DEF, PULL_EXISTS,
          IN_FRANGE_FLOOKUP, MEM_MAP, EXISTS_PROD, code_locs_map, MEM_FLAT]
    \\ metis_tac[ALOOKUP_MEM] )
  \\ strip_tac
  \\ qexists_tac `0` \\ simp []
  \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []
QED

(* syntactic properties *)

Theorem remove_dests_every_Fn_SOME[simp]:
   ∀ds es. every_Fn_SOME es ==> every_Fn_SOME (remove_dests ds es)
Proof
  recInduct remove_dests_ind
  \\ rw[remove_dests_def]
  >- (
    fs[Once every_Fn_SOME_EVERY]
    \\ metis_tac[every_Fn_SOME_EVERY] )
  \\ TRY (Cases_on `lookup dest ds` \\ fs [] \\ NO_TAC)
  \\ Induct_on `fns` \\ fs [] \\ rw []
  \\ PairCases_on `h` \\ fs []
  \\ pop_assum mp_tac
  \\ Cases_on `fns` \\ fs []
  \\ PairCases_on `h` \\ fs []
  \\ metis_tac []
QED

Theorem remove_dests_every_Fn_vs_NONE[simp]:
   ∀ds es. every_Fn_vs_NONE es ==> every_Fn_vs_NONE (remove_dests ds es)
Proof
  recInduct remove_dests_ind
  \\ rw[remove_dests_def]
  >- (
    fs[Once every_Fn_vs_NONE_EVERY]
    \\ metis_tac[every_Fn_vs_NONE_EVERY] )
  \\ TRY (Cases_on `lookup dest ds` \\ fs [] \\ NO_TAC)
  \\ Induct_on `fns` \\ fs [] \\ rw []
  \\ PairCases_on `h` \\ fs []
  \\ pop_assum mp_tac
  \\ Cases_on `fns` \\ fs []
  \\ PairCases_on `h` \\ fs []
  \\ metis_tac []
QED

Theorem remove_dests_every_Fn_vs_SOME[simp]:
   ∀ds es. every_Fn_vs_SOME es ==> every_Fn_vs_SOME (clos_labels$remove_dests ds es)
Proof
  recInduct clos_labelsTheory.remove_dests_ind
  \\ rw[clos_labelsTheory.remove_dests_def]
  >- (
    fs[Once every_Fn_vs_SOME_EVERY]
    \\ metis_tac[every_Fn_vs_SOME_EVERY] )
  \\ TRY (Cases_on `lookup dest ds` \\ fs [] \\ NO_TAC)
  \\ Induct_on `fns` \\ fs [] \\ rw []
  \\ PairCases_on `h` \\ fs []
  \\ pop_assum mp_tac
  \\ Cases_on `fns` \\ fs []
  \\ PairCases_on `h` \\ fs []
  \\ metis_tac []
QED

Theorem compile_every_Fn_SOME:
   every_Fn_SOME (MAP (SND o SND) es) ⇒
   every_Fn_SOME (MAP (SND o SND) (clos_labels$compile es))
Proof
  rw[clos_labelsTheory.compile_def, Once every_Fn_SOME_EVERY]
  \\ fs[Once every_Fn_SOME_EVERY]
  \\ fs[EVERY_MAP, UNCURRY]
  \\ fs[EVERY_MEM] \\ rw[remove_dests_SING]
QED

Theorem compile_every_Fn_vs_SOME:
   every_Fn_vs_SOME (MAP (SND o SND) es) ⇒
   every_Fn_vs_SOME (MAP (SND o SND) (clos_labels$compile es))
Proof
  rw[Once every_Fn_vs_SOME_EVERY]
  \\ rw[clos_labelsTheory.compile_def]
  \\ rw[Once every_Fn_vs_SOME_EVERY]
  \\ fs[EVERY_MAP, UNCURRY]
  \\ fs[EVERY_MEM, remove_dests_SING]
QED

Theorem EVERY_remove_dests_sing:
   EVERY f (remove_dests n [y]) <=> f (HD (remove_dests n [y]))
Proof
  `?t. remove_dests n [y] = [t]` by metis_tac [remove_dests_SING] \\ fs []
QED

Theorem remove_dests_no_Labels:
   !ds xs. EVERY no_Labels xs ==> EVERY no_Labels (remove_dests ds xs)
Proof
  ho_match_mp_tac remove_dests_ind \\ rw [remove_dests_def]
  \\ fs [EVERY_remove_dests_sing]
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ rw [] \\ res_tac
QED

Theorem remove_dests_obeys_max_app:
   !ds xs. EVERY (obeys_max_app k) xs ==>
            EVERY (obeys_max_app k) (remove_dests ds xs)
Proof
  ho_match_mp_tac remove_dests_ind \\ rw [remove_dests_def]
  \\ fs [EVERY_remove_dests_sing]
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS,LENGTH_remove_dests]
  \\ rw [] \\ res_tac
QED

Theorem code_locs_remove_dests:
   !ds xs. set (code_locs (remove_dests ds xs)) = set (code_locs xs)
Proof
  ho_match_mp_tac remove_dests_ind \\ rw [remove_dests_def]
  \\ `?x1. remove_dests ds [x] = [x1]` by fs [remove_dests_SING]
  \\ `?r1. remove_dests ds [x1] = [r1]` by fs [remove_dests_SING]
  \\ `?r2. remove_dests ds [x2] = [r2]` by fs [remove_dests_SING]
  \\ `?r3. remove_dests ds [x3] = [r3]` by fs [remove_dests_SING]
  \\ fs [NULL_EQ] \\ once_rewrite_tac [code_locs_cons]
  \\ fs [code_locs_def] \\ rveq
  \\ fs[remove_dests_def, code_locs_def]
  \\ fs[code_locs_append]
  >- ( simp[UNION_COMM] )
  \\ fs[Once EXTENSION, code_locs_map, MEM_MAP, PULL_EXISTS, MEM_FLAT, EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem code_locs_remove_dests_distinct:
   !ds xs. ALL_DISTINCT (code_locs xs) ⇒ ALL_DISTINCT (code_locs (clos_labels$remove_dests ds xs))
Proof
  ho_match_mp_tac clos_labelsTheory.remove_dests_ind \\ rw [clos_labelsTheory.remove_dests_def]
  \\ `?x1. clos_labels$remove_dests ds [x] = [x1]` by fs [remove_dests_SING]
  \\ `?r1. clos_labels$remove_dests ds [x1] = [r1]` by fs [remove_dests_SING]
  \\ `?r2. clos_labels$remove_dests ds [x2] = [r2]` by fs [remove_dests_SING]
  \\ `?r3. clos_labels$remove_dests ds [x3] = [r3]` by fs [remove_dests_SING]
  \\ fs[NULL_EQ, code_locs_def]
  \\ qspecl_then[`ds`,`[x]`]mp_tac code_locs_remove_dests
  \\ qspecl_then[`ds`,`xs`]mp_tac code_locs_remove_dests
  \\ qspecl_then[`ds`,`[x1]`]mp_tac code_locs_remove_dests
  \\ qspecl_then[`ds`,`[x2]`]mp_tac code_locs_remove_dests
  \\ qspecl_then[`ds`,`[x3]`]mp_tac code_locs_remove_dests
  \\ rw[] \\ fs[ALL_DISTINCT_APPEND, code_locs_append]
  >- (
    simp[Once code_locs_cons]
    \\ fs[ALL_DISTINCT_APPEND]
    \\ qspecl_then[`ds`,`y::xs`]mp_tac code_locs_remove_dests
    \\ rw[] )
  >- metis_tac[]
  >- metis_tac[]
  \\ conj_tac
  >- (
    fs[code_locs_map, MAP_MAP_o, o_DEF, UNCURRY, MEM_FLAT, PULL_EXISTS, MEM_MAP, FORALL_PROD]
    \\ reverse conj_tac
    >- (
      rw[]
      \\ first_x_assum match_mp_tac
      \\ asm_exists_tac \\ rw[]
      \\ pop_assum mp_tac
      \\ qspecl_then[`ds`,`[p_2]`]mp_tac code_locs_remove_dests
      \\ rw[] )
    \\ fs[ALL_DISTINCT_FLAT, EL_MAP, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    \\ conj_tac
    >- (
      rw[]
      \\ first_x_assum irule
      \\ metis_tac[] )
    \\ rw[]
    \\ qspecl_then[`ds`,`[SND (EL i fns)]`]mp_tac code_locs_remove_dests
    \\ qspecl_then[`ds`,`[SND (EL j fns)]`]mp_tac code_locs_remove_dests
    \\ rw[] \\ fs[] \\ metis_tac[] )
  \\ fs[code_locs_map, MEM_FLAT, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ reverse(rw[])
  >- metis_tac[]
  \\ qspecl_then[`ds`,`[p_2']`]mp_tac code_locs_remove_dests
  \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

Theorem any_dests_remove_dests:
   ∀ds xs. any_dests (remove_dests ds xs) ⊆ domain ds
Proof
  recInduct remove_dests_ind
  \\ rw[remove_dests_def, IS_SOME_EXISTS, app_call_dests_append]
  \\ simp[Once app_call_dests_cons]
  \\ fs[domain_lookup, NULL_EQ]
  \\ TRY(Cases_on`lookup dest ds` \\ fs[remove_dests_def] \\ NO_TAC)
  \\ simp[app_call_dests_map, SUBSET_DEF, PULL_EXISTS, MEM_MAP, FORALL_PROD]
  \\ fs[SUBSET_DEF] \\ metis_tac[]
QED

Theorem compile_any_dests_SUBSET_code_locs:
   any_dests (MAP (SND ∘ SND) (compile input)) ⊆
    set (MAP FST (compile input)) ∪
    set (code_locs (MAP (SND ∘ SND) (compile input)))
Proof
  fs [compile_def] \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
  \\ qmatch_abbrev_tac `any_dests
       (MAP (λx. HD (remove_dests ds [SND (SND x)])) input) ⊆ d`
  \\ `d = domain ds`
  by (
    simp[Abbr`ds`, add_code_locs_code_locs, Abbr`d`]
    \\ simp[Once EXTENSION, domain_list_insert]
    \\ srw_tac[ETA_ss][]
    \\ AP_TERM_TAC
    \\ simp[code_locs_map]
    \\ simp[MEM_FLAT, MEM_MAP, PULL_EXISTS]
    \\ simp[code_locs_remove_dests] )
  \\ fs[Abbr`d`]
  \\ pop_assum kall_tac
  \\ simp[app_call_dests_map]
  \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  \\ rpt gen_tac
  \\ qmatch_goalsub_abbrev_tac`remove_dests ds xs`
  \\ mp_tac(SPEC_ALL any_dests_remove_dests)
  \\ simp[SUBSET_DEF]
QED

Theorem MAP_FST_compile:
   ∀ls. MAP FST (clos_labels$compile ls) = MAP FST ls
Proof
  Induct
  \\ rw[clos_labelsTheory.compile_def, MAP_MAP_o, o_DEF, UNCURRY]
  \\ srw_tac[ETA_ss][]
QED

Theorem no_Labels_labs:
   !xs.
      EVERY no_Labels (MAP (SND o SND) xs) ==>
      EVERY no_Labels (MAP (SND ∘ SND) (clos_labels$compile xs))
Proof
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`,`remove_dests ds`] \\ fs []
  \\ qspecl_then [`ds`,`[x3]`] mp_tac remove_dests_no_Labels
  \\ fs [EVERY_remove_dests_sing]
QED

Theorem obeys_max_app_labs:
   !xs.
      EVERY (obeys_max_app k) (MAP (SND o SND) xs) ==>
      EVERY (obeys_max_app k) (MAP (SND ∘ SND) (clos_labels$compile xs))
Proof
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`,`remove_dests ds`] \\ fs []
  \\ qspecl_then [`ds`,`[x3]`] mp_tac remove_dests_obeys_max_app
  \\ fs [EVERY_remove_dests_sing]
QED

Theorem every_Fn_SOME_labs:
   !xs.
      every_Fn_SOME (MAP (SND o SND) xs) ==>
      every_Fn_SOME (MAP (SND ∘ SND) (clos_labels$compile xs))
Proof
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs [] \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
  \\ rename [`remove_dests ds`] \\ fs []
  \\ Induct_on `xs` \\ fs []
  \\ once_rewrite_tac [closPropsTheory.every_Fn_SOME_APPEND
      |> Q.INST [`l1`|->`x::[]`] |> SIMP_RULE std_ss [APPEND]]
  \\ fs [] \\ rw []
QED

(*

Theorem remove_fvs_set_globals[simp]:
   ∀fvs x. MAP set_globals (remove_fvs fvs x) = MAP set_globals x
Proof
  recInduct remove_fvs_ind
  \\ rw[remove_fvs_def] \\ fs[]
  \\ simp[elist_globals_FOLDR]
  >- EVAL_TAC
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
  \\ rw[] \\ res_tac \\ fs[]
QED

Theorem set_globals_HD_remove_fvs_SING[simp]:
   set_globals (HD (remove_fvs fvs [x])) = set_globals x
Proof
  strip_assume_tac(SPEC_ALL remove_fvs_SING)
  \\ first_assum(mp_tac o Q.AP_TERM`MAP set_globals`)
  \\ rw[]
QED

Theorem remove_fvs_esgc_free[simp]:
   ∀fvs x. EVERY (esgc_free) (remove_fvs fvs x) ⇔ EVERY esgc_free x
Proof
  recInduct remove_fvs_ind
  \\ rw[remove_fvs_def, EVERY_remove_fvs_SING]
  \\ simp[elist_globals_FOLDR]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, o_DEF, UNCURRY]
QED

Theorem remove_fvs_elist_globals[simp]:
   elist_globals (remove_fvs fvs xs) = elist_globals xs
Proof
  rw[elist_globals_FOLDR]
QED

*)

val _ = export_theory();
