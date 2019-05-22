(*
  Correctness proof for clos_fvs
*)
open preamble closLangTheory clos_fvsTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_fvsProof";

Theorem LENGTH_remove_fvs:
   !fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs
Proof
  recInduct remove_fvs_ind \\ simp [remove_fvs_def] \\ rw []
QED

Theorem remove_fvs_SING:
   !x. ?y. remove_fvs fvs [x] = [y]
Proof
  Induct \\ fs [remove_fvs_def] \\ rw[]
QED

Theorem HD_remove_fvs_SING[simp]:
   !x. [HD (remove_fvs fvs [x])] = remove_fvs fvs [x]
Proof
  strip_tac \\ strip_assume_tac (Q.SPEC `x` remove_fvs_SING) \\ simp []
QED

Theorem EVERY_remove_fvs_SING:
   EVERY P (remove_fvs fvs [x]) ⇔ P (HD (remove_fvs fvs [x]))
Proof
  strip_assume_tac(SPEC_ALL remove_fvs_SING) \\ rw[]
QED

val code_rel_def = Define `
  code_rel fvs e1 e2 <=>
    e2 = remove_fvs fvs e1`;

Theorem code_rel_IMP_LENGTH:
   !xs ys. code_rel fvs xs ys ==> LENGTH xs = LENGTH ys
Proof
  fs [code_rel_def, LENGTH_remove_fvs]
QED

Theorem code_rel_CONS_CONS:
   code_rel fvs (x1::x2::xs) (y1::y2::ys) ==>
      code_rel fvs [x1] [y1] /\ code_rel fvs (x2::xs) (y2::ys)
Proof
  simp [code_rel_def, remove_fvs_def]
QED

(* value relation *)

val f_rel_def = Define `
  f_rel fvs (a1, e1) (a2, e2) <=>
     a1 = a2 /\ code_rel (a1+fvs) [e1] [e2]`;

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
     code_rel (LENGTH env1 + num_args) [e1] [e2] ==>
       v_rel (Closure loc args1 env1 num_args e1) (Closure loc args2 env2 num_args e2)) /\
  (!loc args1 args2 env1 env2 k.
     LIST_REL v_rel env1 env2 /\
     LIST_REL v_rel args1 args2 /\
     LIST_REL (f_rel (LENGTH env1 + LENGTH funs1)) funs1 funs2 ==>
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

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL v_rel xs ys ==>
    ref_rel (ValueArray xs) (ValueArray ys))`

val compile_inc_def = Define `
  compile_inc (e, xs) = (clos_fvs$compile e, [])`;

val state_rel_def = Define `
  state_rel (s:('c, 'ffi) closSem$state) (t:('c, 'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    t.max_app = s.max_app /\ 1 <= s.max_app /\
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL v_rel) s.globals t.globals /\
    fmap_rel ref_rel s.refs t.refs /\
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

Theorem lookup_vars_lemma:
   !vs env1 env2. LIST_REL v_rel env1 env2 ==>
    case lookup_vars vs env1 of
      | NONE => lookup_vars vs env2 = NONE
      | SOME l1 => ?l2. LIST_REL v_rel l1 l2 /\ lookup_vars vs env2 = SOME l2
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

Theorem find_code_lemma:
   !s t p args. state_rel s t ==>
      find_code p args s.code = NONE /\
      find_code p args t.code = NONE
Proof
  fs [state_rel_def, find_code_def]
QED

Theorem dest_closure_SOME_IMP:
   dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)
Proof
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []
QED

Theorem dest_closure_SOME_Full_app:
   v_rel f1 f2 /\ v_rel a1 a2 /\ LIST_REL v_rel args1 args2 /\
    dest_closure max_app loc_opt f1 (a1::args1) = SOME (Full_app exp1 env1 rest_args1) ==>
      ?exp2 env2 rest_args2.
      code_rel (LENGTH env1) [exp1] [exp2] /\
      LIST_REL v_rel env1 env2 /\
      LIST_REL v_rel rest_args1 rest_args2 /\
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
  ``state_rel s t /\ LIST_REL v_rel xs ys ==>
    case do_app opp xs s of
      | Rerr err1 => ?err2. do_app opp ys t = Rerr err2 /\
                            exc_rel v_rel err1 err2
      | Rval (x, s1) => ?y t1. v_rel x y /\ state_rel s1 t1 /\
                               do_app opp ys t = Rval (y, t1)``,
  match_mp_tac simple_val_rel_do_app
  \\ conj_tac THEN1 (fs [simple_val_rel_def] \\ rw [] \\ fs [v_rel_cases])
  \\ fs [simple_state_rel_def, state_rel_def]
  \\ rw [] \\ fs [fmap_rel_def, FLOOKUP_DEF] \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);

(* evaluate level correctness *)

Theorem evaluate_remove_fvs:
   (!xs env1 (s1:('c,'ffi) closSem$state) res1 s2 ys env2 t1.
      evaluate (xs, env1, s1) = (res1, s2) /\
      LIST_REL v_rel env1 env2 /\ state_rel s1 t1 /\
      code_rel (LENGTH env1) xs ys ==>
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
        state_rel s2 t2)
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
    \\ reverse (fs [case_eq_thms, pair_case_eq])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [PULL_EXISTS] (* Closes Rerr *)
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ rveq \\ fs [] (* Closes Rval :: Rerr *)
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  \\ conj_tac THEN1 (* Var *) (
    rw[evaluate_def, remove_fvs_def, code_rel_def]
    \\ res_tac \\ rfs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ simp[do_app_def])
  \\ conj_tac THEN1 (* If *)
   (rw [code_rel_def, remove_fvs_def] \\ rveq
    \\ fs [evaluate_def]
    \\ reverse (fs [case_eq_thms, pair_case_eq])
    \\ rveq \\ fsrw_tac[DNF_ss] [PULL_EXISTS]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac
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
  \\ conj_tac THEN1 (* Let *)
   (fs [code_rel_def, remove_fvs_def]
    \\ rw[evaluate_def]
    \\ fsrw_tac[DNF_ss][CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt(disch_then drule \\ fs[])
    \\ strip_tac \\ fs[]
    \\ fsrw_tac[DNF_ss][case_eq_thms] \\ rveq \\ fs[LENGTH_remove_fvs]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[]
    \\ first_x_assum irule \\ simp[]
    \\ irule EVERY2_APPEND_suff \\ fs[])
  \\ conj_tac THEN1 (* Raise *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [])
  \\ conj_tac THEN1 (* Handle *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac \\ fs []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ fsrw_tac[DNF_ss][ADD1])
  \\ conj_tac THEN1 (* Op *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [pair_case_eq]
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
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs []
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ fs [Once case_eq_thms] \\ rveq \\ fs[]
    THEN1 (fs [code_rel_def])
    \\ drule (Q.SPEC `vs` lookup_vars_lemma)
    \\ CASE_TAC \\ strip_tac
    \\ fs [] \\ rveq \\ fs [code_rel_def]
    \\ imp_res_tac lookup_vars_SOME \\ fs[])
  \\ conj_tac THEN1 (* Letrec *)
   (rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ `t1.max_app = s1.max_app` by fs [state_rel_def]
    \\ fs[code_rel_def, remove_fvs_def] \\ rveq
    \\ fs[evaluate_def, EVERY_MAP, LAMBDA_PROD]
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      fs[CaseEq"bool"] \\ rveq \\ fs[]
      \\ fs[EVERY_MEM, EXISTS_MEM]
      \\ res_tac \\ fs[] )
    \\ fs[CaseEq"option"] \\ rveq \\ fs[]
    >- (
      imp_res_tac lookup_vars_lemma
      \\ pop_assum(qspec_then`names`mp_tac)
      \\ simp[] )
    >- (
      first_x_assum irule \\ simp[]
      \\ irule EVERY2_APPEND_suff \\ fs[]
      \\ fs[LIST_REL_GENLIST]
      \\ fs[LIST_REL_EL_EQN, EL_MAP]
      \\ rw[]
      \\ pairarg_tac \\ fs[f_rel_def]
      \\ fs[code_rel_def] )
    >- (
      imp_res_tac lookup_vars_lemma
      \\ pop_assum(qspec_then`names`mp_tac)
      \\ simp[] \\ strip_tac \\ fs[]
      \\ imp_res_tac lookup_vars_SOME \\ fs[]
      \\ first_x_assum irule \\ simp[]
      \\ irule EVERY2_APPEND_suff \\ fs[]
      \\ fs[LIST_REL_GENLIST]
      \\ fs[LIST_REL_EL_EQN, EL_MAP]
      \\ rw[]
      \\ pairarg_tac \\ fs[f_rel_def]
      \\ fs[code_rel_def] ))
  \\ conj_tac THEN1 (* App *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [LENGTH_remove_fvs]
    \\ fs[CaseEq"prod"]
    \\ first_x_assum drule
    \\ rpt(disch_then drule) \\ rw[]
    \\ fs[case_eq_thms, PULL_EXISTS, CaseEq"prod"] \\ rveq \\ fs[]
    \\ fsrw_tac[DNF_ss][]
    \\ first_x_assum drule
    \\ rpt(disch_then drule) \\ rw[]
    \\ imp_res_tac evaluate_SING \\ fs[])
  \\ conj_tac THEN1 (* Tick *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ fs [dec_clock_def, state_rel_def])
  \\ conj_tac THEN1 (* Call *)
   (fs [code_rel_def, remove_fvs_def] \\ rveq
    \\ rw [evaluate_def]
    \\ fs [Once case_eq_thms, pair_case_eq]
    \\ rveq \\ fsrw_tac[DNF_ss][]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq
    \\ fs [state_rel_def, find_code_def]
    \\ rveq \\ fs [])
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
  \\ qpat_x_assum `v_rel f1 f2` assume_tac
  \\ drule (GEN_ALL dest_closure_SOME_Full_app)
  \\ pop_assum kall_tac
  \\ ntac 3 (disch_then drule)
  \\ strip_tac \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ `s1.clock = t1.clock` by fs [state_rel_def]
  \\ rw[evaluate_def] \\ fs[] \\ rveq \\ fs[]
  THEN1 fs [state_rel_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac `evaluate (xxx2, _, sss2)`
  \\ disch_then (qspecl_then [`xxx2`, `sss2`] mp_tac)
  \\ unabbrev_all_tac \\ simp []
  \\ impl_tac THEN1 fs [dec_clock_def, state_rel_def]
  \\ strip_tac \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []
QED

Theorem remove_fvs_correct:
   !xs env1 (s1:('c,'ffi) closSem$state) res1 s2 env2 t1.
       evaluate (xs, env1, s1) = (res1, s2) /\
       LIST_REL v_rel env1 env2 /\ state_rel s1 t1 ==>
       ?res2 t2.
         evaluate (remove_fvs (LENGTH env1) xs, env2, t1) = (res2, t2) /\
         result_rel (LIST_REL v_rel) v_rel res1 res2 /\
         state_rel s2 t2
Proof
  rpt strip_tac \\ drule (CONJUNCT1 evaluate_remove_fvs) \\ simp [code_rel_def]
QED

(* preservation of observational semantics *)

Theorem semantics_compile:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc compile_inc cc) xs <> Fail ==>
   (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (pure_co compile_inc o co) cc (clos_fvs$compile xs) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc compile_inc cc) xs
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule remove_fvs_correct
  \\ simp []
  \\ disch_then (qspec_then `initial_state ffi max_app FEMPTY
                               (pure_co compile_inc o co) cc k` mp_tac)
  \\ impl_tac
  THEN1 fs [state_rel_def, initial_state_def]
  \\ fs[compile_def]
  \\ strip_tac
  \\ qexists_tac `0` \\ simp []
  \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []
QED

(* syntactic properties *)

Theorem code_locs_remove_fvs[simp]:
   !fvs xs. code_locs (remove_fvs fvs xs) = code_locs xs
Proof
  ho_match_mp_tac remove_fvs_ind \\ rw []
  \\ fs [code_locs_def,remove_fvs_def]
  THEN1
   (`?y. remove_fvs fvs [x] = [y]` by metis_tac [remove_fvs_SING]
    \\ fs [] \\ simp [Once code_locs_cons])
  THEN1 (every_case_tac \\ fs [code_locs_def] )
  \\ fs[code_locs_map]
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
QED

Theorem fv_max_remove_fvs:
   ∀fvs xs.
    every_Fn_vs_NONE xs ⇒
    (∀v. fv v (remove_fvs fvs xs) ⇒ v < fvs)
Proof
  recInduct remove_fvs_ind
  \\ rw[remove_fvs_def] \\ fs[fv1_thm]
  \\ full_simp_tac std_ss [fv1_def, HD_remove_fvs_SING]
  \\ fs[LENGTH_remove_fvs]
  \\ res_tac \\ fs[]
  \\ fs[EXISTS_MAP, EXISTS_MEM]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ full_simp_tac std_ss [fv1_def, HD_remove_fvs_SING]
  \\ first_x_assum drule
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ impl_tac
  >- (
    fs[Q.SPEC`MAP SND _`every_Fn_vs_NONE_EVERY]
    \\ fs[EVERY_MAP, LAMBDA_PROD]
    \\ fs[EVERY_MEM, FORALL_PROD]
    \\ res_tac )
  \\ rw[]
QED

Theorem remove_fvs_every_Fn_SOME[simp]:
   ∀fvs es. every_Fn_SOME (remove_fvs fvs es) ⇔ every_Fn_SOME es
Proof
  recInduct remove_fvs_ind
  \\ rw[remove_fvs_def]
  >- (
    fs[Once every_Fn_SOME_EVERY]
    \\ metis_tac[every_Fn_SOME_EVERY] )
  >- (
    simp[MAP_MAP_o,o_DEF,UNCURRY]
    \\ Cases_on`IS_SOME loc_opt` \\ fs[]
    \\ Cases_on`every_Fn_SOME [x1]` \\ fs[]
    \\ simp[Once every_Fn_SOME_EVERY]
    \\ fs[EVERY_MEM,UNCURRY,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ simp[Once every_Fn_SOME_EVERY, SimpRHS]
    \\ simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ metis_tac[])
QED

Theorem remove_fvs_every_Fn_vs_NONE[simp]:
   ∀fvs es. every_Fn_vs_NONE (remove_fvs fvs es) ⇔ every_Fn_vs_NONE es
Proof
  recInduct remove_fvs_ind
  \\ rw[remove_fvs_def]
  >- (
    fs[Once every_Fn_vs_NONE_EVERY]
    \\ metis_tac[every_Fn_vs_NONE_EVERY] )
  >- (
    simp[MAP_MAP_o,o_DEF,UNCURRY]
    \\ Cases_on`IS_SOME loc_opt` \\ fs[]
    \\ Cases_on`every_Fn_vs_NONE [x1]` \\ fs[]
    \\ simp[Once every_Fn_vs_NONE_EVERY]
    \\ fs[EVERY_MEM,UNCURRY,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ simp[Once every_Fn_vs_NONE_EVERY, SimpRHS]
    \\ simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ metis_tac[])
QED

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

Theorem EVERY_remove_fvs_sing:
   EVERY f (remove_fvs n [y]) <=> f (HD (remove_fvs n [y]))
Proof
  `?t. remove_fvs n [y] = [t]` by metis_tac [remove_fvs_SING] \\ fs []
QED

Theorem remove_fvs_no_Labels:
   !n xs. EVERY no_Labels (remove_fvs n xs) = EVERY no_Labels xs
Proof
  ho_match_mp_tac remove_fvs_ind \\ rw [remove_fvs_def]
  \\ fs [EVERY_remove_fvs_sing]
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ res_tac
QED

Theorem remove_fvs_obeys_max_app:
   !n xs. EVERY (obeys_max_app k) (remove_fvs n xs) = EVERY (obeys_max_app k) xs
Proof
  ho_match_mp_tac remove_fvs_ind \\ rw [remove_fvs_def]
  \\ fs [EVERY_remove_fvs_sing]
  \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS,LENGTH_remove_fvs]
  \\ rw [] \\ eq_tac \\ rw [] \\ res_tac
QED

Theorem get_code_labels_remove_fvs[simp]:
   ∀n es. MAP get_code_labels (remove_fvs n es) = MAP get_code_labels es
Proof
  recInduct clos_fvsTheory.remove_fvs_ind
  \\ rw[clos_fvsTheory.remove_fvs_def] \\ fs[closLangTheory.assign_get_code_label_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
  \\ rw[]
  \\ first_x_assum drule
  \\ rw[] \\ fs[]
QED

val _ = export_theory();
