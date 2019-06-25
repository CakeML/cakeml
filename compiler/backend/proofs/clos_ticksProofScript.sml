(*
  Correctness proof for clos_ticks
*)
open preamble closPropsTheory clos_ticksTheory closSemTheory;
open closLangTheory;
open backendPropsTheory;

val qexistsl_tac = map_every qexists_tac;
fun bump_assum pat = qpat_x_assum pat assume_tac;

val _ = new_theory "clos_ticksProof";

val _ = temp_overload_on("remove_ticks",``clos_ticks$remove_ticks``);

Theorem remove_ticks_IMP_LENGTH:
   !(es:closLang$exp list) xs. xs = remove_ticks es ==> LENGTH es = LENGTH xs
Proof
  fs [LENGTH_remove_ticks]
QED

Theorem remove_ticks_SING:
   !e. ?e'. remove_ticks [e] = [e']
Proof
  Induct \\ fs [remove_ticks_def]
QED

Theorem HD_remove_ticks_SING[simp]:
   !x. [HD (remove_ticks [x])] = remove_ticks [x] ∧
       LENGTH (remove_ticks [x]) = 1
Proof
  gen_tac \\ strip_assume_tac (Q.SPEC `x` remove_ticks_SING) \\ fs []
QED

(* code relation *)

val code_rel_def = Define `
  code_rel e1 e2 <=>
    e2 = remove_ticks e1`;

Theorem code_rel_IMP_LENGTH:
   !xs ys. code_rel xs ys ==> LENGTH xs = LENGTH ys
Proof
  fs [code_rel_def, LENGTH_remove_ticks]
QED

Theorem remove_ticks_CONS:
   !es e. remove_ticks (e::es) = HD (remove_ticks [e])::remove_ticks es
Proof
  Induct_on `es` \\ Induct_on `e` \\ fs [remove_ticks_def]
QED

Theorem code_rel_CONS_CONS:
   !x1 x2 xs y1 y2 ys. code_rel (x1::x2::xs) (y1::y2::ys) <=>
                        code_rel [x1] [y1] /\ code_rel (x2::xs) (y2::ys)
Proof
  fs [code_rel_def]
  \\ rpt strip_tac
  \\ `?t1. remove_ticks [x1] = [t1]` by metis_tac [remove_ticks_SING]
  \\ `?t2. remove_ticks [x2] = [t2]` by metis_tac [remove_ticks_SING]
  \\ rw [remove_ticks_CONS]
QED

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
  compile_inc (e, xs) = (remove_ticks e, [])`;

val state_rel_def = Define `
  state_rel (s:('c, 'ffi) closSem$state) (t:('c, 'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    t.max_app = s.max_app /\ 1 <= s.max_app /\
    t.clock = s.clock /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL v_rel) s.globals t.globals /\
    FMAP_REL ref_rel s.refs t.refs /\
    s.compile = pure_cc compile_inc t.compile /\
    t.compile_oracle = pure_co compile_inc o s.compile_oracle`;

(* eval remove ticks *)

val mk_Ticks_def = Define `
  (mk_Ticks [] (e : closLang$exp) = e) /\
  (mk_Ticks (t::tr) e = Tick t (mk_Ticks tr e))`;

Theorem remove_ticks_Tick:
   !x t e. ~([Tick t e] = remove_ticks [x])
Proof
  Induct \\ fs [remove_ticks_def]
QED

Theorem remove_ticks_Var_IMP_mk_Ticks:
   (!x tr n. [Var tr n] = remove_ticks [x] ==> ?ts. x = mk_Ticks ts (Var tr n))
Proof
  Induct \\ fs [remove_ticks_def] \\ metis_tac [mk_Ticks_def]
QED

Theorem remove_ticks_If_IMP_mk_Ticks:
   !x tr e1' e2' e3'.
      [If tr e1' e2' e3'] = remove_ticks [x] ==>
        ?ts e1 e2 e3. x = mk_Ticks ts (If tr e1 e2 e3) /\
                      e1' = HD (remove_ticks [e1]) /\
                      e2' = HD (remove_ticks [e2]) /\
                      e3' = HD (remove_ticks [e3])
Proof
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexists_tac `t::ts` \\ metis_tac [mk_Ticks_def]
QED

Theorem remove_ticks_Let_IMP_mk_Ticks:
   !x t l e. [Let t l e] = remove_ticks [x] ==>
              (?ts l' e'. x = mk_Ticks ts (Let t l' e') /\
               l = remove_ticks l' /\
               [e] = remove_ticks [e'])
Proof
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac  \\ qexistsl_tac [`t::ts`, `l'`, `e'`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Raise_IMP_mk_Ticks:
   !x t e. [Raise t e] = remove_ticks [x] ==>
            (?ts e'. x = mk_Ticks ts (Raise t e') /\ [e] = remove_ticks [e'])
Proof
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e'`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Handle_IMP_mk_Ticks:
   !x t e1' e2'. [Handle t e1' e2'] = remove_ticks [x] ==>
                  (?ts e1 e2. x = mk_Ticks ts (Handle t e1 e2) /\
                   [e1'] = remove_ticks [e1] /\ [e2'] = remove_ticks [e2])
Proof
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e1`, `e2`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Op_IMP_mk_Ticks:
   !x tr op es'. [Op tr op es'] = remove_ticks [x] ==>
      ?ts es. x = mk_Ticks ts (Op tr op es) /\ es' = remove_ticks es
Proof
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `es`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Fn_IMP_mk_Ticks:
   !x tr loc vsopt num_args e'.
      [Fn tr loc vsopt num_args e'] = remove_ticks [x] ==>
        ?ts e. x = mk_Ticks ts (Fn tr loc vsopt num_args e) /\ [e'] = remove_ticks [e]
Proof
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Letrec_IMP_mk_Ticks:
   !x tr loc vsopt fns' e'.
      [Letrec tr loc vsopt fns' e'] = remove_ticks [x] ==>
        ?ts fns e. x = mk_Ticks ts (Letrec tr loc vsopt fns e) /\
                   e' = HD (remove_ticks [e]) /\
                   fns' = MAP (\(num_args, x). (num_args, HD (remove_ticks [x]))) fns
Proof
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `fns`, `e`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_App_IMP_mk_Ticks:
   !x tr loc_opt e1' es'.
      [App tr loc_opt e1' es'] = remove_ticks [x] ==>
        ?ts e1 es. x = mk_Ticks ts (App tr loc_opt e1 es) /\
                   e1' = HD (remove_ticks [e1]) /\
                   es' = remove_ticks es
Proof
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e1`, `es`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_Call_IMP_mk_Ticks:
   !x tr ticks' dest es'. [Call tr ticks' dest es'] = remove_ticks [x] ==>
      ticks' = 0 /\
      ?ts ticks es. x = mk_Ticks ts (Call tr ticks dest es) /\
                    es' = remove_ticks es
Proof
  reverse (Induct \\ rw [remove_ticks_def])
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ rpt strip_tac \\ res_tac
  \\ qexistsl_tac [`t::ts`, `ticks`, `es`] \\ fs [mk_Ticks_def]
QED

Theorem remove_ticks_mk_Ticks:
   !tr e. remove_ticks [mk_Ticks tr e] = remove_ticks [e]
Proof
  Induct_on `tr` \\ fs [mk_Ticks_def, remove_ticks_def]
QED

Theorem evaluate_mk_Ticks:
   !tr e env s1.
      evaluate ([mk_Ticks tr e], env, s1) =
        if s1.clock < LENGTH tr then (Rerr (Rabort Rtimeout_error), s1 with clock := 0)
                                else evaluate ([e], env, dec_clock (LENGTH tr) s1)
Proof
  Induct THEN1 simp [mk_Ticks_def, dec_clock_def]
  \\ rw []
  \\ fs [mk_Ticks_def, evaluate_def, dec_clock_def]
  THEN1 (IF_CASES_TAC \\ simp [state_component_equality])
  \\ fs [ADD1]
QED

val do_app_lemma = prove(
  ``state_rel s t /\ LIST_REL v_rel xs ys ==>
    case do_app opp ys t of
      | Rerr err2 => ?err1. do_app opp xs s = Rerr err1 /\
                            exc_rel v_rel err1 err2
      | Rval (y, t1) => ?x s1. v_rel x y /\ state_rel s1 t1 /\
                               do_app opp xs s = Rval (x, s1)``,
  match_mp_tac simple_val_rel_do_app_rev
  \\ conj_tac THEN1 (fs [simple_val_rel_def] \\ rw [] \\ fs [])
  \\ fs [simple_state_rel_def, state_rel_def]
  \\ rw []
  \\ fs [FMAP_REL_def, FLOOKUP_DEF]
  \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);

Theorem lookup_vars_lemma:
   !vs env1 env2. LIST_REL v_rel env1 env2 ==>
    case lookup_vars vs env2 of
      | NONE => lookup_vars vs env1 = NONE
      | SOME l2 => ?l1. LIST_REL v_rel l1 l2 /\ lookup_vars vs env1 = SOME l1
Proof
  Induct_on `vs` \\ fs [lookup_vars_def]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw []
  \\ res_tac
  \\ Cases_on `lookup_vars vs env2`
  \\ fs []
  \\ fs [LIST_REL_EL_EQN]
QED

Theorem state_rel_IMP_max_app_EQ:
   !s t. state_rel s t ==> s.max_app = t.max_app
Proof
  fs [state_rel_def]
QED

val state_rel_IMP_code_FEMPTY = prove(
  ``!s t. state_rel s t ==> s.code = FEMPTY /\ t.code = FEMPTY``,
  fs [state_rel_def]);

Theorem state_rel_clock:
   !s t k. state_rel (s with clock := k) (t with clock := k) <=> state_rel s (t with clock := s.clock)
Proof
  rw [] \\ eq_tac \\ rw [state_rel_def]
QED


Theorem dest_closure_SOME_IMP:
   dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)
Proof
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []
QED

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!y x.
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
  ``!y x.
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


Theorem evaluate_remove_ticks:
   (!ys env2 (t1:('c,'ffi) closSem$state) res2 t2 env1 s1 xs.
     (evaluate (ys,env2,t1) = (res2,t2)) /\
     LIST_REL v_rel env1 env2 /\
     state_rel s1 t1 /\ code_rel xs ys ==>
     ?ck res1 s2.
        (evaluate (xs,env1,s1 with clock := s1.clock + ck) = (res1,s2)) /\
        result_rel (LIST_REL v_rel) v_rel res1 res2 /\
        state_rel s2 t2) /\
   (!loc_opt f2 args2 (t1:('c,'ffi) closSem$state) res2 t2 f1 args1 s1.
     (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\
     v_rel f1 f2 /\ LIST_REL v_rel args1 args2 /\
     state_rel s1 t1 ==>
     ?ck res1 s2.
       (evaluate_app loc_opt f1 args1 (s1 with clock := s1.clock + ck) = (res1,s2)) /\
       result_rel (LIST_REL v_rel) v_rel res1 res2 /\
       state_rel s2 t2)
Proof
  (**)
  ho_match_mp_tac (evaluate_ind |> Q.SPEC `λ(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac
  \\ TRY (drule code_rel_IMP_LENGTH \\ strip_tac)
  THEN1 (* NIL *)
   (fs [evaluate_def] \\ rveq \\ qexists_tac `0` \\ fs[])
  THEN1 (* CONS *)
   (fs [LENGTH_EQ_NUM] \\ rveq
    \\ fs [evaluate_def]
    \\ reverse (fs [closSemTheory.case_eq_thms, pair_case_eq])
    \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs [code_rel_CONS_CONS]
    \\ disch_then drule \\ disch_then drule \\ strip_tac \\ fs []
    THEN1 (qexists_tac `ck` \\ fs[])
    \\ Cases_on `res1` \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ disch_then drule \\ strip_tac \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ qexists_tac `ck + ck'` \\ fs []
    \\ bump_assum `evaluate ([h], env1, _) = _`
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then kall_tac
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  THEN1 (* Var *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Var_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ qexists_tac `LENGTH ts`
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  THEN1 (* If *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_If_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks]
    \\ fs [evaluate_def]
    \\ simp [dec_clock_def]
    \\ fs [pair_case_eq] \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e1]`) \\ simp []
    \\ strip_tac
    \\ reverse (fs [case_eq_thms] \\ rveq \\ Cases_on `res1` \\ fs [])
    THEN1 (qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
    \\ `(Boolv T = y <=> Boolv T = r1) /\
        (Boolv F = y <=> Boolv F = r1)` by
     (qpat_x_assum `v_rel _ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp [EVAL ``closSem$Boolv T``,EVAL ``closSem$Boolv F``]
      \\ rw [] \\ eq_tac \\ rw []
      \\ rpt (pop_assum mp_tac)
      \\ simp [Once v_rel_cases])
    \\ ntac 2 (pop_assum (fn th => fs [th]))
    \\ reverse (Cases_on `Boolv T = r1 \/ Boolv F = r1`) \\ fs [] \\ rveq \\ fs []
    THEN1 (qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ TRY (rename1 `evaluate (remove_ticks [e_taken_branch], env2, _) = (res2, t2)`)
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `[e_taken_branch]` mp_tac) \\ fs []
    \\ strip_tac
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ qexists_tac `ck + ck' + LENGTH ts` \\ fs []
    \\ bump_assum `evaluate ([e1], _, _) = _`
    \\ drule evaluate_add_clock \\ fs [])
  THEN1 (* Let *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Let_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks]
    \\ fs [remove_ticks_def]
    \\ simp [evaluate_mk_Ticks]
    \\ fs [evaluate_def]
    \\ simp [dec_clock_def]
    \\ Cases_on `evaluate (remove_ticks l', env2, t1')`
    \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `l'`)
    \\ fs [] \\ strip_tac
    \\ reverse (Cases_on `q`) THEN1 (qexists_tac `ck + LENGTH ts` \\ fs [] \\ rw [])
    \\ fs []
    \\ Cases_on `res1` \\ fs []
    \\ drule (GEN_ALL EVERY2_APPEND_suff)
    \\ bump_assum `LIST_REL v_rel env1 env2`
    \\ disch_then drule
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e']`)
    \\ fs [] \\ strip_tac
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ qexists_tac `ck + ck' + LENGTH ts` \\ fs []
    \\ bump_assum `evaluate (l', env1, _) = _`
    \\ drule evaluate_add_clock \\ fs [])
  THEN1 (* Raise *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Raise_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ fs [pair_case_eq] \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e']`)
    \\ fs [] \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq
    \\ Cases_on `res1` \\ fs []
    \\ qexists_tac `ck + LENGTH ts`
    \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq
    \\ fs [LIST_REL_EL_EQN])
  THEN1 (* Handle *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Handle_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ fs [pair_case_eq] \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e1]`)
    \\ fs [] \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ Cases_on `res1` \\ fs []
    (* Close the Rval and Rerr Rabort cases using TRY *)
    \\ TRY (qexists_tac `ck + LENGTH ts` THEN1 fs [])
    \\ qpat_x_assum `!x. _` mp_tac
    \\ disch_then (mp_tac o Q.SPEC `v'::env1`) \\ fs []
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e2]`) \\ fs []
    \\ strip_tac
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ qexists_tac `ck + ck' + LENGTH ts` \\ fs []
    \\ bump_assum `evaluate ([e1], _m _) = _`
    \\ drule evaluate_add_clock \\ fs [])
 THEN1 (* Op *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Op_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ fs [pair_case_eq] \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `es`) \\ simp []
    \\ strip_tac
    \\ reverse (fs [case_eq_thms]) \\ rveq
    \\ Cases_on `res1` \\ fs []
    THEN1 (qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ reverse (Cases_on `op = Install`) \\ fs [] \\ rveq
    THEN1 (* op /= Install *)
     (fs [case_eq_thms] \\ rw []
      \\ qexists_tac `ck + LENGTH ts` \\ fs []
      \\ drule (GEN_ALL do_app_lemma)
      \\ drule EVERY2_REVERSE \\ strip_tac
      \\ disch_then drule
      \\ disch_then (assume_tac o Q.SPEC `op`)
      \\ rfs []
      \\ PairCases_on `v1`
      \\ fs []
      \\ metis_tac [])
    \\ qexists_tac`ck + LENGTH ts` \\ rw[]
    (*
    (* op = Install *)
    \\ qpat_x_assum `_ = (res2, t2)` mp_tac
    \\ simp [Once do_install_def]
    \\ drule EVERY2_REVERSE
    \\ qabbrev_tac `a1 = REVERSE a`
    \\ qabbrev_tac `v1 = REVERSE vs`
    \\ strip_tac
    \\ Cases_on `a1` \\ fs [] \\ rveq
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw [])
    \\ Cases_on `t` \\ fs [] \\ rveq
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw [])
    \\ reverse (Cases_on `t'`) \\ fs [] \\ rveq
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw [])
    \\ rename1 `v_rel x2 y2` \\ pop_assum mp_tac
    \\ drule v_rel_IMP_v_to_bytes \\ strip_tac
    \\ rename1 `v_rel x1 y1` \\ strip_tac
    \\ drule v_rel_IMP_v_to_words \\ strip_tac \\ fs []
    \\ Cases_on `v_to_bytes x1` \\ fs []
    THEN1 (fs [do_install_def] \\ rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ Cases_on `v_to_words x2` \\ fs []
    THEN1 (fs [do_install_def] \\ rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ pairarg_tac \\ fs []
    \\ PairCases_on `progs`
    \\ Cases_on `s2.compile_oracle 0`
    \\ PairCases_on `r`
    \\ `r1 = [] /\ progs1 = []` by
       (fs [state_rel_def] \\ rfs [pure_co_def] \\ fs [compile_inc_def]
        \\ rveq \\ fs [] \\ metis_tac [SND])
    \\ rveq \\ fs []
    \\ Cases_on `s'.compile cfg (progs0,[])` \\ fs []
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw []
           \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
           \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def])
    \\ rename1 `_ = SOME xx` \\ PairCases_on `xx` \\ fs []
    \\ reverse IF_CASES_TAC
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw []
           \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
           \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def]
           \\ IF_CASES_TAC \\ fs [shift_seq_def]
           \\ metis_tac[LENGTH_remove_ticks, LENGTH_NIL])
    \\ IF_CASES_TAC
    THEN1 (rw [] \\ qexists_tac `ck + LENGTH ts` \\ fs [do_install_def] \\ rw []
           \\ fs [state_rel_def,pure_cc_def,compile_inc_def]
           \\ rfs [] \\ fs [] \\ rfs [pure_co_def,compile_inc_def]
           \\ IF_CASES_TAC \\ fs [shift_seq_def]
           \\ fs [FUPDATE_LIST, o_DEF]
           \\ metis_tac[LENGTH_remove_ticks, LENGTH_NIL])
    \\ fs [] \\ rveq \\ fs []
    \\ strip_tac
    \\ qpat_x_assum `!x. _` mp_tac
    \\ simp [Once do_install_def]
    \\ fs[CaseEq"prod"]
    \\ disch_then (qspec_then `s2 with
                               <|clock := s'.clock − 1;
                                 compile_oracle := (λi. s2.compile_oracle (i + 1));
                                 code := s2.code |++ []|>` mp_tac)
    \\ disch_then (qspec_then `r0` mp_tac)
    \\ impl_tac
    THEN1 (rfs [state_rel_def] \\ fs [pure_co_def, compile_inc_def]
           \\ rveq \\ fs [shift_seq_def, FUPDATE_LIST, o_DEF])
    \\ fs [] \\ strip_tac
    \\ qexists_tac `ck + ck' + LENGTH ts` \\ fs []
    \\ imp_res_tac evaluate_clock
    \\ bump_assum `evalulate (es, _, _) = _`
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then kall_tac
    \\ `s2.clock = s'.clock /\
        s2.compile = pure_cc compile_inc s'.compile /\
        s'.compile_oracle = pure_co compile_inc ∘ s2.compile_oracle`
          by fs [state_rel_def]
    \\ fs [do_install_def]
    \\ fs [pure_cc_def,compile_inc_def,pure_co_def,shift_seq_def]
    \\ reverse IF_CASES_TAC >- metis_tac[LENGTH_remove_ticks, LENGTH_NIL]
    \\ fs[]
    \\ rveq
    \\ CASE_TAC \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ Q.ISPEC_THEN`a'`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[LIST_REL_SNOC]
    *)
    )
  THEN1 (* Fn *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Fn_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ qexists_tac `LENGTH ts` \\ fs []
    \\ imp_res_tac state_rel_IMP_max_app_EQ \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `vsopt` \\ fs [] \\ rveq \\ fs []
    \\ drule (Q.SPEC `x` lookup_vars_lemma) \\ strip_tac
    \\ Cases_on `lookup_vars x env2` \\ fs [] \\ rveq \\ fs []
    \\ fs [code_rel_def])
  THEN1 (* Letrec *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Letrec_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ `EVERY (λ(num_args,e). num_args ≤ t1.max_app ∧ num_args ≠ 0)
             (MAP (λ(num_args,x). (num_args,HD (remove_ticks [x]))) fns') <=>
       EVERY (λ(num_args,e'). num_args ≤ s1.max_app ∧ num_args ≠ 0) fns'` by
     (imp_res_tac state_rel_IMP_max_app_EQ \\ fs []
      \\ rpt (pop_assum kall_tac)
      \\ eq_tac \\ spose_not_then strip_assume_tac
      \\ fs [EXISTS_MEM] \\ rename1 `MEM eee _`
      \\ TRY (CHANGED_TAC (fs [MEM_MAP]) \\ rename1 `MEM yyy _`)
      \\ fs [EVERY_MAP, EVERY_MEM]
      \\ res_tac
      \\ PairCases_on `eee`
      \\ TRY (PairCases_on `yyy`)
      \\ fs [])
    \\ pop_assum (fn (thm) => fs [thm])
    \\ qpat_x_assum `(if _ then _ else _) = _` mp_tac
    \\ reverse IF_CASES_TAC
    THEN1 (simp [] \\ strip_tac \\ rveq \\ qexists_tac `LENGTH ts` \\ fs [])
    \\ strip_tac \\ fs []
    \\ `!l1 l2. LIST_REL v_rel l1 l2 ==> LIST_REL v_rel
          (GENLIST (Recclosure loc [] l1 fns') (LENGTH fns') ++ env1)
          (GENLIST (Recclosure loc [] l2 (MAP (\(num_args, x).
                                                (num_args, HD (remove_ticks [x]))) fns'))
                   (LENGTH fns') ++ env2)` by
     (qpat_x_assum `LIST_REL _ _ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ rpt strip_tac
      \\ match_mp_tac (EVERY2_APPEND_suff) \\ fs []
      \\ fs [LIST_REL_GENLIST]
      \\ `LIST_REL f_rel fns' (MAP (λ(num_args,x). (num_args,HD (remove_ticks [x]))) fns')` by
         (Induct_on `fns'` \\ fs [] \\ Cases_on `h` \\ fs [f_rel_def, code_rel_def])
      \\ fs [])
    \\ fs [case_eq_thms] \\ fs [] \\ rveq \\ fs []
    THEN1
     (qexists_tac `LENGTH ts` \\ fs []
      \\ drule lookup_vars_lemma
      \\ disch_then (qspec_then `names` assume_tac) \\ rfs [])
    \\ drule lookup_vars_lemma
    \\ disch_then (qspec_then `names` assume_tac) \\ rfs []
    \\ first_x_assum drule \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `[e]` mp_tac) \\ fs []
    \\ strip_tac
    \\ qexists_tac `ck + LENGTH ts`
    \\ fs [])
  THEN1 (* App *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_App_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ fs [LENGTH_remove_ticks]
    \\ reverse (Cases_on `LENGTH es > 0`) \\ fs []
    THEN1 (qexists_tac `LENGTH ts` \\ rw [])
    \\ fs [pair_case_eq] \\ reverse (fs [case_eq_thms])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `es` mp_tac)
    \\ fs [] \\ strip_tac
    THEN1 (qexists_tac `ck + LENGTH ts` \\ fs [])
    \\ fs [pair_case_eq] \\ reverse (fs [case_eq_thms])
    \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `[e1]` mp_tac)
    \\ fs [] \\ strip_tac \\ rveq \\ fs []
    THEN1 (qexists_tac `ck + ck' + LENGTH ts` \\ fs []
           \\ imp_res_tac evaluate_clock
           \\ bump_assum `evaluate (es, _, _) = _`
           \\ drule evaluate_add_clock
           \\ Cases_on `res1` \\ fs [])
    \\ ntac 2 (rename1 `result_rel (LIST_REL v_rel) v_rel rrr (Rval _)`
               \\ Cases_on `rrr` \\ fs [])
    \\ imp_res_tac evaluate_SING \\ rveq
    \\ fs [LIST_REL_LENGTH] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ qexists_tac `ck + ck' + ck'' + LENGTH ts`
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ bump_assum `evaluate (es, _, _) = _`
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck' + ck''` assume_tac) \\ fs []
    \\ bump_assum `evaluate ([e1], _, _) = _`
    \\ drule evaluate_add_clock \\ fs [])
  THEN1 (* Tick *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ fs [remove_ticks_Tick])
  THEN1 (* Call *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ imp_res_tac remove_ticks_Call_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks, remove_ticks_def]
    \\ simp [evaluate_mk_Ticks, dec_clock_def]
    \\ fs [evaluate_def]
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ disch_then (qspec_then `es` mp_tac)
    \\ fs [] \\ strip_tac
    \\ qexists_tac `ck + LENGTH ts` \\ fs []
    \\ drule state_rel_IMP_code_FEMPTY \\ strip_tac
    \\ fs [find_code_def]
    \\ fs [case_eq_thms] \\ rveq
    \\ Cases_on `res1` \\ fs [])
  THEN1 (* evaluate_app NIL *)
   (fs [evaluate_def] \\ rw [] \\ qexists_tac `0` \\ fs [state_component_equality])
  (* evaluate_app CONS *)
  \\ fs [evaluate_def]
  \\ fs [dec_clock_def, ADD1]
  \\ imp_res_tac state_rel_IMP_max_app_EQ
  \\ fs [case_eq_thms] \\ fs [] \\ rveq
  THEN1 (* dest_closure returns NONE *)
   (qexists_tac `0` \\ simp []
    \\ fs [dest_closure_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
    \\ Cases_on `EL i fns` \\ fs []
    \\ Cases_on `EL i funs1` \\ fs []
    \\ Cases_on `i < LENGTH fns` \\ fs []
    \\ bump_assum `LIST_REL f_rel _ _`
    \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL)
    \\ fs [] \\ disch_then drule \\ fs [f_rel_def])
  THEN1 (* dest_closure returns Partial_app *)
   (imp_res_tac dest_closure_none_loc
    \\ `s1.clock = t1.clock` by fs [state_rel_def]
    \\ qexists_tac `0` \\ fs []
    \\ drule dest_closure_SOME_IMP \\ strip_tac
    \\ fs [dest_closure_def] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
    THEN1
     (IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq
      \\ fs [state_rel_def]
      \\ irule EVERY2_APPEND_suff \\ simp [])
    \\ Cases_on `EL i fns` \\ fs []
    \\ Cases_on `EL i funs1` \\ fs []
    \\ Cases_on `i < LENGTH fns` \\ fs []
    \\ bump_assum `LIST_REL f_rel _ _`
    \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ fs []
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ fs [f_rel_def] \\ rveq
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ fs [state_rel_def]
    \\ irule EVERY2_APPEND_suff \\ fs [])
  (* dest_closure returns Full_app *)
  \\ rename1 `LIST_REL v_rel xs ys`
  \\ rename1 `v_rel x y`
  \\ `s1.clock = t1.clock` by fs [state_rel_def]
  \\ Cases_on `t1.clock < SUC (LENGTH ys) − LENGTH rest_args` \\ fs []
  THEN1
   (rw []
    \\ imp_res_tac dest_closure_SOME_IMP \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ imp_res_tac state_rel_IMP_max_app_EQ
    \\ fs [dest_closure_def]
    \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
    \\ qexists_tac `0` \\ fs []
    THEN1
     (IF_CASES_TAC \\ fs [] \\ rveq
      \\ fs [LENGTH_REVERSE]
      \\ fs [state_rel_def])
    \\ Cases_on `EL i fns` \\ fs []
    \\ Cases_on `EL i funs1` \\ fs []
    \\ Cases_on `i < LENGTH fns` \\ fs []
    \\ bump_assum `LIST_REL f_rel _ _`
    \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ fs []
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ fs [f_rel_def] \\ rveq
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ fs [LENGTH_REVERSE]
    \\ fs [state_rel_def])
  \\ fs [pair_case_eq, case_eq_thms] \\ rveq \\ fs []
  THEN1
   (imp_res_tac dest_closure_SOME_IMP \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [dest_closure_def]
    \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
    THEN1
     (IF_CASES_TAC \\ fs [] \\ rveq
      \\ fs [LENGTH_REVERSE]
      \\ `LIST_REL v_rel
            (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE xs ++ [x])) ++ args1 ++ env1)
            (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE ys ++ [y])) ++ arg_env ++ clo_env )`
         by (ntac 2 (irule EVERY2_APPEND_suff \\ simp [])
             \\ irule EVERY2_TAKE
             \\ irule EVERY2_APPEND_suff \\ simp [])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `s1 with clock := LENGTH arg_env + t1.clock - num_args` mp_tac)
      \\ simp [state_rel_clock]
      \\ disch_then drule
      \\ strip_tac
      \\ Cases_on `res1` \\ fs [] \\ rveq
      \\ `LIST_REL v_rel (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE xs ++ [x])))
                         (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE ys ++ [y])))`
         by (irule EVERY2_REVERSE \\ irule EVERY2_DROP
             \\ irule EVERY2_APPEND_suff \\ simp [])
      \\ first_x_assum drule
      \\ ntac 2 (disch_then drule)
      \\ strip_tac
      \\ qexists_tac `ck + ck'`
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ drule evaluate_add_clock \\ fs [])
    \\ Cases_on `EL i fns` \\ fs []
    \\ Cases_on `EL i funs1` \\ fs []
    \\ Cases_on `i < LENGTH fns` \\ fs []
    \\ bump_assum `LIST_REL f_rel _ _`
    \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ fs []
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ fs [f_rel_def] \\ rveq
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ fs [LENGTH_REVERSE]
    \\ rename1 `EL i fns = (num_args, _)`
    \\ `LIST_REL v_rel (REVERSE (TAKE (num_args - LENGTH args1) (REVERSE xs ++ [x])) ++ args1
                        ++ GENLIST (Recclosure loc [] env1 funs1) (LENGTH funs1) ++ env1)
                       (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE ys ++ [y])) ++ arg_env
                        ++ GENLIST (Recclosure loc [] clo_env fns) (LENGTH fns) ++ clo_env)`
       by (irule EVERY2_APPEND_suff \\ simp []
           \\ irule EVERY2_APPEND_suff \\ reverse conj_tac THEN1 fs [LIST_REL_GENLIST]
           \\ irule EVERY2_APPEND_suff \\ simp []
           \\ irule EVERY2_TAKE
           \\ irule EVERY2_APPEND_suff \\ simp [])
    \\ first_x_assum drule
    \\ disch_then (qspec_then `s1 with clock := LENGTH arg_env + t1.clock - num_args` mp_tac)
    \\ simp [state_rel_clock]
    \\ disch_then drule
    \\ strip_tac
    \\ Cases_on `res1` \\ fs [] \\ rveq
    \\ `LIST_REL v_rel (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE xs ++ [x])))
                       (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE ys ++ [y])))`
       by (irule EVERY2_REVERSE \\ irule EVERY2_DROP
           \\ irule EVERY2_APPEND_suff \\ simp [])
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ qexists_tac `ck + ck'`
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ drule evaluate_add_clock \\ fs [])
  THEN (* Solves two subgoals *)
   (imp_res_tac dest_closure_SOME_IMP \\ fs [] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [dest_closure_def]
    \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
    THEN1
     (IF_CASES_TAC \\ fs [] \\ rveq
      \\ fs [LENGTH_REVERSE]
      \\ `LIST_REL v_rel
            (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE xs ++ [x])) ++ args1 ++ env1)
            (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE ys ++ [y])) ++ arg_env ++ clo_env )`
         by (ntac 2 (irule EVERY2_APPEND_suff \\ simp [])
             \\ irule EVERY2_TAKE
             \\ irule EVERY2_APPEND_suff \\ simp [])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `s1 with clock := LENGTH arg_env + t1.clock - num_args` mp_tac)
      \\ simp [state_rel_clock]
      \\ disch_then drule
      \\ strip_tac
      \\ Cases_on `res1` \\ fs [] \\ rveq
      \\ qexists_tac `ck` \\ fs [])
    THEN1
     (Cases_on `EL i fns` \\ fs []
      \\ Cases_on `EL i funs1` \\ fs []
      \\ Cases_on `i < LENGTH fns` \\ fs []
      \\ bump_assum `LIST_REL f_rel _ _`
      \\ drule (LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ fs []
      \\ disch_then drule \\ simp [] \\ strip_tac
      \\ fs [f_rel_def] \\ rveq
      \\ IF_CASES_TAC \\ fs [] \\ rveq
      \\ fs [LENGTH_REVERSE]
      \\ rename1 `EL i fns = (num_args, _)`
      \\ `LIST_REL v_rel (REVERSE (TAKE (num_args - LENGTH args1) (REVERSE xs ++ [x])) ++ args1
                          ++ GENLIST (Recclosure loc [] env1 funs1) (LENGTH funs1) ++ env1)
                         (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE ys ++ [y])) ++ arg_env
                          ++ GENLIST (Recclosure loc [] clo_env fns) (LENGTH fns) ++ clo_env)`
         by (irule EVERY2_APPEND_suff \\ simp []
             \\ irule EVERY2_APPEND_suff \\ reverse conj_tac THEN1 fs [LIST_REL_GENLIST]
             \\ irule EVERY2_APPEND_suff \\ simp []
             \\ irule EVERY2_TAKE
             \\ irule EVERY2_APPEND_suff \\ simp [])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `s1 with clock := LENGTH arg_env + t1.clock - num_args` mp_tac)
      \\ simp [state_rel_clock]
      \\ disch_then drule
      \\ strip_tac
      \\ Cases_on `res1` \\ fs [] \\ rveq
      \\ qexists_tac `ck` \\ fs []))
QED

Theorem remove_ticks_correct:
   (!xs env2 (t1:('c,'ffi) closSem$state) res2 t2 env1 s1.
     (evaluate (remove_ticks xs,env2,t1) = (res2,t2)) /\
     LIST_REL v_rel env1 env2 /\ state_rel s1 t1 ==>
     ?ck res1 s2.
        (evaluate (xs,env1,s1 with clock := s1.clock + ck) = (res1,s2)) /\
        result_rel (LIST_REL v_rel) v_rel res1 res2 /\
        state_rel s2 t2)
Proof
  rpt strip_tac \\ drule (CONJUNCT1 evaluate_remove_ticks) \\ simp [code_rel_def]
QED

(* preservation of observable semantics *)

Theorem semantics_remove_ticks:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc compile_inc cc) xs <> Fail ==>
   (∀n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc compile_inc cc) xs =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (pure_co compile_inc ∘ co) cc
     (remove_ticks xs)
Proof
  (**)
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq_no_fail
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule remove_ticks_correct
  \\ simp [code_rel_def]
  \\ disch_then (qspec_then `initial_state ffi max_app FEMPTY
                               co (pure_cc compile_inc cc) k` mp_tac)
  \\ impl_tac
  THEN1 (fs [state_rel_def, initial_state_def, FMAP_REL_def])
  \\ simp [initial_state_def]
  \\ strip_tac
  \\ qexists_tac `ck` \\ simp []
  \\ rename1 `result_rel _ v_rel res2 _`
  \\ Cases_on `res2` \\ fs []
  \\ TRY (Cases_on `e` \\ fs [])
  \\ fs [state_rel_def]
QED

(* syntactic properties *)

Theorem code_locs_remove_ticks:
   !xs. code_locs (remove_ticks xs) = code_locs xs
Proof
  ho_match_mp_tac clos_ticksTheory.remove_ticks_ind \\ rw []
  \\ fs [code_locs_def,clos_ticksTheory.remove_ticks_def]
  THEN1
   (`?y. remove_ticks [x] = [y]` by metis_tac [remove_ticks_SING]
    \\ fs [] \\ simp [Once code_locs_cons])
  \\ Induct_on `fns` \\ fs [FORALL_PROD]
  \\ rw [] \\ fs []
  \\ once_rewrite_tac [code_locs_cons] \\ fs []
  \\ metis_tac []
QED

Theorem remove_ticks_every_Fn_SOME[simp]:
   ∀ls. every_Fn_SOME (remove_ticks ls) ⇔ every_Fn_SOME ls
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def]
  >- (
    qspec_then`x`strip_assume_tac remove_ticks_SING
    \\ fs[] \\ fs[Once every_Fn_SOME_EVERY] )
  \\ simp[Once every_Fn_SOME_EVERY,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ simp[Once every_Fn_SOME_EVERY,SimpRHS,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ metis_tac[]
QED

Theorem remove_ticks_every_Fn_vs_NONE[simp]:
   ∀ls. every_Fn_vs_NONE (remove_ticks ls) ⇔ every_Fn_vs_NONE ls
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def]
  >- (
    qspec_then`x`strip_assume_tac remove_ticks_SING
    \\ fs[] \\ fs[Once every_Fn_vs_NONE_EVERY] )
  \\ simp[Once every_Fn_vs_NONE_EVERY,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ simp[Once every_Fn_vs_NONE_EVERY,SimpRHS,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ metis_tac[]
QED

Theorem EVERY_remove_ticks_sing:
   EVERY f (remove_ticks [x]) = f (HD (remove_ticks [x]))
Proof
  qspec_then`x`strip_assume_tac remove_ticks_SING \\ fs []
QED

Theorem remove_ticks_obeys_max_app:
   !xs. EVERY (obeys_max_app m) xs ==> EVERY (obeys_max_app m) (remove_ticks xs)
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def]
  \\ fs [EVERY_remove_ticks_sing,LENGTH_remove_ticks]
  \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac
QED

Theorem remove_ticks_no_Labels:
   !xs. EVERY no_Labels xs ==> EVERY no_Labels (remove_ticks xs)
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def]
  \\ fs [EVERY_remove_ticks_sing]
  \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac
QED

Theorem remove_ticks_app_call_dests[simp]:
   ∀es. app_call_dests x (remove_ticks es) = app_call_dests x es
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def]
  >- rw[Once closPropsTheory.app_call_dests_cons]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, o_DEF, UNCURRY]
  \\ simp[app_call_dests_map]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f, FORALL_PROD] \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem remove_ticks_code_labels[simp]:
   ∀es. MAP get_code_labels (clos_ticks$remove_ticks es) = MAP get_code_labels es
Proof
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def] \\ fs[]
  \\ fs[MAP_MAP_o, UNCURRY, o_DEF]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f, FORALL_PROD] \\ rw[]
  \\ res_tac \\ fs[]
QED

val _ = export_theory();
