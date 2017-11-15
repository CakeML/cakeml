open preamble closPropsTheory
clos_inlineTheory closSemTheory;
open closLangTheory;
open backendPropsTheory;

val _ = new_theory "clos_inlineProof";

(* More than one resolution of overloading was possible? *)

val LENGTH_remove_ticks = store_thm("LENGTH_remove_ticks",
  ``!es. LENGTH (remove_ticks es) = LENGTH es``,
  recInduct remove_ticks_ind \\ fs [remove_ticks_def]);

val remove_ticks_IMP_LENGTH = store_thm("remove_ticks_LENGTH_imp",
  ``!es xs. xs = remove_ticks es ==> LENGTH es = LENGTH xs``,
  fs [LENGTH_remove_ticks]);

(* code relation *)

val code_rel_def = Define `
  code_rel e1 e2 <=>
    e2 = remove_ticks e1`;

val code_rel_IMP_LENGTH = store_thm("code_rel_IMP_LENGTH",
  ``!xs ys. code_rel xs ys ==> LENGTH xs = LENGTH ys``,
  fs [code_rel_def, LENGTH_remove_ticks]);

val remove_ticks_sing = store_thm("remove_ticks_sing",
  ``!e. ?e'. remove_ticks [e] = [e']``,
  Induct \\ fs [remove_ticks_def]);

val remove_ticks_cons = store_thm("remove_ticks_cons",
  ``!es e. remove_ticks (e::es) = HD (remove_ticks [e])::remove_ticks es``,
  Induct_on `es` \\ Induct_on `e` \\ fs [remove_ticks_def]);

val code_rel_CONS = store_thm("code_rel_CONS",
  ``!x xs y y ys. code_rel (x::xs) (y::ys) <=>
                  code_rel [x] [y] /\ code_rel xs ys``,
  fs [code_rel_def]
  \\ rpt strip_tac
  \\ `?x'. remove_ticks [x] = [x']` by metis_tac [remove_ticks_sing]
  \\ rw [Once remove_ticks_cons]);

val code_rel_CONS_CONS = store_thm("code_rel_CONS_CONS",
  ``!x1 x2 xs y1 y2 ys. code_rel (x1::x2::xs) (y1::y2::ys) <=>
                        code_rel [x1] [y1] /\ code_rel (x2::xs) (y2::ys)``,
  fs [code_rel_def]
  \\ rpt strip_tac
  \\ `?t1. remove_ticks [x1] = [t1]` by metis_tac [remove_ticks_sing]
  \\ `?t2. remove_ticks [x2] = [t2]` by metis_tac [remove_ticks_sing]
  \\ rw [remove_ticks_cons]);

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
  (!l1 l2 args1 args2 env1 env2 num_args e1 e2.
     LIST_REL v_rel env1 env2 /\
     LIST_REL v_rel args1 args2 /\
     [e2] = remove_ticks [e1] ==>
       v_rel (Closure l1 args1 env1 num_args e1) (Closure l2 args2 env2 num_args e2)) /\
  (!l1 l2 args1 args2 env1 env2 k.
     LIST_REL v_rel env1 env2 /\
     LIST_REL v_rel args1 args2 /\
     LIST_REL f_rel funs1 funs2 ==>
       v_rel (Recclosure l1 args1 env1 funs1 k) (Recclosure l2 args2 env2 funs2 k))`;

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
  compile_inc (e, xs) = (HD (remove_ticks [e]), [])`;

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


(* eval remove ticks *)

val mk_Ticks_def = Define `
  (mk_Ticks [] (e : closLang$exp) = e) /\
  (mk_Ticks (t::tr) e = Tick t (mk_Ticks tr e))`;

val remove_ticks_IMP_mk_Ticks = store_thm("remove_ticks_IMP_mk_Ticks",
  ``(!e t n. [Var t n] = remove_ticks [e] ==> ?tr. e = mk_Ticks tr (Var t n))``,
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexists_tac `[]` \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexists_tac `t::tr` \\ fs [mk_Ticks_def]);

val HD_remove_ticks_SING = store_thm("HD_remove_ticks_SING[simp]",
  ``!x. [HD (remove_ticks [x])] = remove_ticks [x]``,
  gen_tac \\ strip_assume_tac (Q.SPEC `x` remove_ticks_sing) \\ fs []);

val remove_ticks_Tick = store_thm("remove_ticks_Tick",
  ``!x t e. ~([Tick t e] = remove_ticks [x])``,
  Induct \\ fs [remove_ticks_def]);

val qexistsl_tac = map_every qexists_tac;

val remove_ticks_If_IMP_mk_Ticks = store_thm("remove_ticks_If_IMP_mk_Ticks",
  ``!x tr e1' e2' e3'.
      [If tr e1' e2' e3'] = remove_ticks [x] ==>
        ?ts e1 e2 e3. x = mk_Ticks ts (If tr e1 e2 e3) /\
                      e1' = HD (remove_ticks [e1]) /\
                      e2' = HD (remove_ticks [e2]) /\
                      e3' = HD (remove_ticks [e3])``,
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `x`, `x'`, `x''`] \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e1`, `e2`, `e3`] \\ fs [mk_Ticks_def]);
 

val remove_ticks_Let_IMP_mk_Ticks = store_thm("remove_ticks_Let_IMP_mk_Ticks",
  ``!x t l e. [Let t l e] = remove_ticks [x] ==>
              (?ts l' e'. x = mk_Ticks ts (Let t l' e') /\
               l = remove_ticks l' /\
               [e] = remove_ticks [e'])``,
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `l`, `x`] \\ fs [mk_Ticks_def])
  \\ res_tac
  \\ qexistsl_tac [`t::ts`, `l'`, `e'`]
  \\ fs [mk_Ticks_def]);

val remove_ticks_Raise_IMP_mk_Ticks = store_thm(
  "remove_ticks_Raise_IMP_mk_Ticks",
  ``!x t e. [Raise t e] = remove_ticks [x] ==>
            (?ts e'. x = mk_Ticks ts (Raise t e') /\ [e] = remove_ticks [e'])``,
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `x`] \\ fs [mk_Ticks_def])
  \\ res_tac
  \\ qexistsl_tac [`t::ts`, `e'`]
  \\ fs [mk_Ticks_def]);

val remove_ticks_Handle_IMP_mk_Ticks = store_thm(
  "remove_ticks_Handle_IMP_mk_Ticks",
  ``!x t e1' e2'. [Handle t e1' e2'] = remove_ticks [x] ==>
                  (?ts e1 e2. x = mk_Ticks ts (Handle t e1 e2) /\
                   [e1'] = remove_ticks [e1] /\ [e2'] = remove_ticks [e2])``,
  Induct \\ fs [remove_ticks_def] \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `x`, `x'`] \\ fs [mk_Ticks_def])
  \\ res_tac
  \\ qexistsl_tac [`t::ts`, `e1`, `e2`]
  \\ fs [mk_Ticks_def]);

val remove_ticks_Op_IMP_mk_Ticks = store_thm("remove_ticks_Op_IMP_mk_Ticks",
  ``!x tr op es'. [Op tr op es'] = remove_ticks [x] ==>
      ?ts es. x = mk_Ticks ts (Op tr op es) /\ es' = remove_ticks es``,
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `l`] \\ fs [mk_Ticks_def])
  \\ res_tac  \\ qexistsl_tac [`t::ts`, `es`] \\ fs [mk_Ticks_def]);

val remove_ticks_Fn_IMP_mk_Ticks = store_thm("remove_ticks_Fn_IMP_mk_Ticks",
  ``(!x tr loc vsopt num_args e'.
       [Fn tr loc vsopt num_args e'] = remove_ticks [x] ==>
         ?ts e. x = mk_Ticks ts (Fn tr loc vsopt num_args e) /\ [e'] = remove_ticks [e])``,
  reverse (Induct \\ fs [remove_ticks_def]) \\ rpt strip_tac
  THEN1 (qexistsl_tac [`[]`, `x`] \\ fs [mk_Ticks_def])
  \\ res_tac \\ qexistsl_tac [`t::ts`, `e`] \\ fs [mk_Ticks_def]);


val LIST_REL_APPEND = store_thm("LIST_REL_APPEND",
  ``!r xs ys a1 a2. LIST_REL r a1 a2 /\ LIST_REL r xs ys ==>
                    LIST_REL r (a1++xs) (a2++ys)``, 
  cheat);

val remove_ticks_mk_Ticks = store_thm("remove_ticks_mk_Ticks",
  ``!tr e. remove_ticks [mk_Ticks tr e] = remove_ticks [e]``,
  Induct_on `tr` \\ fs [mk_Ticks_def, remove_ticks_def]);

val evaluate_mk_Ticks = store_thm("evaluate_mk_Ticks",
  ``!tr e env s1.
      evaluate ([mk_Ticks tr e], env, s1) =
        if s1.clock < LENGTH tr then (Rerr (Rabort Rtimeout_error), s1 with clock := 0)
                                else evaluate ([e], env, dec_clock (LENGTH tr) s1)``,
  Induct THEN1 simp [mk_Ticks_def, dec_clock_def]
  \\ rw []
  \\ fs [mk_Ticks_def, evaluate_def, dec_clock_def]
  THEN1 (IF_CASES_TAC \\ simp [state_component_equality])
  \\ fs [ADD1]);

val bump_assum = fn (pat) => qpat_x_assum pat assume_tac;

val do_app_lemma = prove(
  ``state_rel s t /\ LIST_REL v_rel xs ys ==>
    case do_app opp ys t of
      | Rerr err2 => ?err1. do_app opp xs s = Rerr err1 /\ exc_rel v_rel err1 err2
      | Rval (y, t1) => ?x s1. v_rel x y /\ state_rel s1 t1 /\ do_app opp xs s = Rval (x, s1)``,
  cheat);

val lookup_vars_lemma = store_thm("lookup_vars_lemma",
  ``!vs env1 env2. LIST_REL v_rel env1 env2 ==>
    case lookup_vars vs env2 of
      | NONE => lookup_vars vs env1 = NONE
      | SOME l2 => ?l1. LIST_REL v_rel l1 l2 /\ lookup_vars vs env1 = SOME l1``,
  Induct_on `vs` \\ fs [lookup_vars_def]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw []
  \\ res_tac
  \\ Cases_on `lookup_vars vs env2`
  \\ fs []
  \\ fs [LIST_REL_EL_EQN]);

val state_rel_IMP_max_app_EQ = store_thm("state_rel_IMP_max_app_EQ",
  ``!s t. state_rel s t ==> s.max_app = t.max_app``,
  fs [state_rel_def]);


val evaluate_remove_ticks = Q.store_thm("evaluate_remove_ticks",
  `(!ys env2 (t1:('c,'ffi) closSem$state) res2 t2 env1 s1 xs.
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
     state_rel s1 t1 /\ LENGTH args1 <= s1.max_app ==>
     ?ck res1 s2.
       (evaluate_app loc_opt f1 args1 (s1 with clock := s1.clock + ck) = (res1,s2)) /\
       result_rel (LIST_REL v_rel) v_rel res1 res2 /\
       state_rel s2 t2)`,
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
    \\ qpat_x_assum `evaluate ([h], env1, _) = _` assume_tac (* move an asm to use with drule *)
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then kall_tac (* drop and ignore the precedent of an implication *)
    \\ imp_res_tac evaluate_SING
    \\ fs [])
  THEN1 (* Var *)
   (Cases_on `xs` \\ fs [code_rel_def, remove_ticks_def]
    \\ imp_res_tac remove_ticks_IMP_mk_Ticks \\ rveq
    \\ fs [remove_ticks_mk_Ticks]
    \\ fs [remove_ticks_def]
    \\ qexists_tac `LENGTH tr`
    \\ fs [evaluate_mk_Ticks]
    \\ fs [dec_clock_def]
    \\ fs [evaluate_def]
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
    \\ drule LIST_REL_APPEND
    \\ qpat_x_assum `LIST_REL v_rel env1 env2` assume_tac
    \\ disch_then drule 
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (mp_tac o Q.SPEC `[e']`)
    \\ fs [] \\ strip_tac
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ qexists_tac `ck + ck' + LENGTH ts` \\ fs []
    \\ qpat_x_assum `evaluate (l', env1, _) = _` assume_tac (* move an asm to use with drule *)
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
    \\ reverse (Cases_on `op = Install`) \\ fs []
    THEN1 (* op /= Install *)
     (fs [case_eq_thms]
      \\ rw []
      \\ qexists_tac `ck + LENGTH ts`
      \\ fs []
      \\ drule (GEN_ALL do_app_lemma)
      \\ drule EVERY2_REVERSE \\ strip_tac
      \\ disch_then drule
      \\ disch_then (assume_tac o Q.SPEC `op`)
      \\ rfs []
      \\ PairCases_on `v1`
      \\ fs []
      \\ metis_tac [])
    THEN1 (* op = Install *)
     (cheat)
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
    \\ fs [v_rel_rules])
  THEN1 (* Letrec *)
   (cheat)
  THEN1 (* App *)
   (cheat)
  THEN1 (* Tick *)
   (fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [code_rel_def]
    \\ fs [remove_ticks_Tick])
  THEN1 (* Call *)
   (cheat)
  THEN1 (* evaluate_app NIL *)
   (fs [evaluate_def] \\ rw [] \\ qexists_tac `0` \\ fs [state_component_equality])









































val _ = export_theory();

