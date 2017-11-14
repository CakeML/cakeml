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
   (cheat)
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
   (cheat)
  THEN1 (* Fn *)
   (cheat)
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

