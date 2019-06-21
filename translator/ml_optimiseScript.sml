(*
  A simple verified optimiser for CakeML expressions, which is applied once the
  translator has produced some CakeML syntax.

  The HOL-->ML translator occsionally produces clunky code. This file
  defines a verified optimiser which is used to simplify the clunky
  parts of the generated code.

  This optimiser:
   - first, rewrites "(fn x => exp) y" to "let x = y in exp"
   - then, a number of rewrites are applied, e.g.
       "x - n + n" --> "x"
       "x + n - n" --> "x"
       "let x = y in x" --> "y"
*)

open preamble
     astTheory libTheory semanticPrimitivesTheory
     ml_progTheory ml_translatorTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory;
open terminationTheory ml_translatorTheory

val _ = new_theory "ml_optimise";

(* first an optimisation combinator: BOTTOM_UP_OPT *)

val MEM_exp_size1 = Q.prove(
  `!xs a. MEM a xs ==> exp_size a <= exp6_size xs`,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val MEM_exp_size2 = Q.prove(
  `!ys p x. MEM (p,x) ys ==> exp_size x < exp3_size ys`,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def] THEN Cases
  THEN FULL_SIMP_TAC std_ss [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val exp6_size_SNOC = prove(
  ``!xs y. exp6_size (xs ++ [y]) = exp6_size xs + exp6_size [y]``,
  Induct \\ fs [exp_size_def]);

val exp6_size_REVERSE = prove(
  ``!xs. exp6_size (REVERSE xs) = exp6_size xs``,
  Induct \\ fs [exp_size_def,exp6_size_SNOC]);

val BOTTOM_UP_OPT_def = tDefine "BOTTOM_UP_OPT" `
  (BOTTOM_UP_OPT f (Lit v) = f (Lit v)) /\
  (BOTTOM_UP_OPT f (Raise ex) = f (Raise ex)) /\
  (BOTTOM_UP_OPT f (Var name) = f (Var name)) /\
  (BOTTOM_UP_OPT f (Con tag xs) =
     let ys = BOTTOM_UP_OPT_LIST f (REVERSE xs) in
       f (Con tag (BOTTOM_UP_OPT_LIST f xs))) /\
  (BOTTOM_UP_OPT f (Fun name x) = f (Fun name x)) /\
  (BOTTOM_UP_OPT f (App op xs) =
     let ys = BOTTOM_UP_OPT_LIST f (REVERSE xs) in
       f (App op (BOTTOM_UP_OPT_LIST f xs))) /\
  (BOTTOM_UP_OPT f (Log l x1 x2) = f (Log l (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (If x1 x2 x3) = f (If (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2) (BOTTOM_UP_OPT f x3))) /\
  (BOTTOM_UP_OPT f (Mat x ys) = f (Mat (BOTTOM_UP_OPT f x) (BOTTOM_UP_OPT_PAT f ys))) /\
  (BOTTOM_UP_OPT f (Let name x1 x2) = f (Let name (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (Handle x ys) = Handle x ys) /\
  (BOTTOM_UP_OPT f (Letrec z1 z2) = f (Letrec z1 z2)) ∧
  (BOTTOM_UP_OPT f (Tannot x t) = Tannot (BOTTOM_UP_OPT f x) t) ∧
  (BOTTOM_UP_OPT f (Lannot x l) = Lannot (BOTTOM_UP_OPT f x) l) /\
  (BOTTOM_UP_OPT_LIST f [] = []) /\
  (BOTTOM_UP_OPT_LIST f (y::ys) =
     BOTTOM_UP_OPT f y :: BOTTOM_UP_OPT_LIST f ys) /\
  (BOTTOM_UP_OPT_PAT f [] = []) /\
  (BOTTOM_UP_OPT_PAT f ((p,y)::ys) =
     (p,BOTTOM_UP_OPT f y) :: BOTTOM_UP_OPT_PAT f ys)`
  (WF_REL_TAC `measure (\x. case x of
                  | INL x => (exp_size o SND) x
                  | INR (INL x) => (exp6_size o SND) x
                  | INR (INR x) => (exp3_size o SND) x)`
   \\ rw [exp6_size_REVERSE]);

val BOTTOM_UP_OPT_def = save_thm("BOTTOM_UP_OPT_def[compute]",
  BOTTOM_UP_OPT_def |> SIMP_RULE std_ss [LET_THM]);

val LENGTH_BOTTOM_UP_OPT_LIST = prove(
  ``!xs. LENGTH (BOTTOM_UP_OPT_LIST f xs) = LENGTH xs``,
  Induct \\ fs [BOTTOM_UP_OPT_def]);

val BOTTOM_UP_OPT_LIST_APPEND = prove(
  ``!xs ys. BOTTOM_UP_OPT_LIST f (xs++ys) =
            BOTTOM_UP_OPT_LIST f xs ++ BOTTOM_UP_OPT_LIST f ys``,
  Induct \\ fs [BOTTOM_UP_OPT_def]);

val REVERSE_BOTTOM_UP_OPT_LIST = prove(
  ``!xs. REVERSE (BOTTOM_UP_OPT_LIST f xs) = BOTTOM_UP_OPT_LIST f (REVERSE xs)``,
  Induct \\ fs [BOTTOM_UP_OPT_def,BOTTOM_UP_OPT_LIST_APPEND]);

Theorem dec_clock_with_clock[simp]:
   (dec_clock st1 with clock := c) = st1 with clock := c
Proof
  fs [state_component_equality,evaluateTheory.dec_clock_def]
QED

val s = ``s:'ffi semanticPrimitives$state``

local
  val assum =
    ``(!x ^s env s1 r. eval_rel ^s env x s1 r ==>
                       eval_rel ^s env (f x) s1 r)``
  val lemma =
    fetch "-" "BOTTOM_UP_OPT_ind"
    |> Q.SPECL [`\g x. ^assum ==>
                   !s s1 r env. eval_rel ^s env x s1 r ==>
                            eval_rel ^s env (BOTTOM_UP_OPT f x) s1 r`]
    |> Q.SPECL [`\g xs. ^assum ==>
                   !s s1 r env. eval_list_rel ^s env xs s1 r ==>
                            eval_list_rel ^s env (BOTTOM_UP_OPT_LIST f xs) s1 r`]
    |> Q.SPECL [`\g pats. ^assum ==>
                   !s s1 r v r w env. eval_match_rel ^s env v pats w s1 r ==>
                            eval_match_rel s env v (BOTTOM_UP_OPT_PAT f pats) w s1 r`]
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
    |> UNDISCH |> CONJUNCT1 |> DISCH_ALL;
in
  val BOTTOM_UP_OPT_THM = prove(
    ``^((snd o dest_imp o concl) lemma)``,
    match_mp_tac lemma \\ rpt strip_tac
    \\ pop_assum mp_tac
    \\ simp [eval_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM],
             eval_list_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM],
             eval_match_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM]] \\ fs []
    \\ fs [eval_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM],
           eval_list_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM],
           eval_match_rel_def |> ONCE_REWRITE_RULE [CONJ_COMM]]
    \\ fs [evaluate_def,pair_case_eq,result_case_eq,PULL_EXISTS,
           bool_case_eq,option_case_eq,state_component_equality]
    \\ rpt strip_tac \\ fs []
    \\ rveq \\ fs [BOTTOM_UP_OPT_def] \\ fs [evaluate_def]
    \\ TRY (first_x_assum match_mp_tac) \\ fs [evaluate_def]
    \\ fs [state_component_equality,LENGTH_BOTTOM_UP_OPT_LIST]
    \\ TRY (asm_exists_tac \\ fs [])
    \\ fs [evaluate_def,pair_case_eq,result_case_eq,PULL_EXISTS,
           bool_case_eq,option_case_eq,state_component_equality,
           REVERSE_BOTTOM_UP_OPT_LIST]
    \\ TRY (asm_exists_tac \\ fs [state_component_equality] \\ NO_TAC)
    \\ TRY (qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
            \\ asm_exists_tac \\ fs [state_component_equality] \\ NO_TAC)
    THEN1 (* Con *)
     (rename1 `_ = (st1,Rval vs)`
      \\ `evaluate (s with clock := ck1) env (REVERSE xs) =
            ((st1 with clock := s1.clock) with clock := st1.clock,Rval vs)`
               by fs [state_component_equality]
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ asm_exists_tac \\ fs [])
    THEN1 (* App Opapp *)
     (rename1 `_ = (st1,Rval vs)`
      \\ `evaluate (s with clock := ck1) env (REVERSE xs) =
            ((st1 with clock := s1.clock) with clock := st1.clock,Rval vs)`
               by fs [state_component_equality]
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2' + 1` assume_tac)
      \\ rfs [EVAL ``(dec_clock st1).clock``]
      \\ qpat_x_assum `evaluate _ _
           (BOTTOM_UP_OPT_LIST f (REVERSE xs)) = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `st1.clock+1` assume_tac)
      \\ asm_exists_tac \\ fs []
      \\ fs [evaluateTheory.dec_clock_def,state_component_equality])
    THEN1 (* App other *)
     (rename1 `_ = (st1,Rval vs)`
      \\ `evaluate (s with clock := ck1) env (REVERSE xs) =
            ((st1 with clock := s1.clock) with clock := st1.clock,Rval vs)`
               by fs [state_component_equality]
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ asm_exists_tac \\ fs [])
    THEN1 (* do_log *)
     (rename1 `_ = SOME v4` \\ reverse (Cases_on `v4`) \\ fs [] \\ rveq \\ fs []
      THEN1
       (imp_res_tac evaluate_sing \\ rveq \\ fs []
        \\ first_x_assum drule \\ fs [] \\ strip_tac \\ asm_exists_tac \\ fs []
        \\ `do_log l v (BOTTOM_UP_OPT f x2) = SOME (Val r)` by
             (fs [do_log_def] \\ rw [do_log_def] \\ fs [bool_case_eq] \\ rfs [])
        \\ fs [state_component_equality])
      \\ rename1 `_ = (st1,Rval v1)`
      \\ imp_res_tac evaluate_sing \\ rveq \\ fs []
      \\ rename1 `_ = (st1,Rval [v1])`
      \\ `evaluate (s with clock := ck1) env [x1] =
            ((st1 with clock := s1.clock) with clock := st1.clock,Rval [v1])`
               by fs [state_component_equality]
      \\ first_x_assum drule \\ simp [] \\ strip_tac \\ rveq \\ fs []
      \\ `x2 = e` by fs [do_log_def,bool_case_eq] \\ rveq \\ fs []
      \\ qpat_x_assum `evaluate st1 env [e] = _` assume_tac
      \\ `evaluate (st1 with clock := st1.clock) env [e] =
              ((s1 with clock := st1.clock) with clock := ck2,Rval [r])` by
       (`st1 with clock := st1.clock = st1` by fs [state_component_equality] \\ fs [])
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2'` assume_tac)
      \\ qpat_x_assum `evaluate _ _ [BOTTOM_UP_OPT f x1] = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck1''` assume_tac)
      \\ asm_exists_tac \\ fs []
      \\ `do_log l v1 (BOTTOM_UP_OPT f e) = SOME (Exp (BOTTOM_UP_OPT f e))` by
           (fs [do_log_def] \\ rw [do_log_def] \\ fs [bool_case_eq] \\ rfs [])
      \\ fs [] \\ fs [state_component_equality])
    THEN1 (* do_if *)
     (imp_res_tac evaluate_sing \\ rveq \\ fs []
      \\ rename1 `evaluate (s with clock := ck1) env [x1] = (st5,Rval [v5])`
      \\ rveq \\ fs []
      \\ `evaluate (s with clock := ck1) env [x1] =
            ((st5 with clock := s.clock) with clock := st5.clock,Rval [v5])` by
           fs [state_component_equality]
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ fs [do_if_def,bool_case_eq] \\ rveq \\ fs []
      \\ `evaluate (st5 with clock := st5.clock) env [e] =
             ((s1 with clock := st5.clock) with clock := ck2,Rval [r])` by fs []
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2'` assume_tac)
      \\ qpat_x_assum `evaluate _ _ [BOTTOM_UP_OPT f x1] = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck1''` assume_tac)
      \\ asm_exists_tac \\ fs [state_component_equality])
    THEN1 (* Mat *)
     (imp_res_tac evaluate_sing \\ rveq \\ fs []
      \\ rename1 `evaluate (s with clock := ck1) env [x1] = (st5,Rval [v5])`
      \\ rveq \\ fs []
      \\ `evaluate (s with clock := ck1) env [x1] =
            ((st5 with clock := s.clock) with clock := st5.clock,Rval [v5])` by
           fs [state_component_equality]
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ `evaluate_match (st5 with clock := st5.clock) env v5 ys bind_exn_v =
             ((s1 with clock := st5.clock) with clock := ck2,Rval [r])` by
                 (simp [] \\ fs [state_component_equality])
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ drule evaluate_match_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2'` assume_tac)
      \\ qpat_x_assum `evaluate _ _ [BOTTOM_UP_OPT f x1] = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck1''` assume_tac)
      \\ asm_exists_tac \\ fs [state_component_equality])
    THEN1 (* Let *)
     (imp_res_tac evaluate_sing \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate (s with clock := ck1) env [x1] = (st5,Rval [v5])`
      \\ rveq \\ fs []
      \\ `evaluate (s with clock := ck1) env [x1] =
            ((st5 with clock := s.clock) with clock := st5.clock,Rval [v5])` by
           fs [state_component_equality]
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ `evaluate (st5 with clock := st5.clock)
             (env with v := nsOptBind name v5 env.v) [x2] =
             ((s1 with clock := st5.clock) with clock := ck2,Rval [r])` by
                 (simp [] \\ fs [state_component_equality])
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2'` assume_tac)
      \\ qpat_x_assum `evaluate _ _ [BOTTOM_UP_OPT f x1] = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck1''` assume_tac)
      \\ asm_exists_tac \\ fs [state_component_equality])
    THEN1 (* cons *)
     (ntac 2 (pop_assum mp_tac)
      \\ once_rewrite_tac [evaluate_cons]
      \\ fs [pair_case_eq,result_case_eq] \\ strip_tac
      \\ rveq \\ fs []
      \\ imp_res_tac evaluate_sing \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate (s with clock := ck1) env [x1] = (st5,Rval [v5])`
      \\ rveq \\ fs [] \\ rpt strip_tac
      \\ `evaluate (s with clock := ck1) env [x1] =
            ((st5 with clock := s.clock) with clock := st5.clock,Rval [v5])` by
           fs [state_component_equality]
      \\ qpat_x_assum `!x. _` kall_tac
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ `evaluate (st5 with clock := st5.clock) env ys =
             ((s1 with clock := st5.clock) with clock := ck2,Rval vs')` by
                 (simp [] \\ fs [state_component_equality])
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck2'` assume_tac)
      \\ qpat_x_assum `evaluate _ _ [BOTTOM_UP_OPT f x1] = _` assume_tac
      \\ drule evaluate_add_to_clock \\ fs []
      \\ disch_then (qspec_then `ck1''` assume_tac)
      \\ asm_exists_tac \\ fs [state_component_equality]
      \\ qexists_tac `s1 with clock := ck2' + ck2''` \\ fs [])
    THEN1 (* match *)
     (ntac 2 (pop_assum (mp_tac o GSYM))
      \\ CASE_TAC \\ fs []
      THEN1 (rw [] \\ first_x_assum drule \\ fs [] \\ fs [])
      THEN1 (rw [] \\ last_x_assum drule \\ fs [] \\ fs [])));
end;


(* rewrite optimisation: (fn x => exp) y --> let x = y in exp *)

val abs2let_def = Define `
  abs2let x =
     case x of App Opapp [Fun v exp; y] => Let (SOME v) y exp
             | rest => rest`;

val abs2let_thm = Q.prove(
  `!env s exp t res. eval_rel s env exp t res ==>
                     eval_rel s env (abs2let exp) t res`,
  rpt strip_tac
  \\ Cases_on `abs2let exp = exp` \\ fs []
  \\ `?v e y. exp = App Opapp [Fun v e; y]` by
    (fs [Once abs2let_def] \\ every_case_tac \\ fs [])
  \\ rveq \\ fs [abs2let_def]
  \\ fs [eval_rel_def,evaluate_def,pair_case_eq,result_case_eq]
  \\ rveq \\ fs [] \\ rveq \\ fs [do_opapp_def,bool_case_eq,PULL_EXISTS]
  \\ fs [evaluateTheory.dec_clock_def,evaluate_def,abs2let_def]
  \\ qexists_tac `ck1` \\ fs []
  \\ first_x_assum (assume_tac o SYM) \\ fs []
  \\ drule evaluate_add_to_clock \\ fs []
  \\ disch_then (qspec_then `1` mp_tac) \\ fs []
  \\ `(st' with clock := st'.clock) = st'` by fs [state_component_equality]
  \\ fs [namespaceTheory.nsOptBind_def]
  \\ rw [] \\ fs [state_component_equality]);

(* rewrite optimisation: let x = y in x --> y *)

val let_id_def = Define `
  (let_id (Let (SOME v) x y) =
     if (y = Var (Short v)) then x else Let (SOME v) x y) /\
  (let_id rest = rest)`;

val let_id_thm = Q.prove(
  `!env s exp t res. eval_rel s env exp t res ==>
                     eval_rel s env (let_id exp) t res`,
  rpt strip_tac
  \\ Cases_on `let_id exp = exp` \\ fs []
  \\ `?v x y. exp = Let (SOME v) x (Var (Short v))` by
    (Cases_on `exp` \\ fs [let_id_def]
     \\ Cases_on `o'` \\ fs [let_id_def,bool_case_eq])
  \\ rveq \\ fs [let_id_def]
  \\ fs [eval_rel_def,evaluate_def,pair_case_eq,result_case_eq,option_case_eq]
  \\ qexists_tac `ck1`
  \\ rveq \\ fs []
  \\ fs [state_component_equality,namespaceTheory.nsOptBind_def]
  \\ imp_res_tac evaluate_sing \\ fs []);


(* rewrite optimisations: x - n + n --> x and x + n - n --> x *)

val dest_binop_def = Define `
  (dest_binop (App (Opn op) [x;y]) = SOME (op,x,y)) /\
  (dest_binop rest = NONE)`;

val opt_sub_add_def = Define `
  opt_sub_add x =
    case dest_binop x of
     | NONE => x
     | (SOME (op1,y,z)) =>
        case dest_binop y of
         | (SOME (op2,x1,Lit y1)) =>
            if z = Lit y1 then
              if (op1 = Plus) /\ (op2 = Minus) then x1 else
              if (op2 = Plus) /\ (op1 = Minus) then x1 else x
            else x
         | _ => x`;

val dest_binop_thm = Q.prove(
  `!x. (dest_binop x = SOME (x1,x2,x3)) <=> (x = App (Opn x1) [x2; x3])`,
  HO_MATCH_MP_TAC (fetch "-" "dest_binop_ind")
  \\ FULL_SIMP_TAC (srw_ss()) [dest_binop_def]);

val opt_sub_add_thm = Q.prove(
  `!env s exp t res. eval_rel s env exp t res ==>
                     eval_rel s env (opt_sub_add exp) t res`,
  rpt strip_tac
  \\ Cases_on `opt_sub_add exp = exp` \\ fs []
  \\ fs [opt_sub_add_def]
  \\ Cases_on `dest_binop exp` \\ fs []
  \\ PairCases_on `x` \\ fs [dest_binop_thm]
  \\ Cases_on `dest_binop x1` \\ fs []
  \\ rename1 `_ = SOME y`
  \\ PairCases_on `y` \\ fs [dest_binop_thm]
  \\ rveq \\ fs []
  \\ Cases_on `y2` \\ fs []
  \\ Cases_on `x2` \\ fs []
  \\ rw []
  \\ fs [eval_rel_def]
  \\ qexists_tac `ck1`
  \\ qexists_tac `ck2`
  \\ fs [eval_rel_def,evaluate_def,pair_case_eq,result_case_eq,option_case_eq]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ fs [state_component_equality]
  \\ imp_res_tac evaluate_sing \\ fs []
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ fs [do_app_def,option_case_eq,v_case_eq,lit_case_eq]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ fs [opn_lookup_def, dest_binop_def,
       intLib.COOPER_PROVE ``i + i2 - i2 = i:int``,
       intLib.COOPER_PROVE ``i - i2 + i2 = i:int``]);

(* top-level optimiser *)

val OPTIMISE_def = Define `
  OPTIMISE =
    BOTTOM_UP_OPT (opt_sub_add o let_id) o BOTTOM_UP_OPT abs2let`;

Theorem Eval_OPTIMISE:
   Eval env exp P ==> Eval env (OPTIMISE exp) P
Proof
  simp [Eval_def] \\ rpt strip_tac
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ qexists_tac `res` \\ fs [OPTIMISE_def]
  \\ qexists_tac`refs'`
  \\ match_mp_tac (MP_CANON BOTTOM_UP_OPT_THM) \\ fs []
  \\ metis_tac [BOTTOM_UP_OPT_THM,opt_sub_add_thm,let_id_thm,abs2let_thm]
QED

val _ = export_theory();
