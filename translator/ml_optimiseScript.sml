open preamble;
local open intLib in end;
open astTheory libTheory semanticPrimitivesTheory;
open terminationTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory ml_translatorTheory lcsymtacs;

val _ = new_theory "ml_optimise";

infix \\ val op \\ = op THEN;

(*

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



(* first an optimisation combinator: BOTTOM_UP_OPT *)

val MEM_exp_size1 = prove(
  ``!xs a. MEM a xs ==> exp_size a <= exp6_size xs``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val MEM_exp_size2 = prove(
  ``!ys p x. MEM (p,x) ys ==> exp_size x < exp3_size ys``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def] THEN Cases
  THEN FULL_SIMP_TAC std_ss [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val BOTTOM_UP_OPT_def = tDefine "BOTTOM_UP_OPT" `
  (BOTTOM_UP_OPT f (Lit v) = f (Lit v)) /\
  (BOTTOM_UP_OPT f (Raise ex) = f (Raise ex)) /\
  (BOTTOM_UP_OPT f (Var name) = f (Var name)) /\
  (BOTTOM_UP_OPT f (Con tag xs) = f (Con tag (MAP (BOTTOM_UP_OPT f) xs))) /\
  (BOTTOM_UP_OPT f (Fun name x) = f (Fun name x)) /\
  (BOTTOM_UP_OPT f (App op xs) = f (App op (MAP (BOTTOM_UP_OPT f) xs))) /\
  (BOTTOM_UP_OPT f (Log l x1 x2) = f (Log l (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (If x1 x2 x3) = f (If (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2) (BOTTOM_UP_OPT f x3))) /\
  (BOTTOM_UP_OPT f (Mat x ys) = f (Mat (BOTTOM_UP_OPT f x) (MAP (\(p,x). (p,BOTTOM_UP_OPT f x)) ys))) /\
  (BOTTOM_UP_OPT f (Let name x1 x2) = f (Let name (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (* TODO: Handle wasn't optimised before full-blown exceptions were in the
           language, but perhaps it should be now? *)
  (BOTTOM_UP_OPT f (Handle x ys) = Handle x ys) /\
  (BOTTOM_UP_OPT f (Letrec z1 z2) = f (Letrec z1 z2)) ∧
  (BOTTOM_UP_OPT f (Tannot x t) = Tannot (BOTTOM_UP_OPT f x) t)`
 (WF_REL_TAC `measure (exp_size o SND)` THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC MEM_exp_size1 THEN IMP_RES_TAC MEM_exp_size2 THEN DECIDE_TAC)

val two_assums = METIS_PROVE [] ``(b ==> c) = (b ==> c /\ b)``;

val isRval_def = Define `(isRval (Rval _) = T) /\ (isRval _ = F)`;

val do_log_IMP = prove(
  ``(do_log op v e2 = SOME (Exp x2)) ==> (x2 = e2)``,
  fs [do_log_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val do_log_IMP_2 = prove(
  ``(do_log op v e2 = SOME (Exp e2)) ==>
    !e3. (do_log op v e3 = SOME (Exp e3))``,
  fs [do_log_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val do_log_IMP_3 = prove(
  ``(do_log op v e2 = SOME (Val x)) ==>
    !e3. (do_log op v e3 = SOME (Val x))``,
  fs [do_log_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val s = ``s:'ffi state``

val map_sing_lemma = Q.prove (
`[f x] = MAP f [x]`,
rw []);

val lemma2 = Q.prove(
`(\a. f x a) = f x`,
 rw [FUN_EQ_THM]);

val BOTTOM_UP_OPT_LEMMA = prove(
  ``(!^s env exp res. evaluate s env exp = res ==> isRval (SND res) ==> evaluate s env (MAP f exp) = res) ==>
    (!^s x1 x2 x3. evaluate s x1 x2 = x3 ==> isRval (SND x3) ==> evaluate s x1 (MAP (BOTTOM_UP_OPT f) x2) = x3) /\
    (!^s x1 x2 x3 x4 x5. evaluate_match s x1 x2 x3 x4 = x5 ==> isRval (SND x5) ==> evaluate_match s x1 x2 (MAP (\(p,x). (p,BOTTOM_UP_OPT f x)) x3) x4 = x5)``,
  STRIP_TAC \\ ONCE_REWRITE_TAC [two_assums]
  \\ HO_MATCH_MP_TAC evaluate_ind
  >> rw [evaluate_def, BOTTOM_UP_OPT_def]
  >> simp_tac std_ss [Once map_sing_lemma]
  >> TRY (first_assum irule)
  >> simp [evaluate_def]
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw []
    >> fs [rich_listTheory.MAP_REVERSE, lemma2]
    >> rw []
    >> fs [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw []
    >> fs [rich_listTheory.MAP_REVERSE, lemma2]
    >> rw []
    >> fs [])
  >- (
    Cases_on `evaluate s x1 [e1]`
    >> Cases_on `r`
    >> fs []
    >> Cases_on `do_log lop (HD a) e2`
    >> fs [isRval_def]
    >> Cases_on `x`
    >> fs []
    >> TRY (drule do_log_IMP)
    >> TRY (drule do_log_IMP_3)
    >> rw []
    >> drule do_log_IMP_2
    >> rw [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw []
    >> fs [do_if_def]
    >> Cases_on `HD a = Boolv T`
    >> Cases_on `HD a = Boolv F`
    >> fs [Boolv_11]
    >> rw [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw [])
  >- (
    every_case_tac
    >> fs [isRval_def]
    >> rw []));

val BOTTOM_UP_OPT_THM = prove(
  ``!f.
      (!^s env exp t res.
         evaluate s env exp = (t,Rval res) ==>
         evaluate s env (MAP f exp) = (t,Rval res)) ==>
      (!^s env exp t res.
         evaluate s env exp = (t,Rval res) ==>
         evaluate s env (MAP (BOTTOM_UP_OPT f) exp) = (t,Rval res))``,
  STRIP_TAC \\ STRIP_TAC \\ (BOTTOM_UP_OPT_LEMMA
    |> UNDISCH |> CONJUNCT1
    |> Q.SPECL [`s`, `env`,`exp`,`(t,Rval res)`] |> GEN_ALL
    |> DISCH_ALL |> GEN_ALL |> SIMP_RULE std_ss [isRval_def] |> MATCH_MP_TAC)
  \\ REPEAT STRIP_TAC \\ Cases_on `evaluate s env exp` \\ FULL_SIMP_TAC std_ss [isRval_def]
  \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [isRval_def])
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];


(* rewrite optimisation: (fn x => exp) y --> let x = y in exp *)

(*
 * TODO: This optimisation changes the clock ticks, and so needs a more complicated
 * setup

val abs2let_def = Define `
  abs2let x =
     case x of App Opapp [Fun v exp; y] => Let (SOME v) y exp
             | rest => rest`;

val abs2let_thm = prove(
  ``!s env exp t res. evaluate s env [exp] = (t,Rval res) ==>
                      evaluate s env [abs2let exp] = (t,Rval res)``,

  SIMP_TAC std_ss [abs2let_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [evaluate_def,do_opapp_def]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [evaluate_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ SRW_TAC [] []
  >> fs []
  >> rw [opt_bind_def]
  >> fs [evaluateTheory.dec_clock_def]);
  *)

(* rewrite optimisation: let x = y in x --> y *)

val let_id_def = Define `
  (let_id (Let (SOME v) x y) =
     if (y = Var (Short v)) then x else Let (SOME v) x y) /\
  (let_id rest = rest)`;

val let_id_thm = prove(
  ``!s env exp t res. evaluate s env [exp] = (t,Rval res) ==>
                      evaluate s env [let_id exp] = (t,Rval res)``,
  STRIP_TAC \\ STRIP_TAC \\ HO_MATCH_MP_TAC (fetch "-" "let_id_ind")
  \\ FULL_SIMP_TAC std_ss [let_id_def] \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [evaluate_def]
  \\ FULL_SIMP_TAC (srw_ss()) [lookup_var_id_def,opt_bind_def]
  >> every_case_tac
  >> rw []
  >> imp_res_tac evaluatePropsTheory.evaluate_sing
  >> fs []);

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

val dest_binop_thm = prove(
  ``!x. (dest_binop x = SOME (x1,x2,x3)) ==> (x = App (Opn x1) [x2; x3])``,
  HO_MATCH_MP_TAC (fetch "-" "dest_binop_ind")
  \\ FULL_SIMP_TAC (srw_ss()) [dest_binop_def]);

val do_app_IMP = prove(
  ``(do_app s (Opn opn) [v1; v2] = SOME (s1,e3)) ==>
    ?i1 i2. (v1 = Litv (IntLit i1)) /\ (v2 = Litv (IntLit i2))``,
  Cases_on`s` >> FULL_SIMP_TAC (srw_ss()) [semanticPrimitivesPropsTheory.do_app_cases]
  \\ SRW_TAC [] []);

val evaluate_11_Rval = prove(
  ``evaluate s env exp = (t,Rval res1) ==>
    evaluate s env exp = (t,Rval res2) ==> (res1 = res2)``,
  rw []);

val evaluate_Lit = prove(
  ``evaluate s env [Lit l] = (s1,Rval (res)) <=> (res = [Litv l]) /\ (s = s1)``,
  FULL_SIMP_TAC (srw_ss()) [evaluate_def] \\ METIS_TAC []);

val with_same_refs_io = Q.prove(
  `x with <| refs := x.refs; ffi := x.ffi |> = x`,
  rw[state_component_equality])

val opt_sub_add_thm = prove(
  ``!s env exp t res. evaluate s env [exp] = (t,Rval res) ==>
                      evaluate s env [opt_sub_add exp] = (t,Rval res)``,
  STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ SIMP_TAC std_ss [opt_sub_add_def]
  \\ Cases_on `dest_binop exp` \\ FULL_SIMP_TAC std_ss []
  \\ `?x1 x2 x3. x = (x1,x2,x3)` by METIS_TAC [PAIR] \\ fs []
  \\ Cases_on `dest_binop x2` \\ FULL_SIMP_TAC std_ss []
  \\ `?y1 y2 y3. x' = (y1,y2,y3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []
  \\ Cases_on `y3` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x3 = Lit l` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC dest_binop_thm \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [evaluate_def]
  >> every_case_tac
  >> rw []
  >> rw [state_component_equality]
  >> fs []
  >> rw []
  >> fs [semanticPrimitivesPropsTheory.do_app_cases]
  >> rw []
  >> fs []
  >> rw [opn_lookup_def]
  >> intLib.ARITH_TAC);

(* top-level optimiser *)

val OPTIMISE_def = Define `
  OPTIMISE =
    BOTTOM_UP_OPT (opt_sub_add o let_id) (*o BOTTOM_UP_OPT abs2let*)`;

val sing_opt_to_list = Q.prove (
`(∀^s env exp t res.
   evaluate s env [exp] = (t,Rval res) ⇒
   evaluate s env [f exp] = (t,Rval res))
 ⇒
 (∀^s env exp t res.
   evaluate s env exp = (t,Rval res) ⇒
   evaluate s env (MAP f exp) = (t,Rval res))`,
 strip_tac
 >> Induct_on `exp`
 >> rw []
 >> pop_assum mp_tac
 >> ONCE_REWRITE_TAC [evaluatePropsTheory.evaluate_cons]
 >> every_case_tac
 >> rw []
 >> res_tac
 >> fs []
 >> rw []
 >> fs []);

val Eval_OPTIMISE = store_thm("Eval_OPTIMISE",
  ``Eval env exp P ==> Eval env (OPTIMISE exp) P``,
  SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss [OPTIMISE_def]
  \\ qexists_tac `k`
  >> simp_tac std_ss [Once map_sing_lemma]
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  >> simp []
  >> match_mp_tac sing_opt_to_list
  \\ SIMP_TAC std_ss [opt_sub_add_thm,let_id_thm]);

  (*
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  \\ ASM_SIMP_TAC std_ss [abs2let_thm]);
  *)

val _ = export_theory();
