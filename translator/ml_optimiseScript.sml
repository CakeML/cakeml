open HolKernel Parse boolLib bossLib;
val _ = new_theory "ml_optimise";
local open intLib in end;
open astTheory libTheory semanticPrimitivesTheory bigStepTheory;
open terminationTheory;
open evalPropsTheory bigClockTheory determTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory ml_translatorTheory;

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
  (BOTTOM_UP_OPT f (Letrec z1 z2) = f (Letrec z1 z2))`
 (WF_REL_TAC `measure (exp_size o SND)` THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC MEM_exp_size1 THEN IMP_RES_TAC MEM_exp_size2 THEN DECIDE_TAC)

val two_assums = METIS_PROVE [] ``(b ==> c) = (b ==> c /\ b)``;

val isRval_def = Define `(isRval (Rval _) = T) /\ (isRval _ = F)`;

val BOTTOM_UP_OPT_LEMMA = prove(
  ``(!ck env s exp res. evaluate F env s exp res ==> isRval (SND res) ==> evaluate F env s (f exp) res) ==>
    (!ck x1 s x2 x3. evaluate ck x1 s x2 x3 ==> isRval (SND x3) ∧ (ck = F) ==> evaluate ck x1 s (BOTTOM_UP_OPT f x2) x3) /\
    (!ck x1 s x2 x3. evaluate_list ck x1 s x2 x3 ==> isRval (SND x3) ∧ (ck = F) ==> evaluate_list ck x1 s (MAP (BOTTOM_UP_OPT f) x2) x3) /\
    (!ck x1 s x2 x3 x4 x5. evaluate_match ck x1 s x2 x3 x4 x5 ==> isRval (SND x5) ∧ (ck = F) ==> evaluate_match ck x1 s x2 (MAP (\(p,x). (p,BOTTOM_UP_OPT f x)) x3) x4 x5)``,
  STRIP_TAC \\ ONCE_REWRITE_TAC [two_assums]
  \\ HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [BOTTOM_UP_OPT_def,isRval_def,AND_IMP_INTRO]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ ASM_SIMP_TAC std_ss []
  \\ TRY (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases] THEN NO_TAC)
  \\ TRY (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th THEN ASSUME_TAC th)
          THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] THEN NO_TAC)
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ REPEAT DISJ1_TAC \\ METIS_TAC [])
  THEN1
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ REPEAT DISJ1_TAC
    \\ METIS_TAC [])
  THEN1 
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ DISJ2_TAC \\ DISJ1_TAC
    \\ METIS_TAC [])
  THEN1 
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ DISJ2_TAC \\ DISJ1_TAC
    \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ REPEAT DISJ1_TAC \\ METIS_TAC [])
  THEN1
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ REPEAT DISJ1_TAC
    \\ METIS_TAC [])
  THEN1 
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def]
    \\ DISJ2_TAC \\ DISJ1_TAC
    \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [do_log_def]
    \\ Cases_on `op` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v`
    \\ FULL_SIMP_TAC std_ss [do_if_def]
    \\ REPEAT (BasicProvers.FULL_CASE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,isRval_def] \\ METIS_TAC []));

val BOTTOM_UP_OPT_THM = prove(
  ``!f.
      (!env s exp t res.
         evaluate F env s exp (t,Rval res) ==>
         evaluate F env s (f exp) (t,Rval res)) ==>
      (!env s exp t res.
         evaluate F env s exp (t,Rval res) ==>
         evaluate F env s (BOTTOM_UP_OPT f exp) (t,Rval res))``,
  STRIP_TAC \\ STRIP_TAC \\ (BOTTOM_UP_OPT_LEMMA
    |> UNDISCH |> CONJUNCT1 |> Q.SPECL [`F`, `env`,`s`,`exp`,`(t,Rval res)`] |> GEN_ALL
    |> DISCH_ALL |> GEN_ALL |> SIMP_RULE std_ss [isRval_def] |> MATCH_MP_TAC)
  \\ REPEAT STRIP_TAC \\ Cases_on `res` \\ FULL_SIMP_TAC std_ss [isRval_def]
  \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [isRval_def])
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];


(* rewrite optimisation: (fn x => exp) y --> let x = y in exp *)

val abs2let_def = Define `
  abs2let x =
     case x of App Opapp [Fun v exp; y] => Let (SOME v) y exp
             | rest => rest`;

val abs2let_thm = prove(
  ``!env s exp t res. evaluate F env s exp (t,Rval res) ==>
                      evaluate F env s (abs2let exp) (t,Rval res)``,
  SIMP_TAC std_ss [abs2let_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,do_opapp_def]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ PairCases_on `env` \\ SIMP_TAC (srw_ss()) []
  \\ BasicProvers.EVERY_CASE_TAC
  \\ SRW_TAC [] []
  \\ NTAC 3 (FULL_SIMP_TAC (srw_ss()) [Once (hd (tl (CONJUNCTS evaluate_cases)))])
  \\ Q.LIST_EXISTS_TAC [`h`,(`count',s2`)] \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `evaluate F env s (Fun s' e) ((s2',Rval v1))` MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [opt_bind_def]);


(* rewrite optimisation: let x = y in x --> y *)

val let_id_def = Define `
  (let_id (Let (SOME v) x y) =
     if (y = Var (Short v)) then x else Let (SOME v) x y) /\
  (let_id rest = rest)`;

val let_id_thm = prove(
  ``!env s exp t res. evaluate F env s exp (t,Rval res) ==>
                      evaluate F env s (let_id exp) (t,Rval res)``,
  STRIP_TAC \\ STRIP_TAC \\ HO_MATCH_MP_TAC (fetch "-" "let_id_ind")
  \\ FULL_SIMP_TAC std_ss [let_id_def] \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [lookup_var_id_def,opt_bind_def]);


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
  FULL_SIMP_TAC (srw_ss()) [do_app_cases]
  \\ SRW_TAC [] []);

val evaluate_11_Rval = prove(
  ``evaluate ck env s exp (t,Rval res1) ==>
    evaluate ck env s exp (t,Rval res2) ==> (res1 = res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC big_exp_determ
  \\ FULL_SIMP_TAC (srw_ss()) []);

val evaluate_Lit = prove(
  ``evaluate ck env s (Lit l) (s1,Rval (res)) <=> (res = Litv l) /\ (s = s1)``,
  FULL_SIMP_TAC (srw_ss()) [Once evaluate_cases] \\ METIS_TAC []);

val opt_sub_add_thm = prove(
  ``!env s exp t res. evaluate F env s exp (t,Rval res) ==>
                      evaluate F env s (opt_sub_add exp) (t,Rval res)``,
  STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ SIMP_TAC std_ss [opt_sub_add_def]
  \\ Cases_on `dest_binop exp` \\ FULL_SIMP_TAC std_ss []
  \\ `?x1 x2 x3. x = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `dest_binop x2` \\ FULL_SIMP_TAC std_ss []
  \\ `?y1 y2 y3. x' = (y1,y2,y3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []
  \\ Cases_on `y3` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x3 = Lit l` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC dest_binop_thm \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ NTAC 3 (FULL_SIMP_TAC (srw_ss()) [Once (hd (tl (CONJUNCTS evaluate_cases)))])
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ NTAC 3 (FULL_SIMP_TAC (srw_ss()) [Once (hd (tl (CONJUNCTS evaluate_cases)))])
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]
  \\ REPEAT STRIP_TAC
  \\ SRW_TAC [] []
  \\ IMP_RES_TAC do_app_IMP
  \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT (Q.PAT_ASSUM `Lit xx = yy` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]
  \\ FULL_SIMP_TAC (srw_ss()) [opn_lookup_def, dest_binop_def,
       intLib.COOPER_PROVE ``i + i2 - i2 = i:int``,
       intLib.COOPER_PROVE ``i - i2 + i2 = i:int``]
  \\ SRW_TAC [] [intLib.COOPER_PROVE ``x+y-y:int = x``]);

(* top-level optimiser *)

val OPTIMISE_def = Define `
  OPTIMISE =
    BOTTOM_UP_OPT (opt_sub_add o let_id) o BOTTOM_UP_OPT abs2let`;

val Eval_OPTIMISE = store_thm("Eval_OPTIMISE",
  ``Eval env exp P ==> Eval env (OPTIMISE exp) P``,
  SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss [OPTIMISE_def]
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  \\ SIMP_TAC std_ss [opt_sub_add_thm,let_id_thm]
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  \\ ASM_SIMP_TAC std_ss [abs2let_thm]);

val _ = export_theory();
