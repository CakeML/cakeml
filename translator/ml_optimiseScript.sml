open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_optimise";

open MiniMLTheory MiniMLTerminationTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory ml_translatorTheory;

infix \\ val op \\ = op THEN;

(*

  The HOL-->ML translator occsionally produces clunky code. This file
  defines a verified optimiser which is used to simplify the clunky
  parts of the generated code.

  This optimiser:
   - first, rewrites "(fn x => exp) y" to "let x = y in exp"
   - then, attempts to decide simple arithmetic in if-statements,
     e.g. it attempts to simplify "if n < 0 then 0 else n" to "n"
     such if-statements arise from translation of minus for :num
   - finally, a number of rewrites are applied, e.g.
       "x - n + n" --> "x"
       "x + n - n" --> "x"
       "let x = y in x" --> "y"

*)



(* first an optimisation combinator: BOTTOM_UP_OPT *)

val MEM_exp_size1 = prove(
  ``!xs a. MEM a xs ==> exp_size (\x.0) a <= exp8_size (\x.0) xs``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val MEM_exp_size2 = prove(
  ``!ys p x. MEM (p,x) ys ==> exp_size (\x.0) x < exp5_size (\x.0) ys``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [exp_size_def] THEN Cases
  THEN FULL_SIMP_TAC std_ss [exp_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN DECIDE_TAC);

val BOTTOM_UP_OPT_def = tDefine "BOTTOM_UP_OPT" `
  (BOTTOM_UP_OPT f (Lit v) = f (Lit v)) /\
  (BOTTOM_UP_OPT f (Raise ex) = f (Raise ex)) /\
  (BOTTOM_UP_OPT f (Var name t) = f (Var name t)) /\
  (BOTTOM_UP_OPT f (Con tag xs) = f (Con tag (MAP (BOTTOM_UP_OPT f) xs))) /\
  (BOTTOM_UP_OPT f (Fun name ty x) = f (Fun name ty x)) /\
  (BOTTOM_UP_OPT f (Uapp uop x2) = f (Uapp uop (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (App op x1 x2) = f (App op (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (Log l x1 x2) = f (Log l (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (If x1 x2 x3) = f (If (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2) (BOTTOM_UP_OPT f x3))) /\
  (BOTTOM_UP_OPT f (Mat x ys) = f (Mat (BOTTOM_UP_OPT f x) (MAP (\(p,x). (p,BOTTOM_UP_OPT f x)) ys))) /\
  (BOTTOM_UP_OPT f (Let n name tt x1 x2) = f (Let n name tt (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
  (BOTTOM_UP_OPT f (Handle x1 name x2) = Handle x1 name x2) /\
  (BOTTOM_UP_OPT f (Letrec d z1 z2) = f (Letrec d z1 z2))`
 (WF_REL_TAC `measure (exp_size (\x.0) o SND)` THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC MEM_exp_size1 THEN IMP_RES_TAC MEM_exp_size2 THEN DECIDE_TAC)

val two_assums = METIS_PROVE [] ``(b ==> c) = (b ==> c /\ b)``;

val isRval_def = Define `(isRval (Rval _) = T) /\ (isRval _ = F)`;

val BOTTOM_UP_OPT_LEMMA = prove(
  ``(!s env exp res. evaluate' s env exp res ==> isRval (SND res) ==> evaluate' s env (f exp) res) ==>
    (!s x1 x2 x3. evaluate' s x1 x2 x3 ==> isRval (SND x3) ==> evaluate' s x1 (BOTTOM_UP_OPT f x2) x3) /\
    (!s x1 x2 x3. evaluate_list' s x1 x2 x3 ==> isRval (SND x3) ==> evaluate_list' s x1 (MAP (BOTTOM_UP_OPT f) x2) x3) /\
    (!s x1 x2 x3 x4. evaluate_match' s x1 x2 x3 x4 ==> isRval (SND x4) ==> evaluate_match' s x1 x2 (MAP (\(p,x). (p,BOTTOM_UP_OPT f x)) x3) x4)``,
  STRIP_TAC \\ ONCE_REWRITE_TAC [two_assums]
  \\ HO_MATCH_MP_TAC evaluate'_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [BOTTOM_UP_OPT_def,isRval_def,AND_IMP_INTRO]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ ASM_SIMP_TAC std_ss []
  \\ TRY (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] THEN NO_TAC)
  \\ TRY (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th THEN ASSUME_TAC th)
          THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] THEN NO_TAC)
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def]
    \\ REPEAT DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`v`]
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  THEN1
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def]
    \\ REPEAT DISJ1_TAC
    \\ Q.LIST_EXISTS_TAC [`v`,`s2`] \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def]
    \\ REPEAT DISJ1_TAC
    \\ Q.LIST_EXISTS_TAC [`v`] \\ ASM_SIMP_TAC std_ss [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ REPEAT DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`v1`,`v2`]
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [do_log_def]
    \\ Cases_on `op` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v`
    \\ FULL_SIMP_TAC std_ss [do_if_def]
    \\ REPEAT (BasicProvers.FULL_CASE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bbb` (fn th => MATCH_MP_TAC th \\ ASSUME_TAC th)
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,isRval_def] \\ METIS_TAC []));

val BOTTOM_UP_OPT_THM = prove(
  ``!f.
      (!s env exp t res.
         evaluate' s env exp (t,Rval res) ==>
         evaluate' s env (f exp) (t,Rval res)) ==>
      (!s env exp t res.
         evaluate' s env exp (t,Rval res) ==>
         evaluate' s env (BOTTOM_UP_OPT f exp) (t,Rval res))``,
  STRIP_TAC \\ STRIP_TAC \\ (BOTTOM_UP_OPT_LEMMA
    |> UNDISCH |> CONJUNCT1 |> Q.SPECL [`s`,`env`,`exp`,`(t,Rval res)`] |> GEN_ALL
    |> DISCH_ALL |> GEN_ALL |> SIMP_RULE std_ss [isRval_def] |> MATCH_MP_TAC)
  \\ REPEAT STRIP_TAC \\ Cases_on `res` \\ FULL_SIMP_TAC std_ss [isRval_def]
  \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [isRval_def])
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];


(* rewrite optimisation: (fn x => exp) y --> let x = y in exp *)

val abs2let_def = Define `
  abs2let x =
     case x of (App Opapp (Fun v tt exp) y) => Let (SOME 0) v tt y exp
             | rest => rest`;

val abs2let_thm = prove(
  ``!s env exp t res. evaluate' s env exp (t,Rval res) ==>
                      evaluate' s env (abs2let exp) (t,Rval res)``,
  SIMP_TAC std_ss [abs2let_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (BasicProvers.FULL_CASE_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases,do_app_def]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ Q.LIST_EXISTS_TAC [`v2`,`s3`] \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `evaluate' s env (Fun s' o'' e') ((s2,Rval v1))` MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases,do_app_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []);


(* rewrite optimisation: let x = y in x --> y *)

val let_id_def = Define `
  (let_id (Let NONE v NONE x y) =
     if (y = Var (Short v) NONE) then x else Let NONE v NONE x y) /\
  (let_id (Let (SOME i) v (SOME t) x y) =
     if (y = Var (Short v) (SOME [t])) /\ (i = 0) then x else Let (SOME i) v (SOME t) x y) /\
  (let_id rest = rest)`;

val let_id_thm = prove(
  ``!s env exp t res. evaluate' s env exp (t,Rval res) ==>
                      evaluate' s env (let_id exp) (t,Rval res)``,
  STRIP_TAC \\ STRIP_TAC \\ HO_MATCH_MP_TAC (fetch "-" "let_id_ind")
  \\ FULL_SIMP_TAC std_ss [let_id_def] \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases,bind_def,lookup_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [do_tapp_def,add_tvs_def]);


(* rewrite optimisations: x - n + n --> x and x + n - n --> x *)

val dest_binop_def = Define `
  (dest_binop (App (Opn op) x y) = SOME (op,x,y)) /\
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
  ``!x. (dest_binop x = SOME (x1,x2,x3)) ==> (x = App (Opn x1) x2 x3)``,
  HO_MATCH_MP_TAC (fetch "-" "dest_binop_ind")
  \\ FULL_SIMP_TAC (srw_ss()) [dest_binop_def]);

val do_app_IMP = prove(
  ``(do_app s env (Opn opn) v1 v2 = SOME (s1,env1,e3)) ==>
    ?i1 i2. (v1 = Litv (IntLit i1)) /\ (v2 = Litv (IntLit i2))``,
  FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) []);

val evaluate'_11_Rval = prove(
  ``evaluate' s env exp (t,Rval res1) ==>
    evaluate' s env exp (t,Rval res2) ==> (res1 = res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC big_exp_determ'
  \\ FULL_SIMP_TAC (srw_ss()) []);

val evaluate_Lit = prove(
  ``evaluate' s env (Lit l) (s1,Rval (res)) = (res = Litv l) /\ (s = s1)``,
  FULL_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC []);

val opt_sub_add_thm = prove(
  ``!s env exp t res. evaluate' s env exp (t,Rval res) ==>
                      evaluate' s env (opt_sub_add exp) (t,Rval res)``,
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
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]
  \\ `?i1 i2. (v1 = Litv (IntLit i1)) /\ (v2 = Litv (IntLit i2))` by METIS_TAC [do_app_IMP]
  \\ `?i1' i2'. (v1' = Litv (IntLit i1')) /\ (v2' = Litv (IntLit i2'))` by METIS_TAC [do_app_IMP]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT (Q.PAT_ASSUM `Lit xx = yy` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]
  \\ REPEAT (Q.PAT_ASSUM `IntLit xx = yy` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]
  \\ FULL_SIMP_TAC (srw_ss()) [opn_lookup_def,
       intLib.COOPER_PROVE ``i + i2 - i2 = i:int``,
       intLib.COOPER_PROVE ``i - i2 + i2 = i:int``]);


(*

(* integer "if-decide" optimisation *)

val pat_size_lemma = prove(
  ``!xs a. MEM a xs ==> pat_size a < pat1_size xs``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [pat_size_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val pat_vars_def = tDefine "pat_vars" `
  (pat_vars (Pvar v _) = [v]) /\
  (pat_vars (Pref p) = pat_vars p) /\
  (pat_vars (Plit _) = []) /\
  (pat_vars (Pcon c xs) = FLAT (MAP pat_vars xs))`
 (WF_REL_TAC `measure (pat_size)` THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC pat_size_lemma THEN DECIDE_TAC);

val _ = Hol_datatype `
  int_cmp = IntUnkown | IntLessEq of int => string
                      | IntGreater of int => string`;

val get_fact_def = Define `
  (get_fact (App (Opb Gt) (Var v NONE) ((Lit (IntLit i)))) = IntLessEq (i+1) v) /\
  (get_fact (App (Opb Geq) (Var v NONE) ((Lit (IntLit i)))) = IntLessEq i v) /\
  (get_fact (App (Opb Lt) ((Lit (IntLit i))) (Var v NONE)) = IntLessEq (i+1) v) /\
  (get_fact (App (Opb Leq) ((Lit (IntLit i))) (Var v NONE)) = IntLessEq i v) /\
  (get_fact (App (Opb Gt) ((Lit (IntLit i))) (Var v NONE)) = IntGreater i v) /\
  (get_fact (App (Opb Geq) ((Lit (IntLit i))) (Var v NONE)) = IntGreater (i+1) v) /\
  (get_fact (App (Opb Lt) (Var v NONE) ((Lit (IntLit i)))) = IntGreater i v) /\
  (get_fact (App (Opb Leq) (Var v NONE) ((Lit (IntLit i)))) = IntGreater (i+1) v) /\
  (get_fact _ = IntUnkown)`;

val int_negate_def = Define `
  (int_negate IntUnkown = IntUnkown) /\
  (int_negate (IntLessEq i v) = IntGreater i v) /\
  (int_negate (IntGreater i v) = IntLessEq i v)`;

val add_pos_fact_def = Define `add_pos_fact x b = get_fact x :: b`;
val add_neg_fact_def = Define `add_neg_fact x b = int_negate (get_fact x) :: b`;

val decide_guard_def = Define `
  (decide_guard (IntLessEq i v) (IntLessEq j w::xs) =
     if (v = w) /\ i <= j then SOME T else
       decide_guard (IntLessEq i v) xs) /\
  (decide_guard (IntLessEq i v) (IntGreater j w::xs) =
     if (v = w) /\ j <= i then SOME F else
       decide_guard (IntLessEq i v) xs) /\
  (decide_guard (IntGreater i v) (IntGreater j w::xs) =
     if (v = w) /\ j <= i then SOME T else
       decide_guard (IntGreater i v) xs) /\
  (decide_guard (IntGreater i v) (IntLessEq j w::xs) =
     if (v = w) /\ i <= j then SOME F else
       decide_guard (IntGreater i v) xs) /\
  (decide_guard _ [] = NONE) /\
  (decide_guard g (x::xs) = decide_guard g xs)`

val int_cmp_sem_def = Define `
  (int_cmp_sem (env:envE) res IntUnkown = T) /\
  (int_cmp_sem env res (IntLessEq i v) =
     ?j t. (lookup v env = SOME (Litv (IntLit j),t)) /\ (i <= j = res)) /\
  (int_cmp_sem env res (IntGreater i v) =
     ?j t. (lookup v env = SOME (Litv (IntLit j),t)) /\ (j < i = res))`;

val case_LEMMA = prove(
  ``!t. (case t of NONE => v | SOME (y,z) => v) = v``,
  Cases \\ SIMP_TAC (srw_ss()) [] \\ Cases_on `x` \\ SIMP_TAC (srw_ss()) []);

val get_fact_thm_T = prove(
  ``!x env.
      evaluate' s env x (s1,Rval (Litv (Bool T))) ==>
      int_cmp_sem env T ((get_fact x))``,
  HO_MATCH_MP_TAC (fetch "-" "get_fact_ind")
  \\ FULL_SIMP_TAC std_ss [get_fact_def,int_negate_def,int_cmp_sem_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `v1` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `v2` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Q.PAT_ASSUM `Lit xxx = e` (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
  \\ FULL_SIMP_TAC (srw_ss()) [opb_lookup_def,evaluate_Lit]
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) [do_tapp_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [case_LEMMA]
  \\ Q.PAT_ASSUM `Litv xx = yy` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [INT_NOT_LT,INT_NOT_LE,int_ge,int_gt]
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) > jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) >= jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) < jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) <= jjj` MP_TAC)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ intLib.COOPER_TAC);

val get_fact_thm_F = prove(
  ``!x env.
      evaluate' s env x (s1,Rval (Litv (Bool F))) ==>
      int_cmp_sem env T (int_negate (get_fact x))``,
  HO_MATCH_MP_TAC (fetch "-" "get_fact_ind")
  \\ FULL_SIMP_TAC std_ss [get_fact_def,int_negate_def,int_cmp_sem_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `v1` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `v2` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Q.PAT_ASSUM `Lit xxx = e` (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
  \\ FULL_SIMP_TAC (srw_ss()) [opb_lookup_def,evaluate_Lit]
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) [do_tapp_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [case_LEMMA]
  \\ Q.PAT_ASSUM `Litv xx = yy` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [INT_NOT_LT,INT_NOT_LE,int_ge,int_gt]
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) > jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) >= jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) < jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) <= jjj` MP_TAC)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ intLib.COOPER_TAC);

val decide_guard_thm = prove(
  ``!env b x.
      EVERY (int_cmp_sem env T) b ==>
      !res. (decide_guard x b = SOME res) ==> int_cmp_sem env res x``,
  STRIP_TAC \\ Induct \\ Cases_on `x` \\ SIMP_TAC std_ss [decide_guard_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [decide_guard_def,EVERY_DEF]
  \\ Cases_on `s' = s` \\ FULL_SIMP_TAC std_ss [decide_guard_def,EVERY_DEF]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [int_cmp_sem_def]
  \\ intLib.COOPER_TAC);

val int_cmp_keep_def = Define `
  (int_cmp_keep vs IntUnkown = F) /\
  (int_cmp_keep vs (IntLessEq i v) = ~MEM v vs) /\
  (int_cmp_keep vs (IntGreater i v) = ~MEM v vs)`;

val int_read_exp_def = Define `
  (int_read_exp (Var v _) = SOME (v,0)) /\
  (int_read_exp (App (Opn Plus) (Var v _) ((Lit (IntLit i)))) = SOME (v,i)) /\
  (int_read_exp (App (Opn Minus) (Var v _) ((Lit (IntLit i)))) = SOME (v,0-i)) /\
  (int_read_exp _ = NONE)`;

val int_cmp_apply_def = Define `
  (int_cmp_apply (name,v,i) [] = []) /\
  (int_cmp_apply (name,v,i) (IntUnkown::xs) = int_cmp_apply (name,v,i) xs) /\
  (int_cmp_apply (name,v,i) ((IntLessEq (j:int) w)::xs) =
     if v = w then IntLessEq (j+i) name :: int_cmp_apply (name,v,i) xs
              else int_cmp_apply (name,v,i) xs) /\
  (int_cmp_apply (name,v,i) ((IntGreater j w)::xs) =
     if v = w then IntGreater (j+i) name :: int_cmp_apply (name,v,i) xs
              else int_cmp_apply (name,v,i) xs)`;

val int_cmp_let_def = Define `
  int_cmp_let name x b =
    case int_read_exp x of
      NONE => []
    | (SOME (v,i)) => int_cmp_apply (name,v,i) b`;

val INT_IF_OPT_def = tDefine "INT_IF_OPT" `
  (INT_IF_OPT b (Lit v) = Lit v) /\
  (INT_IF_OPT b (Raise ex) = Raise ex) /\
  (INT_IF_OPT b (Var name t) = Var name t) /\
  (INT_IF_OPT b (Con tag xs) = Con tag (MAP (INT_IF_OPT b) xs)) /\
  (INT_IF_OPT b (Fun name tt x) = Fun name tt x) /\
  (INT_IF_OPT b (Uapp uop x1) = Uapp uop (INT_IF_OPT b x1)) /\
  (INT_IF_OPT b (App op x1 x2) = App op (INT_IF_OPT b x1) (INT_IF_OPT b x2)) /\
  (INT_IF_OPT b (Log l x1 x2) = Log l (INT_IF_OPT b x1) (INT_IF_OPT b x2)) /\
  (INT_IF_OPT b (If x1 x2 x3) =
     case decide_guard (get_fact x1) b of
       NONE => If (INT_IF_OPT b x1) (INT_IF_OPT (add_pos_fact x1 b) x2)
                                    (INT_IF_OPT (add_neg_fact x1 b) x3)
     | SOME T => (INT_IF_OPT b x2)
     | SOME F => (INT_IF_OPT b x3)) /\
  (INT_IF_OPT b (Mat x ys) = Mat (INT_IF_OPT b x) (MAP (\(p,x). (p,INT_IF_OPT (FILTER (int_cmp_keep (pat_vars p)) b) x)) ys)) /\
  (INT_IF_OPT b (Let oo name tt x1 x2) = Let oo name tt (INT_IF_OPT b x1)
     (INT_IF_OPT (int_cmp_let name x1 b ++ FILTER (int_cmp_keep [name]) b) x2)) /\
  (INT_IF_OPT b (Letrec oo z1 z2) = Letrec oo z1 z2) /\
  (INT_IF_OPT b other = other)`
 (WF_REL_TAC `measure (exp_size o SND)` THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC MEM_exp_size1 THEN IMP_RES_TAC MEM_exp_size2 THEN DECIDE_TAC)

val MAT_INT_IF_OPT_def = Define `
  MAT_INT_IF_OPT b ys =
    MAP (\(p,x'). (p,INT_IF_OPT (FILTER (int_cmp_keep (pat_vars p)) b) x')) ys`;

val INT_IF_OPT_def = INT_IF_OPT_def |> REWRITE_RULE [GSYM MAT_INT_IF_OPT_def]

val decide_guard_IMP = prove(
  ``!b x res. (decide_guard x b = SOME res) ==> ~(x = IntUnkown)``,
  Induct \\ FULL_SIMP_TAC std_ss [decide_guard_def]);

val IMP_int_negate = prove(
  ``!x. ~(x = IntUnkown) ==> ~(int_negate x = IntUnkown)``,
  Cases \\ EVAL_TAC);

val int_cmp_sem_NOT = prove(
  ``!x env. int_cmp_sem env F x /\ int_cmp_sem env T x /\ ~(x = IntUnkown) ==> F``,
  REPEAT STRIP_TAC \\ Cases_on `x`
  \\ FULL_SIMP_TAC (srw_ss()) [int_cmp_sem_def]
  \\ FULL_SIMP_TAC (srw_ss()) [int_cmp_sem_def]
  \\ FULL_SIMP_TAC std_ss [INT_NOT_LT,INT_NOT_LE,int_ge,int_gt]
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) > jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) >= jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) < jjj` MP_TAC)
  \\ REPEAT (Q.PAT_ASSUM `(iii:int) <= jjj` MP_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ intLib.COOPER_TAC);

val int_cmp_sem_negate = prove(
  ``!x env. int_cmp_sem env T (int_negate x) ==> int_cmp_sem env F x``,
  Cases \\ FULL_SIMP_TAC std_ss [int_cmp_sem_def,int_negate_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [] \\ intLib.COOPER_TAC);

val isRval_def = Define `(isRval (Rval _) = T) /\ (isRval _ = F)`;

val lookup_ZIP_APPEND = prove(
  ``!xs ys s x.
      (LENGTH xs = LENGTH ys) /\ ~(MEM s xs) ==>
      (lookup s (ZIP (xs,ys) ++ x) = lookup s x)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1,ZIP,lookup_def]);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b3 ==> b2) ==> ((b1 ==> b3) ==> b2)``

val ZIP_APPEND = prove(
  ``!xs ys xs1 ys2.
      (LENGTH xs = LENGTH ys) /\ (LENGTH xs1 = LENGTH ys1) ==>
      (ZIP (xs,ys) ++ ZIP (xs1,ys1) = ZIP (xs++xs1, ys++ys1))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val pmatch_lemma = prove(
   ``!p x2 env env1.
       (pmatch' s p x2 env = Match env1) ==>
       ?ys. (LENGTH ys = LENGTH (pat_vars p)) /\
            (env1 = ZIP (REVERSE (pat_vars p), ys) ++ env)``,
  STRIP_TAC \\ completeInduct_on `pat_size p` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `p` \\ FULL_SIMP_TAC (srw_ss()) [pmatch'_def,pat_vars_def,bind_def]
  THEN1 (Q.EXISTS_TAC `[x2]` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1 (Cases_on `x2`
    \\ FULL_SIMP_TAC (srw_ss()) [pmatch'_def,pat_vars_def,bind_def]
    \\ Cases_on `l = l'` \\ Cases_on `lit_same_type l l'`
    \\ FULL_SIMP_TAC (srw_ss()) [pmatch'_def,pat_vars_def,bind_def,LENGTH_NIL])
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `x2` \\ TRY (Cases_on `o'`) \\ TRY (Cases_on `o''`)
  \\ FULL_SIMP_TAC (srw_ss()) [pmatch'_def,pat_vars_def,bind_def]
  \\ SRW_TAC [] [] \\ REPEAT (POP_ASSUM MP_TAC)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Q.SPEC_TAC (`l'`,`l1`)
  \\ Q.SPEC_TAC (`env`,`env`) \\ Q.SPEC_TAC (`env1`,`env1`) THEN1
   (Induct_on `l` \\ Cases_on `l1` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,FLAT,LENGTH,LENGTH_NIL,ZIP,pmatch'_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ Cases_on `pmatch' s h' h env` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_ASSUM `!env1 env l1. bbb ==> bbbb` (MP_TAC o Q.SPECL [`env1`,`l'`,`t`])
    \\ FULL_SIMP_TAC std_ss []
    THEN (MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [pat_size_def]
        \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
        \\ Q.EXISTS_TAC `x2'` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`h'`,`h`,`env`])
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [pat_size_def] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `ys ++ ys'`
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,APPEND_ASSOC,AC ADD_ASSOC ADD_COMM]
      \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,LENGTH_REVERSE]))
  THEN1
   (Cases_on `store_lookup n s` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!pp. bbb` (MP_TAC o Q.SPECL [`p'`,`x`,`env`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC IMP_IMP \\ FULL_SIMP_TAC std_ss [pat_vars_def,pat_size_def]
    \\ DECIDE_TAC)) |> GEN_ALL;

val int_read_exp_IMP = prove(
  ``!x2. (int_read_exp x2 = SOME (s,r)) ==>
         ((x2 = Var s) /\ (r = 0)) \/
         (x2 = (App (Opn Plus) (Var s) ((Lit (IntLit r))))) \/
         (x2 = (App (Opn Minus) (Var s) ((Lit (IntLit (0-r))))))``,
  HO_MATCH_MP_TAC (fetch "-" "int_read_exp_ind")
  \\ FULL_SIMP_TAC (srw_ss()) [int_read_exp_def]
  \\ REPEAT STRIP_TAC
  \\ intLib.COOPER_TAC);

val int_cmp_let_thm = prove(
  ``EVERY (int_cmp_sem x1 T) b /\ evaluate' s0 x1 x2 (s1,Rval (v)) ==>
    EVERY (int_cmp_sem (bind n v x1) T) (int_cmp_let n x2 b)``,
  SIMP_TAC std_ss [int_cmp_let_def]
  \\ Cases_on `int_read_exp x2` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Induct_on `b` \\ FULL_SIMP_TAC (srw_ss()) [int_cmp_apply_def]
  \\ Cases \\ FULL_SIMP_TAC (srw_ss()) [int_cmp_apply_def,int_cmp_sem_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `q = s` \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [int_cmp_sem_def,bind_def,lookup_def]
  THEN (IMP_RES_TAC int_read_exp_IMP \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `evaluate' s0 xx yy zz` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC do_app_IMP
    \\ FULL_SIMP_TAC (srw_ss()) [do_app_def,evaluate_Lit]
    \\ Q.PAT_ASSUM `evaluate' s0 xx yy zz` MP_TAC
    \\ Q.PAT_ASSUM `Lit xx = yy` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `evaluate' s0 xx yy zz` MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ FULL_SIMP_TAC (srw_ss()) [opn_lookup_def,evaluate_Lit]
    \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `-r = i2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [evaluate_Lit]));

val decide_guard_IntUnkown = prove(
  ``!xs. decide_guard IntUnkown xs = NONE``,
  Induct \\ FULL_SIMP_TAC std_ss [decide_guard_def]);

val store_same_LEMMA = prove(
  ``(decide_guard (get_fact x2) b = SOME x) /\
    evaluate' s x1 x2 (s',Rval (Litv (Bool bb))) ==> (s = s')``,
  Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown]
  \\ Cases_on `o'` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown]
  \\ Cases_on `o''` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown]
  \\ Cases_on `e0` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown]
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown])
  \\ TRY (Cases_on `l'` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [get_fact_def,decide_guard_IntUnkown])
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def, Once evaluate'_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def, Once evaluate'_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def, Once evaluate'_cases]
  \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `v1` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `v2` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT (Q.PAT_ASSUM `Lit vv = xx` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC std_ss [evaluate_Lit]);

val INT_IF_OPT_LEMMA = prove(
  ``(!s x1 x2 x3. evaluate' s x1 x2 x3 ==>
       !b. EVERY (int_cmp_sem x1 T) b /\ isRval (SND x3) ==>
           evaluate' s x1 (INT_IF_OPT b x2) x3) /\
    (!s x1 x2 x3. evaluate_list' s x1 x2 x3 ==>
       !b. EVERY (int_cmp_sem x1 T) b /\ isRval (SND x3) ==>
           evaluate_list' s x1 (MAP (INT_IF_OPT b) x2) x3) /\
    (!s x1 x2 x3 x4. evaluate_match' s x1 x2 x3 x4 ==>
       !b. EVERY (int_cmp_sem x1 T) b /\ isRval (SND x4) ==>
           evaluate_match' s x1 x2 (MAT_INT_IF_OPT b x3) x4)``,
  ONCE_REWRITE_TAC [two_assums]
  \\ HO_MATCH_MP_TAC evaluate'_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [INT_IF_OPT_def,isRval_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ TRY (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ NO_TAC)
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v`
    \\ FULL_SIMP_TAC std_ss [do_log_def]
    \\ Cases_on `op` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `b'` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `v`
    \\ FULL_SIMP_TAC std_ss [do_log_def] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ2_TAC \\ DISJ1_TAC \\ Q.EXISTS_TAC `v`
    \\ FULL_SIMP_TAC std_ss [do_log_def] \\ METIS_TAC [])
  THEN1
   (Cases_on `decide_guard (get_fact x2) b`
    \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (FULL_SIMP_TAC std_ss [do_if_def]
      \\ REPEAT (BasicProvers.FULL_CASE_TAC)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
      \\ DISJ1_TAC \\ Q.EXISTS_TAC `v` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
      \\ Q.EXISTS_TAC `s'` \\ FULL_SIMP_TAC std_ss []
      THEN1 (Q.PAT_ASSUM `!b.bbb` MATCH_MP_TAC
        \\ FULL_SIMP_TAC std_ss [add_neg_fact_def,EVERY_DEF]
        \\ MATCH_MP_TAC (get_fact_thm_F |> GEN_ALL)
        \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
      THEN1 (Q.PAT_ASSUM `!b.bbb` MATCH_MP_TAC
        \\ FULL_SIMP_TAC std_ss [add_pos_fact_def,EVERY_DEF]
        \\ MATCH_MP_TAC (get_fact_thm_T |> GEN_ALL)
        \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []))
    \\ IMP_RES_TAC decide_guard_thm
    \\ FULL_SIMP_TAC std_ss [do_if_def]
    \\ Cases_on `v = Litv (Bool T)` \\ FULL_SIMP_TAC std_ss []
    \\ `s' = s` by METIS_TAC [store_same_LEMMA]
    \\ FULL_SIMP_TAC std_ss []
    THEN1 (Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC get_fact_thm_T
      \\ IMP_RES_TAC decide_guard_IMP
      \\ IMP_RES_TAC int_cmp_sem_NOT)
    THEN1 (Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC get_fact_thm_F
      \\ IMP_RES_TAC decide_guard_IMP
      \\ IMP_RES_TAC int_cmp_sem_negate
      \\ IMP_RES_TAC int_cmp_sem_NOT))
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
    \\ DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`v`,`s'`] \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!b.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_APPEND]
    \\ FULL_SIMP_TAC std_ss [EVERY_FILTER,int_cmp_let_thm]
    \\ IMP_RES_TAC int_cmp_let_thm
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ Cases_on `x`
    \\ FULL_SIMP_TAC std_ss [int_cmp_sem_def,int_cmp_keep_def]
    \\ Q.EXISTS_TAC `j` \\ FULL_SIMP_TAC std_ss [MEM,lookup_def,bind_def])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (RES_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MAT_INT_IF_OPT_def,MAP]
      \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
      \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
      \\ FULL_SIMP_TAC std_ss [EVERY_FILTER]
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ IMP_RES_TAC pmatch_lemma
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x`
      \\ FULL_SIMP_TAC std_ss [int_cmp_sem_def,int_cmp_keep_def]
      \\ Q.EXISTS_TAC `j` \\ FULL_SIMP_TAC std_ss []
      \\ `~MEM s' (REVERSE (pat_vars p))` by FULL_SIMP_TAC std_ss [MEM_REVERSE]
      \\ FULL_SIMP_TAC std_ss [lookup_ZIP_APPEND,LENGTH_REVERSE])
  THEN1
     (FULL_SIMP_TAC std_ss [MAT_INT_IF_OPT_def,MAP]
      \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases] \\ METIS_TAC []));

val INT_IF_OPT_THM =
  INT_IF_OPT_LEMMA |> CONJUNCT1 |> Q.SPECL [`s`,`env`,`exp`,`t,Rval res`]
    |> SIMP_RULE std_ss [isRval_def,PULL_FORALL] |> Q.SPEC `[]`
    |> REWRITE_RULE [EVERY_DEF]
    |> Q.GEN `res` |> Q.GEN `t` |> Q.GEN `exp` |> Q.GEN `env` |> Q.GEN `s`

*)

(* top-level optimiser *)

val OPTIMISE_def = Define `
  OPTIMISE =
    BOTTOM_UP_OPT (opt_sub_add o let_id) o
    (* INT_IF_OPT [] o *)
    BOTTOM_UP_OPT abs2let`;

val Eval_OPTIMISE = store_thm("Eval_OPTIMISE",
  ``Eval env exp P ==> Eval env (OPTIMISE exp) P``,
  SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss [OPTIMISE_def]
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  \\ SIMP_TAC std_ss [opt_sub_add_thm,let_id_thm]
  (* \\ MATCH_MP_TAC INT_IF_OPT_THM *)
  \\ MATCH_MP_TAC BOTTOM_UP_OPT_THM
  \\ ASM_SIMP_TAC std_ss [abs2let_thm]);

val _ = export_theory();
