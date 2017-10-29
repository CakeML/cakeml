open preamble astTheory libTheory bigStepTheory semanticPrimitivesTheory whileTheory;
open terminationTheory ml_translatorLib ml_translatorTheory ml_progLib;

val _ = new_theory "std_prelude";

val register_type = abs_register_type;
val translate = abs_translate;

(* type registration *)

val _ = register_type ``:ordering``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:'a # 'b``;

(* pair *)

val res = translate FST;
val res = translate SND;
val res = translate CURRY_DEF;
val res = translate UNCURRY;

(* combin *)

val _ = next_ml_names := ["o"];
val res = translate o_DEF;
val res = translate I_THM;
val res = translate C_DEF;
val res = translate K_DEF;
val res = translate S_DEF;
val res = translate UPDATE_def;
val res = translate W_DEF;

(* sum *)

val res = translate ISL;
val res = translate ISR;
val res = translate OUTL;
val res = translate OUTR;
val res = translate SUM_MAP_def;

val outl_side_def = Q.prove(
  `outl_side = ISL`,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "outl_side_def"])
  |> update_precondition;

val outr_side_def = Q.prove(
  `outr_side = ISR`,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "outr_side_def"])
  |> update_precondition;

(* arithmetic *)

val EXP_AUX_def = Define `
  EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n-1:num) (m * k:num)`;

val EXP_AUX_THM = Q.prove(
  `!n k. EXP_AUX m n (m**k) = m**(k+n)`,
  Induct THEN SIMP_TAC std_ss [EXP,Once EXP_AUX_def,ADD1]
  THEN ASM_SIMP_TAC std_ss [GSYM EXP]
  THEN FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`n`,`0`] |> SIMP_RULE std_ss [EXP] |> GSYM;

val res = translate EXP_AUX_def;
val res = translate EXP_AUX_THM; (* tailrec version of EXP *)
val res = translate MIN_DEF;
val res = translate MAX_DEF;
val res = translate arithmeticTheory.EVEN_MOD2;
val res = translate (REWRITE_RULE [EVEN_MOD2,DECIDE ``~(n = 0) = (0 < n:num)``] ODD_EVEN);
val res = translate FUNPOW;
val res = translate ABS_DIFF_def;
val res = translate (DECIDE ``PRE n = n-1``);

(* while, owhile and least *)

val IS_SOME_OWHILE_THM = Q.prove(
  `!g f x. (IS_SOME (OWHILE g f x)) =
            ?n. ~ g (FUNPOW f n x) /\ !m. m < n ==> g (FUNPOW f m x)`,
  REPEAT STRIP_TAC THEN Cases_on `OWHILE g f x`
  THEN FULL_SIMP_TAC (srw_ss()) [OWHILE_EQ_NONE]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def]
  THEN Q.EXISTS_TAC `LEAST n. ~g (FUNPOW f n x)`
  THEN (Q.INST [`P`|->`\n. ~g (FUNPOW f n x)`] FULL_LEAST_INTRO
      |> SIMP_RULE std_ss [] |> IMP_RES_TAC)
  THEN ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC LESS_LEAST THEN FULL_SIMP_TAC std_ss []);

val WHILE_ind = Q.store_thm("WHILE_ind",
  `!P. (!p g x. (p x ==> P p g (g x)) ==> P p g x) ==>
        !p g x. IS_SOME (OWHILE p g x) ==> P p g x`,
  SIMP_TAC std_ss [IS_SOME_OWHILE_THM,PULL_EXISTS,PULL_FORALL]
  THEN Induct_on `n` THEN SRW_TAC [] []
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN Q.PAT_X_ASSUM `!x1 x2 x3 x4. bbb` MATCH_MP_TAC
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [FUNPOW]
  THEN `SUC m < SUC n` by DECIDE_TAC
  THEN METIS_TAC [FUNPOW]);

val OWHILE_ind = save_thm("OWHILE_ind",WHILE_ind);

val _ = add_preferred_thy "-";

val _ = next_ml_names := ["while"];
val res = translate WHILE;
val res = translate OWHILE_THM;

val SUC_LEMMA = Q.store_thm("SUC_LEMMA",`SUC = \x. x+1`,SIMP_TAC std_ss [FUN_EQ_THM,ADD1]);

val LEAST_LEMMA = Q.prove(
  `$LEAST P = WHILE (\x. ~(P x)) (\x. x + 1) 0`,
  SIMP_TAC std_ss [LEAST_DEF,o_DEF,SUC_LEMMA]);

val res = translate LEAST_LEMMA;

(*
val FUNPOW_LEMMA = Q.prove(
  `!n m. FUNPOW (\x. x + 1) n m = n + m`,
  Induct THEN FULL_SIMP_TAC std_ss [FUNPOW,ADD1,AC ADD_COMM ADD_ASSOC]);

val least_side_thm = Q.prove(
  `!s. least_side s = ~(s = {})`,
  SIMP_TAC std_ss [fetch "-" "least_side_def"]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def,FUNPOW_LEMMA,FUN_EQ_THM,EMPTY_DEF]
  THEN METIS_TAC [IS_SOME_DEF])
  |> update_precondition;
*)

val _ = (print_asts := true);

val _ = export_theory();
