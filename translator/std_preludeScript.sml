(*
  Translations of various useful HOL functions and datatypes, to serve as a
  starting point for further translations.
*)

open preamble astTheory semanticPrimitivesTheory whileTheory;
open evaluateTheory ml_translatorLib ml_translatorTheory ml_progLib;

val _ = new_theory "std_prelude";

(* type registration *)

val _ = (use_full_type_names := false)

val _ = register_type ``:ordering``;
val _ = register_type ``:'a option``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a + 'b``;
val _ = register_type ``:'a app_list``;

(* pair *)

val res = translate FST;
val res = translate SND;
val res = translate CURRY_DEF;
val res = translate UNCURRY;

(* combin *)

val _ = next_ml_names := ["o"];
val res = translate o_DEF;
val _ = next_ml_names := ["id"];
val res = translate I_THM;
val _ = next_ml_names := ["flip"];
val res = translate C_DEF;
val _ = next_ml_names := ["const"];
val res = translate K_DEF;
val res = translate UPDATE_def;

(* arithmetic *)

Definition EXP_AUX_def:
  EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n-1:num) (m * k:num)
End

val EXP_AUX_THM = Q.prove(
  `!n k. EXP_AUX m n (m**k) = m**(k+n)`,
  Induct THEN SIMP_TAC std_ss [EXP,Once EXP_AUX_def,ADD1]
  THEN ASM_SIMP_TAC std_ss [GSYM EXP]
  THEN FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`n`,`0`] |> SIMP_RULE std_ss [EXP] |> GSYM;

val _ = next_ml_names := ["exp"];
val res = translate EXP_AUX_def;

val _ = next_ml_names := ["exp"];
val res = translate EXP_AUX_THM; (* tailrec version of EXP *)

val res = translate MIN_DEF;
val res = translate MAX_DEF;
val res = translate arithmeticTheory.EVEN_MOD2;
val res = translate (REWRITE_RULE [EVEN_MOD2,DECIDE ``~(n = 0) = (0 < n:num)``] ODD_EVEN);
val res = translate FUNPOW;

val res = translate ABS_DIFF_def;

val res = translate (DECIDE ``PRE n = n-1`` |> REWRITE_RULE [GSYM sub_check_def]);

(* while, owhile and least *)

Triviality IS_SOME_OWHILE_THM:
  !g f x. (IS_SOME (OWHILE g f x)) =
            ?n. ~ g (FUNPOW f n x) /\ !m. m < n ==> g (FUNPOW f m x)
Proof
  REPEAT STRIP_TAC THEN Cases_on `OWHILE g f x`
  THEN FULL_SIMP_TAC (srw_ss()) [OWHILE_EQ_NONE]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def]
  THEN Q.EXISTS_TAC `LEAST n. ~g (FUNPOW f n x)`
  THEN (Q.INST [`P`|->`\n. ~g (FUNPOW f n x)`] FULL_LEAST_INTRO
      |> SIMP_RULE std_ss [] |> IMP_RES_TAC)
  THEN ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC LESS_LEAST THEN FULL_SIMP_TAC std_ss []
QED

Theorem WHILE_ind:
   !P. (!p g x. (p x ==> P p g (g x)) ==> P p g x) ==>
        !p g x. IS_SOME (OWHILE p g x) ==> P p g x
Proof
  SIMP_TAC std_ss [IS_SOME_OWHILE_THM,PULL_EXISTS,PULL_FORALL]
  THEN Induct_on `n` THEN SRW_TAC [] []
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN Q.PAT_X_ASSUM `!x1 x2 x3 x4. bbb` MATCH_MP_TAC
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [FUNPOW]
  THEN `SUC m < SUC n` by DECIDE_TAC
  THEN METIS_TAC [FUNPOW]
QED

Theorem OWHILE_ind =
  WHILE_ind

val _ = add_preferred_thy "-";

val _ = next_ml_names := ["while"];
val res = translate WHILE;
val res = translate OWHILE_THM;

Theorem SUC_LEMMA:
  SUC = \x. x+1
Proof
SIMP_TAC std_ss [FUN_EQ_THM,ADD1]
QED

Triviality LEAST_LEMMA:
  $LEAST P = WHILE (\x. ~(P x)) (\x. x + 1) 0
Proof
  SIMP_TAC std_ss [LEAST_DEF,o_DEF,SUC_LEMMA]
QED

val res = translate LEAST_LEMMA;

Triviality FUNPOW_LEMMA:
  !n m. FUNPOW (\x. x + 1) n m = n + m
Proof
  Induct THEN FULL_SIMP_TAC std_ss [FUNPOW,ADD1,AC ADD_COMM ADD_ASSOC]
QED

val least_side_thm = Q.prove(
  `!s. least_side s = ~(s = {})`,
  SIMP_TAC std_ss [fetch "-" "least_side_def"]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def,FUNPOW_LEMMA,FUN_EQ_THM,EMPTY_DEF]
  THEN METIS_TAC [IS_SOME_DEF])
  |> update_precondition;

(* app_list *)

val _ = ml_prog_update open_local_block;
val r = translate miscTheory.append_aux_def;
val _ = ml_prog_update open_local_in_block;

val r = translate miscTheory.append_def;

val _ = ml_prog_update close_local_blocks;

val _ = (print_asts := true);

val _ = export_theory();
