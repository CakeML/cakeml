open HolKernel Parse boolLib bossLib lcsymtacs;

val _ = new_theory "bytecodeLabels";

open listTheory arithmeticTheory finite_mapTheory pred_setTheory rich_listTheory
open relationTheory bytecodeTheory;

val REVERSE = Tactical.REVERSE

infix \\ val op \\ = op THEN;

(* prove that label removal doesn't change semantics *)

val collect_labels_def = Define `
  (collect_labels [] p l = FEMPTY) /\
  (collect_labels (x::xs) p l =
     case x of
     | Label n => ((collect_labels xs p l) |+ (n,p))
     | _ => collect_labels xs ((p:num) + l x + 1) l)`;

val all_labels_def = Define `
  all_labels l code = collect_labels code 0 l`;

val inst_labels_def = Define `
  (inst_labels f [] = []) /\
  (inst_labels f (Label n :: xs) = inst_labels f xs) /\
  (inst_labels f (PushPtr (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => Lab l | SOME a => Addr a in
       PushPtr addr :: inst_labels f xs) /\
  (inst_labels f (Call (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => Lab l | SOME a => Addr a in
       Call addr :: inst_labels f xs) /\
  (inst_labels f (Jump (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => Lab l | SOME a => Addr a in
       Jump addr :: inst_labels f xs) /\
  (inst_labels f (JumpIf (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => Lab l | SOME a => Addr a in
       JumpIf addr :: inst_labels f xs) /\
  (inst_labels f (x::xs) = x :: inst_labels f xs)`
val inst_labels_def = save_thm("inst_labels_def",
  inst_labels_def |> SIMP_RULE std_ss [LET_DEF]);

val code_labels_def = Define `
  code_labels l code = inst_labels (all_labels l code) code`;

val strip_labels_def = Define `
  strip_labels s =
    s with <| code := code_labels s.inst_length s.code |>`;

val length_ok_def = Define `
  length_ok l =
    !a. (l (Call a) = l (Call ARB)) /\
        (l (Jump a) = l (Jump ARB)) /\
        (l (JumpIf a) = l (JumpIf ARB)) /\
        (l (PushPtr a) = l (PushPtr ARB))`;

val ilength_def = Define `
  ilength l i = if is_Label i then 0 else l i + 1:num`;

val code_length_def = Define `
  code_length l code = SUM (MAP (ilength l) code)`;

val next_addr_thm = store_thm("next_addr_thm",
  ``!xs l. next_addr l xs = code_length l xs``,
  Induct \\ SRW_TAC [] [code_length_def,ilength_def,ADD1]
  \\ FULL_SIMP_TAC std_ss []);

val bc_fetch_aux_SOME = store_thm("bc_fetch_aux_SOME",
  ``!xs l p x.
      (bc_fetch_aux xs l p = SOME x) ==>
      ?ys1 ys2. (xs = ys1 ++ [x] ++ ys2) /\ (p = SUM (MAP (ilength l) ys1)) /\
                ~(is_Label x)``,
  Induct \\ SIMP_TAC std_ss [bc_fetch_aux_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `is_Label h` \\ FULL_SIMP_TAC std_ss [] THEN1
    (RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
     \\ FULL_SIMP_TAC std_ss [APPEND,MAP,SUM,ilength_def])
  \\ Cases_on `p = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.LIST_EXISTS_TAC [`[]`,`xs`] \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11,MAP,SUM]
    \\ METIS_TAC [])
  \\ Cases_on `p < l h + 1` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [APPEND,MAP,SUM,ilength_def]
  \\ DECIDE_TAC);

val strip_labels_pc = store_thm("strip_labels_pc",
  ``(strip_labels s).pc = s.pc``,
  SIMP_TAC (srw_ss()) [strip_labels_def]);

val strip_labels_inst_length = store_thm("strip_labels_inst_length",
  ``(strip_labels s).inst_length = s.inst_length``,
  SIMP_TAC (srw_ss()) [strip_labels_def]);

val strip_labels_output = store_thm("strip_labels_output",
  ``(strip_labels s).output = s.output``,
  SIMP_TAC (srw_ss()) [strip_labels_def]);

val inst_labels_APPEND = store_thm("inst_labels_APPEND",
  ``!xs ys f. inst_labels f (xs ++ ys) = inst_labels f xs ++ inst_labels f ys``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,inst_labels_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [APPEND,inst_labels_def]
  \\ Cases_on `l` \\ FULL_SIMP_TAC std_ss [APPEND,inst_labels_def]);

val bc_fetch_IMP = prove(
  ``(bc_fetch s1 = SOME x) /\ length_ok s1.inst_length ==>
    (bc_fetch (strip_labels s1) =
     SOME (HD (inst_labels (all_labels s1.inst_length s1.code) [x])))``,
  SIMP_TAC (srw_ss()) [bc_fetch_def,strip_labels_def,code_labels_def]
  \\ Q.ABBREV_TAC `f = all_labels s1.inst_length s1.code`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC bc_fetch_aux_SOME
  \\ FULL_SIMP_TAC std_ss [inst_labels_APPEND]
  \\ POP_ASSUM MP_TAC
  \\ Q.PAT_ASSUM `length_ok s1.inst_length` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `ys1` THEN1
   (TRY (Cases_on `l`) \\ FULL_SIMP_TAC std_ss [inst_labels_def,APPEND,SUM,MAP]
    \\ TRY (Cases_on `x`) \\ FULL_SIMP_TAC std_ss [inst_labels_def,HD,APPEND]
    \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_def,is_Label_def]
    \\ TRY (Cases_on `l`) \\ FULL_SIMP_TAC std_ss [inst_labels_def,APPEND,SUM,MAP]
    \\ TRY (Cases_on `x`) \\ FULL_SIMP_TAC std_ss [inst_labels_def,HD,APPEND]
    \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_def,is_Label_def])
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC std_ss [inst_labels_def,APPEND,bc_fetch_aux_def,
       is_Label_def,ilength_def,MAP,SUM]
  \\ FULL_SIMP_TAC std_ss [length_ok_def] \\ DECIDE_TAC);

val bc_fetch_aux_IFF = store_thm("bc_fetch_aux_IFF",
  ``(bc_fetch_aux xs l p = SOME x) <=>
    (?ys1 ys2.
       xs = ys1 ++ [x] ++ ys2 /\ p = SUM (MAP (ilength l) ys1) /\
       ~is_Label x)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [bc_fetch_aux_SOME]
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `ys1` \\ FULL_SIMP_TAC std_ss [APPEND,MAP,SUM]
  \\ SIMP_TAC std_ss [bc_fetch_aux_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `is_Label h` \\ FULL_SIMP_TAC std_ss []
  THEN1 (ASM_SIMP_TAC std_ss [ilength_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ilength_def]
  \\ DECIDE_TAC);

val code_length_inst_labels = store_thm("code_length_inst_labels",
  ``!xs l f. length_ok l ==> (code_length l (inst_labels f xs) =
                              code_length l xs)``,
  Induct \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [inst_labels_def]
  \\ Cases_on `h` \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l'`)
  \\ ASM_SIMP_TAC (srw_ss()) [inst_labels_def,code_length_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [code_length_def]
  \\ FULL_SIMP_TAC std_ss [ilength_def,bytecodeTheory.is_Label_def,
       LET_DEF,MAP,SUM] \\ FULL_SIMP_TAC std_ss [length_ok_def]);

val code_length_strip_labels = store_thm("code_length_strip_labels",
  ``length_ok s.inst_length ==>
    (code_length s.inst_length (strip_labels s).code =
     code_length s.inst_length s.code)``,
  SIMP_TAC (srw_ss()) [strip_labels_def]
  \\ SIMP_TAC std_ss [code_labels_def,code_length_inst_labels])

val inst_labels_SING = prove(
  ``!h. ~is_Label h ==> (inst_labels f [h] ++ xs = HD (inst_labels f [h])::xs)``,
  Cases \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def]);

val bc_fetch_NOT_Label = prove(
  ``(bc_fetch s = SOME x) ==> ~(is_Label x)``,
  SIMP_TAC std_ss [bc_fetch_def] \\ Q.SPEC_TAC (`s.pc`,`p`)
  \\ Q.SPEC_TAC (`s.code`,`xs`) \\ Induct
  \\ SIMP_TAC std_ss [bc_fetch_aux_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val bc_fetch_strip_labels_BACK = prove(
  ``length_ok s.inst_length /\
    (bc_fetch (strip_labels s) = SOME x) ==>
    ?y. (bc_fetch s = SOME y) /\
        (x = HD (inst_labels (all_labels s.inst_length s.code) [y]))``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_IFF,bc_fetch_def]
  \\ FULL_SIMP_TAC std_ss [strip_labels_inst_length,strip_labels_pc]
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,code_labels_def]
  \\ Q.ABBREV_TAC `f = all_labels s.inst_length s.code`
  \\ FULL_SIMP_TAC std_ss [GSYM code_length_def,code_length_inst_labels]
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`ys2`,`ys2`) \\ Q.SPEC_TAC (`ys1`,`ys1`)
  \\ Q.SPEC_TAC (`s.code`,`code`) \\ Induct
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  THEN1 (SRW_TAC [] [inst_labels_def]) \\ STRIP_TAC
  \\ Cases_on `is_Label h` THEN1
   (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [is_Label_def,inst_labels_def]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`y`,`Label n::ys1'`,`ys2'`]
    \\ FULL_SIMP_TAC std_ss [APPEND,code_length_def,MAP,SUM,
         ilength_def,is_Label_def])
  \\ `h::code = [h] ++ code` by FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss [inst_labels_APPEND]
  \\ REPEAT STRIP_TAC \\ Cases_on `ys1` THEN1
   (Q.LIST_EXISTS_TAC [`h`,`[]`] \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
    \\ Cases_on `h`
    \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
    \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def])
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [inst_labels_SING,APPEND,CONS_11]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`y`,`h::ys1'`,`ys2'`]
  \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss [code_length_def,SUM,MAP]
  \\ FULL_SIMP_TAC std_ss [length_ok_def]
  \\ FULL_SIMP_TAC std_ss [ilength_def]
  \\ Cases_on `h`
  \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def]
  \\ Cases_on `h'`
  \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def]);

val bc_fetch_strip_labels = store_thm("bc_fetch_strip_labels",
  ``length_ok s.inst_length ==>
    (bc_fetch (strip_labels s) = SOME (Stop b) <=> bc_fetch s = SOME (Stop b))``,
  REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC bc_fetch_IMP \\ FULL_SIMP_TAC std_ss [inst_labels_def,HD])
  \\ IMP_RES_TAC bc_fetch_strip_labels_BACK \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ IMP_RES_TAC bc_fetch_NOT_Label
  \\ Cases_on `y` \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def]
  \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def]);

val strip_labels_pc = prove(
  ``strip_labels (s1 with pc := n) = strip_labels s1 with pc := n``,
  SRW_TAC [] [strip_labels_def]);

val bc_find_loc_aux = prove(
  ``!code p f.
      (bc_find_loc_aux code len l p = SOME n) /\ ~(l IN FDOM f) ==>
      (FLOOKUP (FUNION f (collect_labels code p len)) l = SOME n)``,
  Induct \\ SIMP_TAC std_ss [bc_find_loc_aux_def]
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `h = Label l`)
  \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FUNION_DEF,IN_UNION]
    \\ Cases_on `h`
    \\ FULL_SIMP_TAC (srw_ss()) [collect_labels_def,FILTER,is_Label_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM])
  \\ FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FUNION_DEF,IN_UNION]
  \\ FULL_SIMP_TAC std_ss [collect_labels_def,FILTER,is_Label_def,ALL_DISTINCT]
  \\ FULL_SIMP_TAC (srw_ss()) [])
  |> Q.SPECL [`code`,`p`,`FEMPTY`]
  |> SIMP_RULE std_ss [FUNION_FEMPTY_1,FDOM_FEMPTY,NOT_IN_EMPTY];

val bc_find_loc_aux_lemma = prove(
  ``length_ok s1.inst_length /\
    (bc_find_loc_aux s1.code s1.inst_length l 0 = SOME n) ==>
    (FLOOKUP (all_labels s1.inst_length s1.code) l = SOME n)``,
  SIMP_TAC std_ss [all_labels_def,length_ok_def,GSYM AND_IMP_INTRO]
  \\ METIS_TAC [bc_find_loc_aux]);

val bool_to_val_11 = prove(
  ``!b1 b2. (bool_to_val b1 = bool_to_val b2) <=> (b1 = b2)``,
  Cases \\ Cases \\ EVAL_TAC);

val bc_next_strip_labels = store_thm("bc_next_strip_labels",
  ``!s1 s2.
      bc_next s1 s2 ==>
      length_ok s1.inst_length ==>
      bc_next (strip_labels s1) (strip_labels s2)``,
  HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC bc_fetch_IMP \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [inst_labels_def,HD]
  \\ ONCE_REWRITE_TAC [bc_next_cases]
  \\ SIMP_TAC (srw_ss()) []
  \\ TRY (Cases_on `l`)
  \\ TRY (Cases_on `b`)
  \\ FULL_SIMP_TAC std_ss [inst_labels_def,HD]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_find_loc_def,strip_labels_pc]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bump_pc_def]
  \\ IMP_RES_TAC bc_find_loc_aux_lemma
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bump_pc_def,bool_to_val_11]
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bump_pc_def,bool_to_val_11]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_fetch_def]
  \\ FULL_SIMP_TAC std_ss [length_ok_def,length_ok_def]
  \\ TRY
   (Q.EXISTS_TAC `n` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def]
    \\ FULL_SIMP_TAC (srw_ss()) [bc_find_loc_def,strip_labels_pc]
    \\ TRY (Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
    \\ TRY (Q.EXISTS_TAC `F` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
    \\ NO_TAC)
  \\ Cases_on `s1` \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bump_pc_def]
  \\ TRY (Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
  \\ TRY (Q.EXISTS_TAC `F` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
  \\ TRY (Q.EXISTS_TAC `ys` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
  \\ METIS_TAC []);

val bc_next_strip_labels_RTC = store_thm("bc_next_strip_labels_RTC",
  ``!s1 s2.
      bc_next^* s1 s2 ==>
      length_ok s1.inst_length ==>
      bc_next^* (strip_labels s1) (strip_labels s2)``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ FULL_SIMP_TAC std_ss [RTC_REFL]
  \\ REPEAT STRIP_TAC
  \\ `length_ok s1'.inst_length` by ALL_TAC
  THEN1 (METIS_TAC [RTC_RULES,bytecodeExtraTheory.RTC_bc_next_preserves])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_next_strip_labels
  \\ IMP_RES_TAC RTC_RULES);


(* prove that more code can be appended *)

val FUNION_FUPDATE = prove(
  ``!a x f1 f2. FUNION (f1 |+ (a,x)) f2 = FUNION f1 f2 |+ (a,x)``,
  SIMP_TAC std_ss [GSYM fmap_EQ,FUNION_DEF,FDOM_FUPDATE,
    FAPPLY_FUPDATE_THM,EXTENSION,IN_INSERT,IN_UNION]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,FUNION_DEF,
       FDOM_FUPDATE,IN_INSERT]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ Cases_on `x' = a` \\ FULL_SIMP_TAC std_ss [])

val collect_labels_APPEND = store_thm("collect_labels_APPEND",
  ``!c1 c2 n l.
      collect_labels (c1 ++ c2) n l =
      FUNION (collect_labels c1 n l)
             (collect_labels c2 (n + code_length l c1) l)``,
  Induct \\ TRY (Cases)
  \\ ASM_SIMP_TAC (srw_ss()) [collect_labels_def,APPEND,code_length_def,SUM,
       MAP,FUNION_FEMPTY_1,ilength_def,is_Label_def,AC ADD_COMM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [FUNION_FUPDATE_1]);

val inst_uses_label_def = Define`
  (inst_uses_label y (Call (Lab x)) ⇔ x = y) ∧
  (inst_uses_label y (Jump (Lab x)) ⇔ x = y) ∧
  (inst_uses_label y (JumpIf (Lab x)) ⇔ x = y) ∧
  (inst_uses_label y (PushPtr (Lab x)) ⇔ x = y) ∧
  (inst_uses_label y _ ⇔ F)`
val _ = export_rewrites["inst_uses_label_def"]

val uses_label_def = Define `
  uses_label code l <=>
    (MEM (Call (Lab l)) code) \/
    (MEM (Jump (Lab l)) code) \/
    (MEM (JumpIf (Lab l)) code) \/
    (MEM (PushPtr (Lab l)) code)`;

val inst_labels_FUNION = prove(
  ``!code.
      (!l. uses_label code l ==> l IN FDOM f1) ==>
      (inst_labels (FUNION f1 f2) code = inst_labels f1 code)``,
  Induct \\ SIMP_TAC std_ss [inst_labels_def]
  \\ Cases \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,uses_label_def,MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ TRY (`n IN FDOM f1` by (POP_ASSUM MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []))
  \\ FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FUNION_DEF,IN_UNION]
  \\ Q.PAT_ASSUM `(!l. bbb) ==> xxx` MATCH_MP_TAC \\ METIS_TAC []);

val code_labels_APPEND = store_thm("code_labels_APPEND",
  ``!c1 c2 l.
      (!l. uses_label c1 l ==> MEM (Label l) c1) ==>
      (code_labels l (c1 ++ c2) =
       inst_labels (all_labels l c1) c1 ++
       inst_labels (FUNION (all_labels l c1)
                           (collect_labels c2 (code_length l c1) l)) c2)``,
  SIMP_TAC std_ss [code_labels_def,inst_labels_APPEND,all_labels_def]
  \\ FULL_SIMP_TAC std_ss [collect_labels_APPEND] \\ SRW_TAC [] []
  \\ MATCH_MP_TAC inst_labels_FUNION
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ Q.SPEC_TAC (`0:num`,`p:num`)
  \\ Induct_on `c1` \\ FULL_SIMP_TAC std_ss [MEM]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [collect_labels_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

(* idempotence *)

val all_labels_inst_labels = prove(
  ``!xs f l. all_labels l (inst_labels f xs) = FEMPTY``,
  SIMP_TAC std_ss [all_labels_def] \\ Q.SPEC_TAC (`0:num`,`k`)
  \\ Induct_on `xs` \\ SIMP_TAC std_ss [inst_labels_def,collect_labels_def]
  \\ Cases \\ ASM_SIMP_TAC (srw_ss()) [inst_labels_def,collect_labels_def]
  \\ Cases_on `l` \\ ASM_SIMP_TAC (srw_ss()) [inst_labels_def,collect_labels_def]);

val inst_labels_FEMPTY = prove(
  ``!x f g. inst_labels FEMPTY (inst_labels g x) = inst_labels g x``,
  Induct \\ SIMP_TAC std_ss [inst_labels_def]
  \\ Cases \\ ASM_SIMP_TAC (srw_ss()) [inst_labels_def]
  \\ Cases_on `l` \\ ASM_SIMP_TAC (srw_ss()) [inst_labels_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `FLOOKUP g n`
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def]);

val strip_labels_idempot = store_thm("strip_labels_idempot",
  ``!s. strip_labels (strip_labels s) = strip_labels s``,
  SIMP_TAC (srw_ss()) [strip_labels_def,code_labels_def]
  \\ SIMP_TAC std_ss [all_labels_inst_labels,inst_labels_FEMPTY]);


(* reverse simulation *)

val FLOOKUP_all_labels = prove(
  ``FLOOKUP (all_labels s.inst_length s.code) l =
    bc_find_loc s (Lab l)``,
  SIMP_TAC std_ss [all_labels_def,bc_find_loc_def]
  \\ Q.SPEC_TAC (`s.inst_length`,`k`)
  \\ Q.SPEC_TAC (`0:num`,`p`)
  \\ Q.SPEC_TAC (`s.code`,`code`) \\ Induct
  \\ SIMP_TAC std_ss [collect_labels_def,bc_find_loc_aux_def]
  THEN1 (SRW_TAC [] [FLOOKUP_DEF])
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ Cases_on `l = n` \\ FULL_SIMP_TAC std_ss []);

val FLOOKUP_all_labels_IMP = prove(
  ``(FLOOKUP (all_labels s.inst_length s.code) l = SOME x) ==>
    (bc_find_loc s (Lab l) = SOME x)``,
  SIMP_TAC std_ss [FLOOKUP_all_labels]);

val bc_find_loc_strip_labels = prove(
  ``(bc_find_loc (strip_labels s) (Lab l) = NONE)``,
  FULL_SIMP_TAC (srw_ss()) [bc_find_loc_def,strip_labels_def,code_labels_def]
  \\ Q.SPEC_TAC (`0:num`,`p`)
  \\ Q.SPEC_TAC (`all_labels s.inst_length s.code`,`f`)
  \\ Q.SPEC_TAC (`s.code`,`xs`)
  \\ Induct \\ FULL_SIMP_TAC std_ss [inst_labels_def,bc_find_loc_aux_def]
  \\ Cases_on `h`
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,bc_find_loc_aux_def]
  \\ Cases_on `l'`
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,bc_find_loc_aux_def]);

val bc_next_strip_IMP = store_thm("bc_next_strip_IMP",
  ``!s t. length_ok s.inst_length /\ bc_next (strip_labels s) t ==>
          ?t'. bc_next s t' /\ (t = strip_labels t')``,
  REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `t with code := s.code`
  \\ REVERSE STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] THEN1
   (`bc_next^* (strip_labels s) t` by METIS_TAC [RTC_RULES]
    \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
    \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def] \\ Cases_on `t`
    \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,
         LIST_CONJ (TypeBase.updates_of ``:bc_state``)])
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once bc_next_cases] \\ STRIP_TAC
  \\ IMP_RES_TAC bc_fetch_strip_labels_BACK
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC)) \\ TRY
   (IMP_RES_TAC bc_fetch_NOT_Label
    \\ Cases_on `y` \\ TRY (Cases_on `l`)
    \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def]
    \\ ASM_SIMP_TAC (srw_ss()) [Once bc_next_cases,bump_pc_def,strip_labels_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,
         LIST_CONJ (TypeBase.updates_of ``:bc_state``)]
    \\ NO_TAC)
  \\ IMP_RES_TAC bc_fetch_NOT_Label
  \\ Cases_on `y` \\ TRY (Cases_on `l`) \\ TRY (Cases_on `l'`)
  \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def]
  \\ Cases_on `FLOOKUP (all_labels s.inst_length s.code) n''`
  \\ FULL_SIMP_TAC (srw_ss()) [bc_find_loc_strip_labels]
  \\ IMP_RES_TAC FLOOKUP_all_labels_IMP
  \\ ASM_SIMP_TAC (srw_ss()) [Once bc_next_cases,bump_pc_def,strip_labels_def]
  \\ FULL_SIMP_TAC std_ss [bc_find_loc_def]
  \\ TRY (Q.EXISTS_TAC `b:bool`)
  \\ Cases_on `s`
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bc_fetch_def,
       LIST_CONJ (TypeBase.updates_of ``:bc_state``)]
  \\ TRY (Cases_on `b`)
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bc_fetch_def,
       LIST_CONJ (TypeBase.updates_of ``:bc_state``),length_ok_def]);

val bc_next_strip = prove(
  ``!r t. bc_next^* r t ==>
          !s. (r = strip_labels s) /\ length_ok s.inst_length ==>
              ?t'. bc_next^* s t'``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ CONJ_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] THEN1 METIS_TAC [RTC_REFL]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `bc_next (strip_labels s) r'` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_next_strip_IMP \\ FULL_SIMP_TAC std_ss []
  \\ FIRST_ASSUM (MP_TAC o Q.SPEC `t'`)
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ METIS_TAC [RTC_RULES])
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];

val _ = save_thm("bc_next_strip",bc_next_strip);

val code_labels_ok_def = Define `
  code_labels_ok code =
    (!l. uses_label code l ==> MEM (Label l) code)`;

val uses_label_nil = store_thm("uses_label_nil",
  ``¬uses_label [] l``,
  simp[uses_label_def])
val _ = export_rewrites["uses_label_nil"]

val uses_label_cons = store_thm("uses_label_cons",
  ``uses_label (i::ls) l ⇔ inst_uses_label l i ∨ uses_label ls l``,
  simp[uses_label_def] >>
  Cases_on`i`>>simp[] >>
  Cases_on`l'`>>simp[] >>
  METIS_TAC[])

val uses_label_thm = store_thm("uses_label_thm",
  ``∀l code. uses_label code l = EXISTS (inst_uses_label l) code``,
  gen_tac >> Induct >> simp[Once uses_label_cons])

val code_labels_ok_nil = store_thm("code_labels_ok_nil",
  ``code_labels_ok []``,
  rw[code_labels_ok_def])
val _ = export_rewrites["code_labels_ok_nil"]

val code_labels_ok_cons = store_thm("code_labels_ok_cons",
  ``∀i ls. code_labels_ok ls ∧ (∀l. inst_uses_label l i ⇒ MEM (Label l) ls) ⇒ code_labels_ok (i::ls)``,
  rw[code_labels_ok_def] >> pop_assum mp_tac >>
  ONCE_REWRITE_TAC[uses_label_cons] >> METIS_TAC[])

val code_labels_ok_cons_label = store_thm("code_labels_ok_cons_label",
  ``∀l ls. code_labels_ok (FILTER ($~ o inst_uses_label l) ls) ⇒ code_labels_ok ((Label l)::ls)``,
  rw[code_labels_ok_def,uses_label_thm,EXISTS_MEM,MEM_FILTER] >>
  Cases_on`l'=l`>>fs[] >>
  first_x_assum MATCH_MP_TAC >>
  HINT_EXISTS_TAC >> simp[] >>
  Cases_on`e`>>fs[]>>
  Cases_on`l''`>>fs[])

val code_labels_ok_append = store_thm("code_labels_ok_append",
  ``∀l1 l2. code_labels_ok l1 ∧ code_labels_ok l2 ⇒ code_labels_ok (l1 ++ l2)``,
  rw[code_labels_ok_def,uses_label_thm] >> METIS_TAC[])

val code_labels_ok_no_labs = store_thm("code_labels_ok_no_labs",
  ``(∀l. ¬uses_label ls l) ⇒ code_labels_ok ls``,
  rw[code_labels_ok_def])

val code_labels_ok_FILTER = store_thm("code_labels_ok_FILTER",
  ``code_labels_ok ls ∧ (∀l. uses_label ls l ⇒ P (Label l)) ⇒ code_labels_ok (FILTER P ls)``,
  rw[code_labels_ok_def,MEM_FILTER,uses_label_thm,EXISTS_MEM] >> METIS_TAC[])

val code_labels_ok_REVERSE = store_thm("code_labels_ok_REVERSE",
  ``code_labels_ok (REVERSE ls) = code_labels_ok ls``,
  rw[code_labels_ok_def,uses_label_thm,EXISTS_REVERSE])
val _ = export_rewrites["code_labels_ok_REVERSE"]

val no_labels_def = Define`
  no_labels = EVERY ($~ o is_Label)`

val inst_labels_no_labels = store_thm("inst_labels_no_labels",
  ``∀ls f. no_labels (inst_labels f ls)``,
  simp[no_labels_def] >>
  Induct >> simp[inst_labels_def] >>
  Cases >> simp[inst_labels_def] >>
  Cases_on`l`>>simp[inst_labels_def])

val code_labels_no_labels = store_thm("code_labels_no_labels",
  ``∀l ls. no_labels (code_labels l ls)``,
  rw[code_labels_def,inst_labels_no_labels])

open bytecodeExtraTheory

val code_executes_ok_strip_labels = store_thm("code_executes_ok_strip_labels",
  ``code_executes_ok bs1 /\ length_ok bs1.inst_length ==>
    code_executes_ok (strip_labels bs1)``,
  SIMP_TAC std_ss [code_executes_ok_def,GSYM ilength_def,LET_DEF]
  \\ REPEAT STRIP_TAC THEN1
   (DISJ1_TAC \\ Q.EXISTS_TAC `strip_labels s2`
    \\ IMP_RES_TAC bc_next_strip_labels_RTC
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC RTC_bc_next_preserves
    \\ METIS_TAC [bc_fetch_strip_labels])
  \\ DISJ2_TAC \\ REPEAT GEN_TAC
  \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`n`]) \\ STRIP_TAC
  \\ Q.EXISTS_TAC `strip_labels s2`
  \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`bs1`,`s1`)
  \\ Q.SPEC_TAC (`s2`,`s2`)
  \\ Induct_on `n`
  THEN1 (ONCE_REWRITE_TAC [NRC_0] \\ SIMP_TAC (srw_ss()) [strip_labels_def])
  \\ ONCE_REWRITE_TAC [NRC]
  \\ SIMP_TAC std_ss [PULL_FORALL,PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `strip_labels z`
  \\ `bc_next^* s1 z` by METIS_TAC [RTC_RULES] \\ IMP_RES_TAC NRC_RTC
  \\ IMP_RES_TAC RTC_bc_next_preserves
  \\ FULL_SIMP_TAC std_ss [strip_labels_output,AND_IMP_INTRO]
  \\ REVERSE STRIP_TAC THEN1
   (Q.PAT_ASSUM `!xx.bbb` MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC RTC_bc_next_output_squeeze
    \\ FULL_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC (bc_next_strip_labels |> REWRITE_RULE [AND_IMP_INTRO])
  \\ FULL_SIMP_TAC std_ss []);

val real_inst_length_ok = store_thm("real_inst_length_ok",
  ``length_ok real_inst_length``,
  EVAL_TAC >> SIMP_TAC std_ss []);

val _ = export_theory();
