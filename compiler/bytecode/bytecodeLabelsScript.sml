open HolKernel Parse boolLib bossLib;

val _ = new_theory "bytecodeLabels";

open listTheory arithmeticTheory finite_mapTheory pred_setTheory
open relationTheory BytecodeTheory;

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
     let addr = case FLOOKUP f l of NONE => 0 | SOME a => a in
       PushPtr (Addr addr) :: inst_labels f xs) /\
  (inst_labels f (Call (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => 0 | SOME a => a in
       Call (Addr addr) :: inst_labels f xs) /\
  (inst_labels f (Jump (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => 0 | SOME a => a in
       Jump (Addr addr) :: inst_labels f xs) /\
  (inst_labels f (JumpIf (Lab l) :: xs) =
     let addr = case FLOOKUP f l of NONE => 0 | SOME a => a in
       JumpIf (Addr addr) :: inst_labels f xs) /\
  (inst_labels f (x::xs) = x :: inst_labels f xs)`
  |> SIMP_RULE std_ss [LET_DEF];

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
  \\ FULL_SIMP_TAC std_ss [ilength_def,BytecodeTheory.is_Label_def,
       LET_DEF,MAP,SUM] \\ FULL_SIMP_TAC std_ss [length_ok_def]);

val code_length_strip_labels = store_thm("code_length_strip_labels",
  ``length_ok s.inst_length ==>
    (code_length s.inst_length (strip_labels s).code =
     code_length s.inst_length s.code)``,
  SIMP_TAC (srw_ss()) [strip_labels_def]
  \\ SIMP_TAC std_ss [code_labels_def,code_length_inst_labels])

val bc_fetch_strip_labels = store_thm("bc_fetch_strip_labels",
  ``length_ok s.inst_length ==>
    (bc_fetch (strip_labels s) = SOME Stop <=> bc_fetch s = SOME Stop)``,
  REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC bc_fetch_IMP \\ FULL_SIMP_TAC std_ss [inst_labels_def,HD])
  \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_IFF,bc_fetch_def]
  \\ FULL_SIMP_TAC std_ss [strip_labels_inst_length,strip_labels_pc]
  \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,code_labels_def]
  \\ Q.ABBREV_TAC `f = all_labels s.inst_length s.code`
  \\ FULL_SIMP_TAC std_ss [GSYM code_length_def,code_length_inst_labels]
  \\ NTAC 3 (POP_ASSUM (K ALL_TAC)) \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`ys2`,`ys2`) \\ Q.SPEC_TAC (`ys1`,`ys1`)
  \\ Q.SPEC_TAC (`s.code`,`code`) \\ Induct
  THEN1 (SRW_TAC [] [inst_labels_def]) \\ STRIP_TAC
  \\ Cases_on `is_Label h` THEN1
   (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [is_Label_def,inst_labels_def]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`Label n::ys1'`,`ys2'`]
    \\ FULL_SIMP_TAC std_ss [APPEND,code_length_def,MAP,SUM,
         ilength_def,is_Label_def])
  \\ `h::code = [h] ++ code` by FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss [inst_labels_APPEND]
  \\ REPEAT STRIP_TAC \\ Cases_on `ys1` THEN1
   (Cases_on `h = Stop` THEN1
     (FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `[]`
      \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11])
    \\ FULL_SIMP_TAC std_ss [APPEND] \\ Cases_on `h`
    \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
    \\ FULL_SIMP_TAC (srw_ss()) [inst_labels_def,is_Label_def])
  \\ `h'::t = [h'] ++ t` by FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss []
  \\ `inst_labels f [h] = [h']` by ALL_TAC THEN1
   (Cases_on `h` \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
    \\ FULL_SIMP_TAC (srw_ss()) [is_Label_def,inst_labels_def])
  \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
  \\ Q.PAT_ASSUM `!xx yy. bbb`
       (STRIP_ASSUME_TAC o REWRITE_RULE [] o Q.SPECL [`t`,`ys2`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1'`,`ys2'`]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [code_length_def,ilength_def,length_ok_def]
  \\ Q.PAT_ASSUM `xx = [h']` (ASSUME_TAC o GSYM)
  \\ Cases_on `h` \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [is_Label_def,inst_labels_def]);

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
  \\ Cases_on `s1` \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def,bump_pc_def]
  \\ TRY (Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
  \\ TRY (Q.EXISTS_TAC `F` \\ FULL_SIMP_TAC std_ss [bool_to_tag_def] \\ NO_TAC)
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

val _ = export_theory();
