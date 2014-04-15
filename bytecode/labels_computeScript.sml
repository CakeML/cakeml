open HolKernel boolLib bossLib lcsymtacs bytecodeLabelsTheory finite_mapTheory patriciaTheory sortingTheory
val _ = new_theory"labels_compute"

val inst_labels_fn_def = Define`
  (inst_labels_fn fn [] = []) ∧
  (inst_labels_fn fn (Label n :: xs) = inst_labels_fn fn xs) ∧
  (inst_labels_fn fn (PushPtr (Lab l) :: xs) =
     let addr = case PEEK fn l of NONE => Lab l | SOME a => Addr a in
       PushPtr addr :: inst_labels_fn fn xs) /\
  (inst_labels_fn fn (Call (Lab l) :: xs) =
     let addr = case PEEK fn l of NONE => Lab l | SOME a => Addr a in
       Call addr :: inst_labels_fn fn xs) /\
  (inst_labels_fn fn (Jump (Lab l) :: xs) =
     let addr = case PEEK fn l of NONE => Lab l | SOME a => Addr a in
       Jump addr :: inst_labels_fn fn xs) /\
  (inst_labels_fn fn (JumpIf (Lab l) :: xs) =
     let addr = case PEEK fn l of NONE => Lab l | SOME a => Addr a in
       JumpIf addr :: inst_labels_fn fn xs) /\
  (inst_labels_fn fn (x::xs) = x :: inst_labels_fn fn xs)`
val inst_labels_fn_def = save_thm("inst_labels_fn_def",
  inst_labels_fn_def |> SIMP_RULE std_ss [LET_DEF]);

val good_label_map_def = Define`
  (good_label_map [] [] p l pt ⇔ T) ∧
  (good_label_map [] us p l pt ⇔ F) ∧
  (good_label_map (Label n::xs) us  p l pt ⇔ pt ' n = SOME p ∧ good_label_map xs us p l pt) ∧
  (good_label_map (PushPtr (Lab n)::xs) (PushPtr (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (PushPtr (Lab n)))) l pt) ∧
  (good_label_map (PushPtr (Lab n)::xs) _ p l pt ⇔ F) ∧
  (good_label_map (Call    (Lab n)::xs) (Call    (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (Call    (Lab n)))) l pt) ∧
  (good_label_map (Call (Lab n)::xs) _ p l pt ⇔ F) ∧
  (good_label_map (Jump    (Lab n)::xs) (Jump    (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (Jump    (Lab n)))) l pt) ∧
  (good_label_map (Jump (Lab n)::xs) _ p l pt ⇔ F) ∧
  (good_label_map (JumpIf  (Lab n)::xs) (JumpIf  (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (JumpIf  (Lab n)))) l pt) ∧
  (good_label_map (JumpIf (Lab n)::xs) _ p l pt ⇔ F) ∧
  (good_label_map (x::xs) (u::us) p l pt ⇔ x = u ∧ good_label_map xs us (p + SUC(l x)) l pt) ∧
  (good_label_map (x::xs) [] p l pt ⇔ F)`

val good_label_map_clauses = store_thm("good_label_map_clauses",``
  (good_label_map [] [] p l pt ⇔ T) ∧
  (good_label_map (Label n        ::xs)                    us  p l pt ⇔ pt ' n = SOME p ∧ good_label_map xs us p l pt) ∧
  (good_label_map (PushPtr (Lab n)::xs) (PushPtr (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (PushPtr (Lab n)))) l pt) ∧
  (good_label_map (Call    (Lab n)::xs) (Call    (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (Call    (Lab n)))) l pt) ∧
  (good_label_map (Jump    (Lab n)::xs) (Jump    (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (Jump    (Lab n)))) l pt) ∧
  (good_label_map (JumpIf  (Lab n)::xs) (JumpIf  (Addr k)::us) p l pt ⇔
   pt ' n = SOME k ∧ good_label_map xs us (p + SUC(l (JumpIf  (Lab n)))) l pt)``,
  simp[good_label_map_def])

val labels_set_def = Define`
  labels_set code = { n | MEM (Label n) code }`

val FDOM_collect_labels_labels_set = store_thm("FDOM_collect_labels_labels_set",
  ``∀l ls p. FDOM (collect_labels ls p l) = labels_set ls``,
  gen_tac >> Induct >> simp[collect_labels_def,labels_set_def] >>
  Cases >> simp[labels_set_def] >> simp[pred_setTheory.EXTENSION])

(*
val good_labels_map_length = store_thm("good_labels_map_length",
  ``∀ls us p l fn. good_label_map ls us p l fn ⇒ LENGTH us = LENGTH (FILTER ($~ o is_Label) ls)``,
  Induct >- (
    simp[good_label_map_def] >>
    Cases >> simp[good_label_map_def] ) >>
  Cases >> simp[good_label_map_def] >>
  Cases >> simp[good_label_map_def] >>
  rpt strip_tac >> fs[] >> res_tac >> fs[] >>
  Cases_on`l`>>Cases_on`h`>>fs[good_label_map_def]>>
  Cases_on`l`>>fs[good_label_map_def]>>
  res_tac >> fs[])
*)

val good_label_map_collect_labels = store_thm("good_label_map_collect_labels",
  ``∀fn l ls us p. good_label_map ls us p l fn ⇒ ∀x. x ∈ FDOM (collect_labels ls p l) ⇒ FLOOKUP (collect_labels ls p l) x = fn ' x``,
  ntac 2 gen_tac >> Induct >>
  simp[collect_labels_def,good_label_map_def] >>
  Cases >> simp[good_label_map_def,collect_labels_def,FLOOKUP_UPDATE] >>
  Cases >> simp[good_label_map_def] >>
  rw[] >> fs[] >>
  rw[] >> fs[] >>
  TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  Cases_on`l'`>>fs[good_label_map_def]>>
  Cases_on`h`>>fs[good_label_map_def]>>
  Cases_on`l'`>>fs[good_label_map_def] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  metis_tac[] )

val inst_labels_fn_intro0 = prove(
  ``∀f1 f2 ls ls0.
      code_labels_ok (ls0++ls) ∧
      (∀x. x ∈ labels_set (ls0++ls) ⇒ FLOOKUP f1 x = PEEK f2 x) ⇒
             inst_labels f1 ls = inst_labels_fn f2 ls``,
  ntac 2 gen_tac >> Induct >>
  simp[inst_labels_def,inst_labels_fn_def] >>
  Cases >> simp[inst_labels_def,inst_labels_fn_def,labels_set_def] >>
  simp[code_labels_ok_def,uses_label_thm] >> rw[] >>
  fs[code_labels_ok_def,uses_label_thm,labels_set_def] >>
  TRY (metis_tac[]) >- (
    last_x_assum(qspec_then`Label n::ls0`mp_tac) >>
    simp[] >> metis_tac[] ) >>
  Cases_on`l`>> (
    fs[inst_labels_def,inst_labels_fn_def]>- (
      last_assum(qspec_then`n`mp_tac) >>
      simp_tac std_ss [] >>
      disch_then assume_tac >>
      first_assum(qspec_then`n`mp_tac) >>
      simp[] >> metis_tac[] )))

val inst_labels_fn_intro = store_thm("inst_labels_fn_intro",
  ``∀fn l ls us. good_label_map ls us 0 l fn ∧ code_labels_ok ls ⇒
          code_labels l ls = inst_labels_fn fn ls``,
   rw[code_labels_def,all_labels_def] >>
   imp_res_tac good_label_map_collect_labels >> fs[] >>
   match_mp_tac inst_labels_fn_intro0 >>
   qexists_tac`[]` >>
   fs[FDOM_collect_labels_labels_set])

val good_label_map_inst_labels = store_thm("good_label_map_inst_labels",
  ``∀fn l ls us p ls0. good_label_map ls us p l fn ∧ code_labels_ok (ls0++ls) ⇒
      inst_labels_fn fn ls = us``,
  ntac 2 gen_tac >> Induct >>
  simp[good_label_map_def,inst_labels_fn_def] >- (
    Cases >> simp[good_label_map_def] ) >>
  Cases >> simp[good_label_map_def,inst_labels_fn_def] >>
  Cases >> simp[good_label_map_def] >>
  rw[] >> fs[] >>
  rw[] >> fs[] >>
  simp[inst_labels_def] >>
  TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    HINT_EXISTS_TAC >> simp[] >>
    TRY(qexists_tac`ls0`>>simp[]>>metis_tac[]) >>
    qexists_tac`Label n :: ls0` >> simp[] >> metis_tac[]) >>
  Cases_on`l'`>>fs[good_label_map_def,inst_labels_fn_def]>>
  TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    metis_tac[] ) >>
  Cases_on`h`>>fs[good_label_map_def,inst_labels_fn_def]>>
  Cases_on`l'`>>fs[good_label_map_def,inst_labels_fn_def] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[code_labels_ok_def,uses_label_thm] >>
  metis_tac[] )

val code_labels_elim = store_thm("code_labels_elim",
  ``∀fn l ls us .
      good_label_map ls us 0 l fn ∧ code_labels_ok ls ⇒
      code_labels l ls = us``,
  rw[] >>
  imp_res_tac good_label_map_inst_labels >>
  pop_assum(qspec_then`[]`mp_tac) >> rw[] >>
  metis_tac[inst_labels_fn_intro])

val _ = Parse.set_fixity"="(Parse.Infix(Parse.NONASSOC, 100)) (* required to load patriciaLib later *)

val _ = export_theory()
