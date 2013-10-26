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
  (good_label_map [] p l fn ⇔ T) ∧
  (good_label_map (Label n::xs) p l fn ⇔ fn ' n = SOME p ∧ good_label_map xs p l fn) ∧
  (good_label_map (x::xs) p l fn = good_label_map xs (p + l x + 1:num) l fn)`

val labels_set_def = Define`
  labels_set code = { n | MEM (Label n) code }`

val FDOM_collect_labels_labels_set = store_thm("FDOM_collect_labels_labels_set",
  ``∀l ls p. FDOM (collect_labels ls p l) = labels_set ls``,
  gen_tac >> Induct >> simp[collect_labels_def,labels_set_def] >>
  Cases >> simp[labels_set_def] >> simp[pred_setTheory.EXTENSION])

val good_label_map_collect_labels = store_thm("good_label_map_collect_labels",
  ``∀fn l ls p. good_label_map ls p l fn ⇒ ∀x. x ∈ FDOM (collect_labels ls p l) ⇒ FLOOKUP (collect_labels ls p l) x = fn ' x``,
  ntac 2 gen_tac >> Induct >>
  simp[collect_labels_def,good_label_map_def] >>
  Cases >> simp[good_label_map_def,collect_labels_def,FLOOKUP_UPDATE] >>
  rw[] >> fs[] >>
  rw[] >> fs[])

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
  ``∀fn l ls. good_label_map ls 0 l fn ∧ code_labels_ok ls ⇒
          code_labels l ls = inst_labels_fn fn ls``,
   rw[code_labels_def,all_labels_def] >>
   imp_res_tac good_label_map_collect_labels >> fs[] >>
   match_mp_tac inst_labels_fn_intro0 >>
   qexists_tac`[]` >>
   fs[FDOM_collect_labels_labels_set])

val _ = Parse.set_fixity"="(Parse.Infix(Parse.NONASSOC, 100)) (* required to load patriciaLib later *)

val _ = export_theory()
