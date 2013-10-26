open HolKernel boolLib bossLib lcsymtacs bytecodeLabelsTheory finite_mapTheory patriciaTheory
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
  (good_label_map [] p l fn ks ⇔ set (TRAVERSE fn) = set ks) ∧
  (good_label_map (Label n::xs) p l fn ks ⇔ fn ' n = SOME p ∧ good_label_map xs p l fn (n::ks)) ∧
  (good_label_map (x::xs) p l fn ks = good_label_map xs (p + l x + 1:num) l fn ks)`

val good_label_map_collect_labels = store_thm("good_label_map_collect_labels",
  ``∀fn l ls p ks. good_label_map ls p l fn ks ∧ IS_PTREE fn ⇒ ∀x. x ∉ set ks ⇒ FLOOKUP (collect_labels ls p l) x = fn ' x``,
  ntac 2 gen_tac >> Induct >>
  simp[collect_labels_def,good_label_map_def] >- (
    rw[] >>
    imp_res_tac MEM_TRAVERSE_PEEK >>
    fs[pred_setTheory.EXTENSION] >>
    last_x_assum(qspec_then`x`mp_tac) >>
    Cases_on`fn ' x` >> simp[] ) >>
  Cases >> simp[good_label_map_def,collect_labels_def,FLOOKUP_UPDATE] >>
  rw[] >> fs[] >>
  rw[] >> fs[] >>
  qmatch_assum_abbrev_tac`good_label_map ls pp l fn kk` >>
  last_x_assum(qspecl_then[`pp`,`kk`]mp_tac) >>
  rw[Abbr`kk`])

val inst_labels_fn_intro0 = prove(
  ``∀f1 f2 l ls p.
      (∀x. FLOOKUP f1 = PEEK f2) ⇒
             inst_labels f1 ls = inst_labels_fn f2 ls``,
  ntac 3 gen_tac >> Induct >>
  simp[inst_labels_def,inst_labels_fn_def] >>
  Cases >> simp[inst_labels_def,inst_labels_fn_def] >>
  Cases_on`l`>>simp[inst_labels_def,inst_labels_fn_def])

val inst_labels_fn_intro = store_thm("inst_labels_fn_intro",
  ``∀fn l ls. good_label_map ls 0 l fn [] ∧ IS_PTREE fn ⇒
          code_labels l ls = inst_labels_fn fn ls``,
   rw[code_labels_def,all_labels_def] >>
   imp_res_tac good_label_map_collect_labels >> fs[] >>
   match_mp_tac inst_labels_fn_intro0 >>
   simp[FUN_EQ_THM])

val _ = export_theory()
