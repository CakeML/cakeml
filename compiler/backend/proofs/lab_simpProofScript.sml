open preamble
  labLangTheory labSemTheory labPropsTheory
  lab_simpTheory lab_to_targetTheory;

val _ = new_theory "lab_simpProof";

(* TODO: move *)
val case_tac = CASE_TAC
val top_case_tac = BasicProvers.TOP_CASE_TAC

val loc_to_pc_SOME_MEM_Section_num = Q.store_thm("loc_to_pc_SOME_MEM_Section_num",
  `∀n1 n2 ls. IS_SOME (loc_to_pc n1 n2 ls) ⇒
    (MEM n1 (MAP Section_num ls) ∧ n2 = 0) ∨
    MEM (n1,n2) (FLAT (MAP (extract_labels o Section_lines) ls))`,
  recInduct loc_to_pc_ind
  \\ rw[] >- ( rw[Once loc_to_pc_def] )
  \\ Cases_on`xs` \\ fs[]
  >- (
    pop_assum mp_tac
    \\ rw[Once loc_to_pc_def] \\ fs[] )
  \\ pop_assum mp_tac
  \\ rw[Once loc_to_pc_def] \\ rfs[] \\ fs[]
  \\ TRY(Cases_on`h` \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]);

val sec_loc_to_pc_NONE_not_MEM = Q.store_thm("sec_loc_to_pc_NONE_not_MEM",
  `∀n ls. sec_loc_to_pc n ls = NONE ⇒ ∀k. ¬MEM(k,n)(extract_labels ls)`,
  recInduct sec_loc_to_pc_ind
  \\ gen_tac \\ Cases \\ fs[]
  \\ rw[sec_loc_to_pc_cons] \\ fs[] \\ rfs[]
  \\ Cases_on`h` \\ fs[]);

val asm_fetch_sec_def = Define`
  (asm_fetch_sec pos [] = INR pos) ∧
  (asm_fetch_sec pos (y::ys) =
   if is_Label y then asm_fetch_sec pos ys
   else if pos = 0n then INL y
   else asm_fetch_sec (pos-1) ys)`;
val _ = export_rewrites["asm_fetch_sec_def"];

val asm_fetch_sec_INR_imp = Q.store_thm("asm_fetch_sec_INR_imp",
  `∀pos ls pos'.
   asm_fetch_sec pos ls = INR pos' ⇒
   pos = pos' + LENGTH (FILTER ($~ o is_Label) ls)`,
  Induct_on`ls` \\ rw[] \\
  first_x_assum(qspec_then`pos-1`mp_tac) \\ rw[]);

val asm_fetch_aux_alt_def = Define`
  (asm_fetch_aux_alt pos [] = NONE) ∧
  (asm_fetch_aux_alt pos (Section k ys::xs) =
   case asm_fetch_sec pos ys of
   | INR pos => asm_fetch_aux_alt pos xs
   | INL y => SOME y)`;
val _ = export_rewrites["asm_fetch_aux_alt_def"];

val asm_fetch_aux_alt_ind = theorem"asm_fetch_aux_alt_ind";

val asm_fetch_aux_alt_intro = Q.store_thm("asm_fetch_aux_alt_intro",
  `∀pos ls. asm_fetch_aux pos ls = asm_fetch_aux_alt pos ls`,
  ho_match_mp_tac asm_fetch_aux_ind \\ rw[asm_fetch_aux_def]);
(* -- *)

val evaluate_ind = labSemTheory.evaluate_ind
val evaluate_def = labSemTheory.evaluate_def

val () = bring_to_front_overload "evaluate" {Name = "evaluate", Thy = "labSem"};

val lab_simp_lines_length = Q.store_thm("lab_simp_lines_length[simp]",
  `!s. LENGTH (lab_simp_lines s) = LENGTH s`,
  ho_match_mp_tac lab_simp_lines_ind \\
  rw [lab_simp_lines_def] \\
  every_case_tac \\ fs []);

val null_lab_simp_lines_cons = Q.store_thm("null_lab_simp_lines_cons[simp]",
  `NULL (lab_simp_lines ls) = NULL ls`,
  rw[NULL_EQ, GSYM LENGTH_NIL]);

val last_lab_simp_lines = Q.store_thm("last_lab_simp_lines[simp]",
  `!xs. LAST (lab_simp_lines xs) = LAST xs`,
  ho_match_mp_tac lab_simp_lines_ind \\
  rw[lab_simp_lines_def] \\
  every_case_tac \\ fs[LAST_CONS_cond] \\ rw[GSYM NULL_EQ]);

val sec_label_ok_lab_simp_lines = Q.store_thm("sec_label_ok_lab_simp_lines[simp]",
  `∀ls. EVERY (sec_label_ok k) (lab_simp_lines ls) ⇔ EVERY (sec_label_ok k) ls`,
  recInduct lab_simp_lines_ind
  \\ rw[lab_simp_lines_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]);

val sec_labels_ok_lab_simp_sec = Q.store_thm("sec_labels_ok_lab_simp_sec[simp]",
  `sec_labels_ok (lab_simp_sec s) ⇔ sec_labels_ok s`,
  Cases_on`s` \\ simp[]);

val EVERY_sec_labels_ok_MAP_lab_simp_sec = Q.store_thm("EVERY_sec_labels_ok_MAP_lab_simp_sec[simp]",
  `∀ls. EVERY sec_labels_ok (MAP lab_simp_sec ls) ⇔ EVERY sec_labels_ok ls`,
  srw_tac[ETA_ss][EVERY_MAP]);

val asm_fetch_sec_lab_simp_lines = Q.store_thm("asm_fetch_sec_lab_simp_lines",
  `∀ls pos.
   EVERY (sec_label_ok k) ls ∧
   ALL_DISTINCT (extract_labels ls) ⇒
   asm_fetch_sec pos (lab_simp_lines ls) = asm_fetch_sec pos ls ∨
   ∃n2 w wl n.
     asm_fetch_sec pos ls = INL (LabAsm (Jump (Lab k n2)) w wl n) ∧ MEM (k,n2) (extract_labels ls) ∧
     asm_fetch_sec pos (lab_simp_lines ls) = INL (Asm (Inst Skip) wl n) ∧
     sec_loc_to_pc n2 (lab_simp_lines ls) = sec_loc_to_pc n2 ls ∧
     (∀p. sec_loc_to_pc n2 ls = SOME p ⇒ p = SUC pos)`,
  recInduct lab_simp_lines_ind
  \\ rw[lab_simp_lines_def]
  \\ TOP_CASE_TAC \\ fs[sec_loc_to_pc_cons]
  >- (
    TOP_CASE_TAC \\ fs[]
    >- (
      Cases_on`b` \\ fs[] \\ rw[] \\ rfs[] \\
      first_x_assum(qspec_then`pos`strip_assume_tac) \\ fs[] \\
      rw[] \\ fs[] \\
      imp_res_tac sec_label_ok_extract_labels \\ fs[] )
    \\ rw[]
    \\ rfs[ALL_DISTINCT_extract_labels_cons]
    \\ first_x_assum(qspec_then`pos-1`strip_assume_tac) \\ fs[]
    \\ fs[extract_labels_not_Label]
    \\ Cases_on`n2=n0` \\ fs[]
    \\ imp_res_tac sec_label_ok_extract_labels \\ fs[]
    \\ rfs[ADD1]
    \\ rw[] \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      Cases_on`b` \\ fs[] \\ rfs[] \\
      first_x_assum(qspec_then`pos-1`strip_assume_tac) \\ fs[] \\
      imp_res_tac sec_label_ok_extract_labels \\ fs[] \\
      Cases_on`n2=n0` \\ fs[] \\
      rpt strip_tac \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[ALL_DISTINCT_extract_labels_cons]
    \\ first_x_assum(qspec_then`pos-2`strip_assume_tac) \\ fs[]
    \\ simp[extract_labels_not_Label]
    \\ imp_res_tac sec_label_ok_extract_labels \\ fs[]
    \\ IF_CASES_TAC \\ fs[] \\ fs[]
    \\ rpt strip_tac \\ fs[] )
  >- (
    reverse TOP_CASE_TAC \\ fs[sec_loc_to_pc_cons]
    \\ TRY (
       IF_CASES_TAC \\ fs[] \\
       IF_CASES_TAC \\ fs[]
       >- (
         Cases_on`b` \\ fs[] \\ rveq \\ rfs[] \\
         first_x_assum(qspec_then`pos-1`strip_assume_tac) \\ fs[] \\
         imp_res_tac sec_label_ok_extract_labels \\ fs[] \\
         Cases_on`n2=n0` \\ fs[] \\
         rpt strip_tac \\ fs[] ) \\
       IF_CASES_TAC \\ fs[extract_labels_not_Label] \\ rfs[] \\
       first_x_assum(qspec_then`pos-2`strip_assume_tac) \\ fs[] \\
       imp_res_tac sec_label_ok_extract_labels \\ fs[] \\
       Cases_on`b` \\ fs[] \\ rpt strip_tac \\ fs[] \\ NO_TAC)
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    \\ TRY (
       IF_CASES_TAC \\ fs[sec_loc_to_pc_cons] \\
       IF_CASES_TAC \\ fs[] \\ rfs[] \\
       first_x_assum(qspec_then`pos-2`strip_assume_tac) \\ fs[] \\
       imp_res_tac sec_label_ok_extract_labels \\ fs[] \\
       rpt strip_tac \\ fs[] \\ NO_TAC)
    \\ reverse IF_CASES_TAC \\ fs[] \\ rveq \\ fs[]
    \\ IF_CASES_TAC \\ fs[sec_loc_to_pc_cons] \\ rfs[] \\
    first_x_assum(qspec_then`pos-1`strip_assume_tac) \\ fs[] \\
    imp_res_tac sec_label_ok_extract_labels \\ fs[] \\
    IF_CASES_TAC \\ fs[] \\
    rpt strip_tac \\ fs[]))

val LENGTH_FILTER_not_Label_lab_simp_lines = Q.store_thm("LENGTH_FILTER_not_Label_lab_simp_lines[simp]",
  `∀ls. LENGTH (FILTER ($~ o is_Label) (lab_simp_lines ls)) = LENGTH (FILTER ($~ o is_Label) ls)`,
  recInduct lab_simp_lines_ind
  \\ rw[lab_simp_lines_def]
  \\ every_case_tac \\ fs[]);

val sec_loc_to_pc_lab_simp_lines = Q.store_thm("sec_loc_to_pc_lab_simp_lines[simp]",
  `∀ls n2. sec_loc_to_pc n2 (lab_simp_lines ls) = sec_loc_to_pc n2 ls`,
  recInduct lab_simp_lines_ind
  \\ rw[lab_simp_lines_def]
  \\ every_case_tac \\ fs[sec_loc_to_pc_cons]);

val loc_to_pc_MAP_lab_simp_sec_non_zero = Q.store_thm("loc_to_pc_MAP_lab_simp_sec_non_zero[simp]",
  `∀n1 n2 ls. n2 ≠ 0 ∧ EVERY sec_labels_ok ls ⇒ loc_to_pc n1 n2 (MAP lab_simp_sec ls) = loc_to_pc n1 n2 ls`,
  Induct_on`ls` \\ rw[] \\
  first_x_assum drule \\ rw[] \\
  first_x_assum(qspec_then`n1`strip_assume_tac) \\
  Cases_on`h` \\ simp[] \\ rw[] \\
  qmatch_goalsub_abbrev_tac`loc_to_pc _ _ code1 = _` \\
  `EVERY sec_labels_ok code1` by fs[Abbr`code1`] \\
  qmatch_goalsub_abbrev_tac`_ = loc_to_pc _ _ code2` \\
  `EVERY sec_labels_ok code2` by fs[Abbr`code2`] \\
  simp[Abbr`code1`,Once loc_to_pc_thm] \\
  simp[Abbr`code2`,Once loc_to_pc_thm,SimpRHS]);

val loc_to_pc_MAP_lab_simp_sec = Q.store_thm("loc_to_pc_MAP_lab_simp_sec[simp]",
  `∀n1 n2 ls.
    EVERY ($~ o NULL o Section_lines) ls ∧ EVERY sec_labels_ok ls ⇒
    loc_to_pc n1 n2 (MAP lab_simp_sec ls) = loc_to_pc n1 n2 ls`,
  Induct_on`ls` \\ rw[lab_simp_def] \\
  first_x_assum drule \\ rw[] \\
  first_x_assum(qspec_then`n1`strip_assume_tac) \\
  Cases_on`h` \\ simp[lab_simp_def] \\ rw[] \\ fs[] \\
  qmatch_goalsub_abbrev_tac`loc_to_pc _ _ code1 = _` \\
  `EVERY sec_labels_ok code1` by fs[Abbr`code1`] \\
  qmatch_goalsub_abbrev_tac`_ = loc_to_pc _ _ code2` \\
  `EVERY sec_labels_ok code2` by fs[Abbr`code2`] \\
  simp[Abbr`code1`,Once loc_to_pc_thm] \\
  simp[Abbr`code2`,Once loc_to_pc_thm,SimpRHS]);

val next_label_lab_simp_lines = Q.store_thm("next_label_lab_simp_lines[simp]",
  `∀ls. next_label ((Section k (lab_simp_lines ls))::ss) = next_label ((Section k ls)::ss)`,
  recInduct lab_simp_lines_ind
  \\ rw[next_label_def,lab_simp_lines_def]
  \\ top_case_tac \\ fs[next_label_def]
  >- ( Cases_on`b` \\ fs[next_label_def] )
  >- (
    reverse top_case_tac \\ fs[next_label_def]
    \\ TRY ( Cases_on`b` \\ fs[next_label_def] \\ NO_TAC )
    \\ top_case_tac \\ fs[next_label_def]
    \\ top_case_tac \\ fs[next_label_def]
    \\ top_case_tac \\ fs[next_label_def] ));

val next_label_MAP_lab_simp_sec = Q.store_thm("next_label_MAP_lab_simp_sec[simp]",
  `∀ls. next_label (MAP lab_simp_sec ls) = next_label ls`,
  recInduct next_label_ind
  \\ rw[next_label_def,lab_simp_lines_def]);

val get_lab_after_lab_simp_lines = Q.store_thm("get_lab_after_lab_simp_lines[simp]",
  `∀ls pc. get_lab_after pc ((Section k (lab_simp_lines ls))::ss) =
           get_lab_after pc ((Section k ls)::ss)`,
  recInduct lab_simp_lines_ind
  \\ rw[lab_simp_lines_def]
  \\ top_case_tac \\ fs[]
  >- ( fs[get_lab_after_def] )
  >- (
    fs[get_lab_after_def] \\
    Cases_on`b` \\ fs[next_label_def] )
  \\ reverse top_case_tac \\ fs[get_lab_after_def]
  \\ TRY ( Cases_on`b` \\ fs[next_label_def] \\ NO_TAC)
  \\ top_case_tac \\ fs[]
  \\ top_case_tac \\ fs[get_lab_after_def,next_label_def]
  \\ top_case_tac \\ fs[get_lab_after_def,next_label_def]);

val get_lab_after_MAP_lab_simp_sec = Q.store_thm("get_lab_after_MAP_lab_simp_sec[simp]",
  `∀pc code. get_lab_after pc (MAP lab_simp_sec code) = get_lab_after pc code`,
  recInduct get_lab_after_ind
  \\ conj_tac >- (EVAL_TAC \\ rw[])
  \\ conj_tac >- ( simp[get_lab_after_def] )
  \\ rw[get_lab_after_def,next_label_def]
  \\ rpt(pop_assum kall_tac)
  \\ Induct_on`ys`
  \\ rw[next_label_def]
  \\ Cases_on`h` \\ fs[next_label_def]);

val asm_fetch_aux_MAP_lab_simp_sec = Q.store_thm("asm_fetch_aux_MAP_lab_simp_sec",
  `∀pos ls.
   EVERY sec_labels_ok ls ∧ ALL_DISTINCT (MAP Section_num ls) ∧
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) ls ∧
   EVERY ($~ o NULL o Section_lines) ls
   ⇒
   asm_fetch_aux pos (MAP lab_simp_sec ls) = asm_fetch_aux pos ls ∨
   ∃n1 n2 w wl n.
     asm_fetch_aux pos ls = SOME (LabAsm (Jump (Lab n1 n2)) w wl n) ∧
     asm_fetch_aux pos (MAP lab_simp_sec ls) = SOME (Asm (Inst Skip) wl n) ∧
     loc_to_pc n1 n2 (MAP lab_simp_sec ls) = loc_to_pc n1 n2 ls ∧
     loc_to_pc n1 n2 ls = SOME (SUC pos)`,
  Induct_on`ls` \\ rw[]
  \\ Cases_on`h` \\ fs[]
  \\ fs[asm_fetch_aux_alt_intro]
  \\ qspecl_then[`n`,`l`,`pos`]mp_tac (Q.GEN`k`asm_fetch_sec_lab_simp_lines)
  \\ fs[]
  \\ strip_tac \\ fs[]
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ first_x_assum(qspec_then`y`strip_assume_tac) \\ fs[] \\
    qmatch_goalsub_abbrev_tac`loc_to_pc n1 n2 code1 = _` \\
    `EVERY sec_labels_ok code1` by simp[Abbr`code1`] \\
    simp[Once loc_to_pc_thm,Abbr`code1`] \\
    reverse IF_CASES_TAC \\ fs[]
    >- (
      rpt strip_tac \\ fs[] \\
      imp_res_tac asm_fetch_sec_INR_imp \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      rpt strip_tac \\ fs[] \\
      imp_res_tac asm_fetch_sec_INR_imp \\ fs[] )
    \\ qspecl_then[`n`,`n2`,`ls`]mp_tac loc_to_pc_SOME_MEM_Section_num
    \\ simp[]
    \\ simp[MEM_FLAT,MEM_MAP,PULL_EXISTS]
    \\ fs[MEM_MAP]
    \\ Cases
    \\ fs[EVERY_MEM]
    \\ strip_tac \\ res_tac
    \\ fs[] \\ rw[]
    \\ imp_res_tac sec_label_ok_extract_labels \\ rw[]
    \\ metis_tac[labLangTheory.Section_num_def] )
  \\ qmatch_goalsub_abbrev_tac`loc_to_pc n1 n2 code1 = _` \\
  `EVERY sec_labels_ok code1` by simp[Abbr`code1`] \\
  simp[Once loc_to_pc_thm,Abbr`code1`] \\
  imp_res_tac sec_label_ok_extract_labels \\ simp[] \\
  TOP_CASE_TAC \\ fs[] \\ rw[] \\
  imp_res_tac sec_loc_to_pc_NONE_not_MEM);

val MAP_lab_simp_sec_correct = Q.store_thm("MAP_lab_simp_sec_correct",
  `!(s1:('a,'ffi) labSem$state) res s2.
     (evaluate s1 = (res,s2)) /\ ¬s1.failed ∧
      EVERY sec_labels_ok s1.code ∧
      ALL_DISTINCT (MAP Section_num s1.code) ∧
      EVERY (ALL_DISTINCT o extract_labels o Section_lines) s1.code ∧
      EVERY ($~ o NULL o Section_lines) s1.code
      ==>
       (evaluate (s1 with code := MAP lab_simp_sec s1.code) = (res,s2 with code := MAP lab_simp_sec s2.code))`,
  ho_match_mp_tac evaluate_ind \\ rw [] \\
  qhdtm_x_assum `evaluate` mp_tac \\
  simp [Once evaluate_def] \\
  IF_CASES_TAC >- (rw[] \\ simp [Once evaluate_def]) \\
  strip_tac \\
  once_rewrite_tac [evaluate_def] \\
  fs[asm_fetch_def] \\
  qspecl_then[`s1.pc`,`s1.code`]mp_tac asm_fetch_aux_MAP_lab_simp_sec \\
  impl_tac >- fs[] \\ rw[] \\ fs[]
  >- (
    top_case_tac \\ fs [] \\
    top_case_tac \\ fs[]
    >- (
      top_case_tac \\ fs[]
      >- (
        top_case_tac \\ fs[]
        \\ rfs[asm_inst_consts]
        \\ fs[dec_clock_def,inc_pc_def,asm_inst_consts] )
      \\ top_case_tac \\ fs[]
      \\ top_case_tac \\ fs[]
      \\ fs[upd_pc_def,dec_clock_def])
    >- (
      fs[get_pc_value_def,dec_clock_def,upd_pc_def,upd_reg_def,inc_pc_def,get_ret_Loc_def] \\
      top_case_tac \\ fs[]
      >- (
        case_tac \\ fs[] \\
        case_tac \\ fs[])
      >- (
        top_case_tac \\ fs[] \\
        case_tac \\ fs[] \\
        case_tac \\ fs[] \\ rw[] \\ fs[])
      >- (
        case_tac \\ fs[] \\
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[])
      >- (
        case_tac \\ fs[] \\
        top_case_tac \\ fs[])
      >- (
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[] \\
        pairarg_tac \\ fs[] )
      >- (
        top_case_tac \\ fs[] \\
        top_case_tac \\ fs[] )))
  \\ fs[dec_clock_def,get_pc_value_def,inc_pc_def,upd_pc_def,ADD1]);

val remove_tail_jumps_correct = Q.store_thm("remove_tail_jumps_correct",
  `∀(s1:('a,'ffi)labSem$state) res s2.
   evaluate s1 = (res,s2) ∧ ¬s1.failed
   ⇒
   evaluate (s1 with code := remove_tail_jumps s1.code) =
     (res,s2 with code := remove_tail_jumps s2.code)`,
  ho_match_mp_tac evaluate_ind \\ rw[] \\
  qhdtm_x_assum`evaluate`mp_tac \\
  once_rewrite_tac[evaluate_def] \\ simp[] \\
  IF_CASES_TAC \\ rw[] \\
  fs[asm_fetch_def] \\
  cheat);

val lab_simp_correct = Q.store_thm("lab_simp_correct",
  `∀(s1:('a,'ffi)labSem$state) res s2.
    evaluate s1 = (res,s2) ∧ ¬s1.failed ∧
    EVERY sec_labels_ok s1.code ∧
    ALL_DISTINCT (MAP Section_num s1.code) ∧
    EVERY (ALL_DISTINCT o extract_labels o Section_lines) s1.code ∧
    EVERY ($~ o NULL o Section_lines) s1.code
    ==>
     (evaluate (s1 with code := lab_simp s1.code) = (res,s2 with code := lab_simp s2.code))`,
  rw[lab_simp_def]
  \\ drule MAP_lab_simp_sec_correct
  \\ impl_tac >- simp[] \\ strip_tac
  \\ drule remove_tail_jumps_correct
  \\ impl_tac >- simp[] \\ rw[]);

val _ = export_theory ();
