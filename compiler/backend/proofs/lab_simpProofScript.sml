open preamble
  labLangTheory labSemTheory labPropsTheory
  lab_simpTheory lab_to_targetTheory;

val _ = new_theory "lab_simpProof";

(* TODO: move *)
val is_Label_exists = Q.store_thm("is_Label_exists",
  `is_Label l ⇔ ∃n1 n2 k. l = Label n1 n2 k`,
  Cases_on`l` \\ rw[]);
(* -- *)

val state_rel_def = Define `
state_rel (s1:('a,'ffi) labSem$state) t1 ⇔
          (t1 = s1 with <| code := lab_simp s1.code |>) ∧
          ¬s1.failed`

val evaluate_ind = labSemTheory.evaluate_ind
val evaluate_def = labSemTheory.evaluate_def

infixr 1 $
fun (a $ b) = a b
val case_tac = CASE_TAC
val top_case_tac = BasicProvers.TOP_CASE_TAC

val () = bring_to_front_overload "evaluate" {Name = "evaluate", Thy = "labSem"};

val lab_simp_sec_length = Q.store_thm("lab_simp_sec_length[simp]",
  `!s. LENGTH (lab_simp_sec s) = LENGTH s`,
  ho_match_mp_tac lab_simp_sec_ind \\
  rw [lab_simp_sec_def] \\
  every_case_tac \\ fs []);

val null_lab_simp_sec_cons = Q.store_thm("null_lab_simp_sec_cons[simp]",
  `NULL (lab_simp_sec ls) = NULL ls`,
  rw[NULL_EQ, GSYM LENGTH_NIL]);

val last_lab_simp_sec = Q.store_thm("last_lab_simp_sec[simp]",
  `!xs. LAST (lab_simp_sec xs) = LAST xs`,
  ho_match_mp_tac lab_simp_sec_ind \\
  rw[lab_simp_sec_def] \\
  every_case_tac \\ fs[LAST_CONS_cond] \\ rw[GSYM NULL_EQ]);

val asm_fetch_sec_def = Define`
  (asm_fetch_sec pos [] = INR pos) ∧
  (asm_fetch_sec pos (y::ys) =
   if is_Label y then asm_fetch_sec pos ys
   else if pos = 0n then INL y
   else asm_fetch_sec (pos-1) ys)`;
val _ = export_rewrites["asm_fetch_sec_def"];

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

val loc_to_pc_lines_def = Define`
  (loc_to_pc_lines _ [] = NONE) /\
  (loc_to_pc_lines n2 (Label n1 n2' k::xs) =
   if n2 = n2' then SOME 0 else loc_to_pc_lines n2 xs) /\
  (loc_to_pc_lines n2 (x::xs) = OPTION_MAP SUC (loc_to_pc_lines n2 xs))`;

val loc_to_pc_sec_def = Define `
  (loc_to_pc_sec n1 n2 [] = NONE) /\
  (loc_to_pc_sec n1 n2 ((Section k xs)::ys) =
   if n1 = k then if n2 = 0 then SOME 0 else loc_to_pc_lines n2 xs else
   OPTION_MAP (\x. x + LENGTH (FILTER ($~ o is_Label) xs)) (loc_to_pc_sec n1 n2 ys))`;

val I_intro = Q.prove(`(λx. x) = I`, rw[FUN_EQ_THM])

val loc_to_pc_sec_intro = Q.store_thm("loc_to_pc_sec_intro",
  `!n1 n2 sections.
    EVERY sec_labels_ok sections ∧ ALL_DISTINCT (MAP Section_num sections) ==>
    loc_to_pc n1 n2 sections = loc_to_pc_sec n1 n2 sections`,
  recInduct loc_to_pc_ind \\
  rw[] >- (rw[loc_to_pc_sec_def, loc_to_pc_def]) \\
  fs [loc_to_pc_sec_def] \\
  simp[Once loc_to_pc_def] \\
  reverse(Cases_on`k=n1`)\\fs[]
  >- (
    TOP_CASE_TAC \\ fs[I_intro,quotient_optionTheory.OPTION_MAP_I] \\
    TOP_CASE_TAC \\ fs[] \\ fs[]
    >- (
      TOP_CASE_TAC \\ rfs[] \\
      Cases_on`loc_to_pc_sec n1 n2 ys` \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[] \\
    Cases_on`loc_to_pc_sec n1 0 ys` \\ fs[] )
  \\ TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[]
  >- (
    rw[loc_to_pc_lines_def] \\
    qhdtm_x_assum`ALL_DISTINCT`kall_tac \\
    qhdtm_x_assum`loc_to_pc`kall_tac \\
    Induct_on`ys` \\ simp[loc_to_pc_sec_def] \\
    rw[] \\ fs[] \\
    Cases_on`h` \\ rw[loc_to_pc_sec_def] \\ fs[] )
  \\ TOP_CASE_TAC \\ fs[]
  >- ( fs[loc_to_pc_lines_def] )
  \\ TOP_CASE_TAC \\ fs[]
  \\ Cases_on `h` \\ fs[loc_to_pc_lines_def] \\ rw[]
  \\ Cases_on`loc_to_pc_lines n2 t` \\ fs[]);

val sec_label_ok_lab_simp_sec = Q.store_thm("sec_label_ok_lab_simp_sec[simp]",
  `∀ls. EVERY (sec_label_ok k) (lab_simp_sec ls) ⇔ EVERY (sec_label_ok k) ls`,
  recInduct lab_simp_sec_ind
  \\ rw[lab_simp_sec_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]);

val sec_labels_ok_lab_simp = Q.store_thm("sec_labels_ok_lab_simp[simp]",
  `∀ls. EVERY sec_labels_ok (lab_simp ls) ⇔ EVERY sec_labels_ok ls`,
  recInduct lab_simp_ind \\ rw[lab_simp_def,NULL_EQ]);

val asm_fetch_sec_lab_simp_sec = Q.store_thm("asm_fetch_sec_lab_simp_sec",
  `∀ls pos.
   EVERY (sec_label_ok k) ls ∧
   ALL_DISTINCT (extract_labels ls) ⇒
   asm_fetch_sec pos (lab_simp_sec ls) = asm_fetch_sec pos ls ∨
   ∃n2 w wl n.
     asm_fetch_sec pos ls = INL (LabAsm (Jump (Lab k n2)) w wl n) ∧ MEM (k,n2) (extract_labels ls) ∧
     asm_fetch_sec pos (lab_simp_sec ls) = INL (Asm (Inst Skip) wl n) ∧
     sec_loc_to_pc n2 (lab_simp_sec ls) = sec_loc_to_pc n2 ls ∧
     (∀p. sec_loc_to_pc n2 ls = SOME p ⇒ p = SUC pos)`,
  recInduct lab_simp_sec_ind
  \\ rw[lab_simp_sec_def]
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

val LENGTH_FILTER_not_Label_lab_simp_sec = Q.store_thm("LENGTH_FILTER_not_Label_lab_simp_sec[simp]",
  `∀ls. LENGTH (FILTER ($~ o is_Label) (lab_simp_sec ls)) = LENGTH (FILTER ($~ o is_Label) ls)`,
  recInduct lab_simp_sec_ind
  \\ rw[lab_simp_sec_def]
  \\ every_case_tac \\ fs[]);

val asm_fetch_sec_INR_imp = Q.store_thm("asm_fetch_sec_INR_imp",
  `∀pos ls pos'.
   asm_fetch_sec pos ls = INR pos' ⇒
   pos = pos' + LENGTH (FILTER ($~ o is_Label) ls)`,
  Induct_on`ls` \\ rw[] \\
  first_x_assum(qspec_then`pos-1`mp_tac) \\ rw[]);

val sec_loc_to_pc_lab_simp_sec = Q.store_thm("sec_loc_to_pc_lab_simp_sec[simp]",
  `∀ls n2. sec_loc_to_pc n2 (lab_simp_sec ls) = sec_loc_to_pc n2 ls`,
  recInduct lab_simp_sec_ind
  \\ rw[lab_simp_sec_def]
  \\ every_case_tac \\ fs[sec_loc_to_pc_cons]);

val loc_to_pc_lab_simp = Q.store_thm("loc_to_pc_lab_simp[simp]",
  `∀n1 n2 ls. n2 ≠ 0 ∧ EVERY sec_labels_ok ls ⇒ loc_to_pc n1 n2 (lab_simp ls) = loc_to_pc n1 n2 ls`,
  Induct_on`ls` \\ rw[lab_simp_def] \\
  first_x_assum drule \\ rw[] \\
  first_x_assum(qspec_then`n1`strip_assume_tac) \\
  Cases_on`h` \\ simp[lab_simp_def] \\ rw[]
  >- (
    fs[NULL_EQ] \\
    simp[Once loc_to_pc_thm,SimpRHS] \\
    simp[Once sec_loc_to_pc_def] \\
    rw[] ) \\
  qmatch_goalsub_abbrev_tac`loc_to_pc _ _ code1 = _` \\
  `EVERY sec_labels_ok code1` by fs[Abbr`code1`] \\
  qmatch_goalsub_abbrev_tac`_ = loc_to_pc _ _ code2` \\
  `EVERY sec_labels_ok code2` by fs[Abbr`code2`] \\
  simp[Abbr`code1`,Once loc_to_pc_thm] \\
  simp[Abbr`code2`,Once loc_to_pc_thm,SimpRHS]);

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

val asm_fetch_aux_lab_simp = Q.store_thm("asm_fetch_lab_simp",
  `∀pos ls.
   EVERY sec_labels_ok ls ∧ ALL_DISTINCT (MAP Section_num ls) ∧
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) ls ∧
   EVERY ($~ o NULL o Section_lines) ls
   ⇒
   asm_fetch_aux pos (lab_simp ls) = asm_fetch_aux pos ls ∨
   ∃n1 n2 w wl n.
     asm_fetch_aux pos ls = SOME (LabAsm (Jump (Lab n1 n2)) w wl n) ∧
     asm_fetch_aux pos (lab_simp ls) = SOME (Asm (Inst Skip) wl n) ∧
     loc_to_pc n1 n2 (lab_simp ls) = loc_to_pc n1 n2 ls ∧
     loc_to_pc n1 n2 ls = SOME (SUC pos)`,
  Induct_on`ls` \\ rw[lab_simp_def]
  \\ Cases_on`h` \\ fs[]
  \\ fs[lab_simp_def]
  \\ fs[asm_fetch_aux_alt_intro]
  \\ qspecl_then[`n`,`l`,`pos`]mp_tac (Q.GEN`k`asm_fetch_sec_lab_simp_sec)
  \\ fs[]
  \\ strip_tac \\ fs[]
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ first_x_assum(qspec_then`y`strip_assume_tac) \\ fs[] \\
    qmatch_goalsub_abbrev_tac`loc_to_pc n1 n2 code1 = _` \\
    `EVERY sec_labels_ok code1` by simp[Abbr`code1`] \\
    simp[Once loc_to_pc_thm,Abbr`code1`] \\
    qmatch_goalsub_abbrev_tac`_ = loc_to_pc n1 n2 code2` \\
    `EVERY sec_labels_ok code2` by simp[Abbr`code2`] \\
    simp[Once loc_to_pc_thm,Abbr`code2`,SimpRHS] \\
    simp[Once loc_to_pc_thm] \\
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
  qmatch_goalsub_abbrev_tac`_ = loc_to_pc n1 n2 code2` \\
  `EVERY sec_labels_ok code2` by simp[Abbr`code2`] \\
  simp[Once loc_to_pc_thm,Abbr`code2`,SimpRHS] \\
  imp_res_tac sec_label_ok_extract_labels \\ simp[] \\
  simp[Once loc_to_pc_thm] \\
  TOP_CASE_TAC \\ fs[] \\ rw[] \\
  imp_res_tac sec_loc_to_pc_NONE_not_MEM);

val lab_simp_correct = Q.store_thm("lab_simp_correct",
`!(s1:('a,'ffi) labSem$state) t1 res s2.
   (evaluate s1 = (res,s2)) /\ state_rel s1 t1 ∧
    EVERY sec_labels_ok s1.code ∧
    ALL_DISTINCT (MAP Section_num s1.code) ∧
    EVERY (ALL_DISTINCT o extract_labels o Section_lines) s1.code ∧
    EVERY ($~ o NULL o Section_lines) s1.code
    ==>
     ?t2. (evaluate t1 = (res,t2)) /\ state_rel s2 t2`,
  ho_match_mp_tac evaluate_ind \\
  rw [] \\
  qhdtm_x_assum `evaluate` mp_tac \\
  simp [Once evaluate_def] \\
  IF_CASES_TAC >-
    (rw[] \\
     first_assum (part_match_exists_tac (el 2 o strip_conj) o concl) \\
     simp [] \\ simp [Once evaluate_def] \\ fs [state_rel_def] \\ rw [] \\ fs []) \\
  strip_tac \\
  qhdtm_x_assum`state_rel`mp_tac \\
  rw[Once state_rel_def] \\
  once_rewrite_tac [evaluate_def] \\
  fs[asm_fetch_def] \\
  qspecl_then[`s1.pc`,`s1.code`]mp_tac asm_fetch_aux_lab_simp \\
  impl_tac >- fs[] \\ rw[] \\ fs[]
  >- (
    top_case_tac \\ fs []
    >- ( rw[state_rel_def] ) \\
    top_case_tac \\ fs[]
    >- ( rw[state_rel_def] ) \\
    >- (
      top_case_tac \\ fs[]
      \\ TRY( rw[state_rel_def] \\ NO_TAC)
      >- (
        top_case_tac \\ fs[]
        >- rw[state_rel_def]
        \\ rfs[asm_inst_consts]
        \\ first_x_assum match_mp_tac
        \\ rw[state_rel_def]
        \\ fs[state_component_equality,dec_clock_def,inc_pc_def,asm_inst_consts] )
      \\ top_case_tac \\ fs[]
      >- rw[state_rel_def]
      \\ pop_assum mp_tac \\ top_case_tac \\ fs[]
      >- rw[]

  >- (rw[] \\ CONV_TAC (QUANT_CONV $ LAND_CONV $ LAND_CONV $ REWR_CONV $ evaluate_def))

(*
val asm_fetch_sec_lab_simp_sec_unchanged = Q.store_thm("asm_fetch_sec_lab_simp_sec_unchanged",
  `∀ls p.
   EVERY (sec_label_ok k) ls ∧
   (∀n2 w wl n.
      asm_fetch_sec p ls = INL (LabAsm (Jump (Lab k n2)) w wl n) ⇒
      sec_loc_to_pc n2 ls ≠ SOME (p+1)) ⇒
   asm_fetch_sec p (lab_simp_sec ls) = asm_fetch_sec p ls`,
  recInduct lab_simp_sec_ind
  \\ rw[lab_simp_sec_def]
  \\ TOP_CASE_TAC \\ fs[] \\ rfs[] \\ rveq \\ rpt(qpat_x_assum`T`kall_tac)
  >- (
    fs[sec_loc_to_pc_cons] \\
    rw[] \\ rfs[]
    asm_fetch_sec_def
    reverse IF_CASES_TAC \\ fs[]
    >- (
      IF_CASES_TAC \\ fs[] \\
      first_x_assum match_mp_tac \\ rw[] \\ fs[] \\
      reverse(Cases_on`n0 = n2` \\ fs[])
      >- ( Cases_on`b` \\ fs[ADD1] )

    rw[] \\ rfs[] \\
    first_x_assum match_mp_tac \\
    fs[sec_loc_to_pc_cons]

val asm_fetch_sec_lab_simp_sec = Q.store_thm("asm_fetch_sec_lab_simp_sec",
  `∀ls p.
    EVERY (label_ok k) ls ⇒
    asm_fetch_sec p (lab_simp_sec ls) =
    case asm_fetch_sec p ls of
    | INL (LabAsm (Jump (Lab n1 n2)) w wl n) =>
      if n1 = k ∧ n2 ≠ 0 ∧ loc_to_pc_lines n2 ls = SOME (p+1) then
        INL (Asm (Inst Skip) wl n)
      else INL (LabAsm (Jump (Lab n1 n2)) w wl n)
    | a => a`,
  recInduct lab_simp_sec_ind
  \\ reverse(rw[lab_simp_sec_def])
  >- (
    CASE_TAC \\ fs[loc_to_pc_lines_def] \\
    CASE_TAC \\ fs[] \\
    CASE_TAC \\ fs[] )
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    TOP_CASE_TAC \\ fs[]
    >- (
      TOP_CASE_TAC \\ fs[] \\
      TOP_CASE_TAC \\ fs[] \\
      TOP_CASE_TAC \\ fs[] \\
      TOP_CASE_TAC \\ fs[] \\
      fs[loc_to_pc_lines_def] \\
      CASE_TAC \\ fs[] \\
      CASE_TAC \\ fs[] \\ rw[]
      match_mp_tac EQ_SYM \\
      simp[Once loc_to_pc_def] \\
      CASE_TAC \\ fs[]
      loc_to_pc_def
  \\ TRY (
    Cases_on`xs` \\ fs[lab_simp_sec_def] \\ rw[]
    \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs[]
  \\ TRY (
    Cases_on`xs` \\ fs[lab_simp_sec_def]
    \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TRY (
    Cases_on`xs` \\ fs[lab_simp_sec_def]
    \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs[]
  \\ TRY (
    Cases_on`xs` \\ fs[lab_simp_sec_def]
    \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs[]
  lab_simp_sec_def

  \\ Cases_on`a` \\ fs[]
  \\ Cases_on`a` \\ fs[]
  \\ simp[is_Label_exists]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    IF_CASES_TAC \\ fs[]

val pc_to_section_def = Define `
  (pc_to_section pc [] = NONE) /\
  (pc_to_section 0 ((Section k xs)::ys) = SOME k) /\
  (pc_to_section pc ((Section k [])::ys) = pc_to_section pc ys) /\
  (pc_to_section (SUC pc) ((Section k (x::xs))::ys) = pc_to_section pc ((Section k xs)::ys))`;

                                         )
val loc_to_pc_section_is_pc_to_section = Q.store_thm("loc_to_pc_section_is_pc_to_section",
`!n1 n2 sections pc. EVERY sec_labels_ok sections /\ EVERY sec_not_empty sections /\ loc_to_pc n1 n2 sections = SOME pc ==> pc_to_section pc sections = SOME n1`
recInduct loc_to_pc_ind \\
rw [pc_to_section_def] >-
rw [loc_to_pc_def] >-
(
  pop_assum mp_tac \\ rw[Once loc_to_pc_def] >-
  rw [pc_to_section_def] \\
  qmatch_assum_abbrev_tac `~xx` \\
  Cases_on `xs` \\ fs[] \\
  qpat_x_assum `_ = SOME pc` mp_tac \\
IF_CASES_TAC >-
(
  fs[] \\
  rw[] \\
fs [loc_to_pc_def] \\
rw[pc_to_section_def] \\
) \\
IF_CASES_TAC >-
(
  qmatch_assum_abbrev_tac `~xy` \\
fs[] \\
qpat_x_assum`_ ==> _`mp_tac \\
impl_tac >- (unabbrev_all_tac \\ fs []) \\

  )
           (
             Cases_on `k = n1 /\ n2 = 0` \\
rw[SYM (ASSUME ``0 = pc``)] \\
rw[pc_to_section_def] \\
fs [demorgan_thingy] \\
rw[pc_to_section_def] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\
fs [] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]
fs [] \\

POP_ASSUM (fn th => rw[SYM th]) \\
ASSUME ``0 = pc``] \\

  )

Cases_on `k` \\ Cases_on `pc` >-
fs[pc_to_section_def] \\
           (
rw[pc_to_section_def] \\
           )
  recInduct pc_to_section_ind
)

                                                    )
val pc_to_section_not_none_eq = Q.store_thm("pc_to_section_not_none_eq",
`!pc sections k n. pc_to_section pc sections = SOME n ==> pc_to_section pc sections = pc_to_section pc (Section k []::sections)`,
recInduct pc_to_section_ind \\
rw[pc_to_section_def] \\
                                           )

val pc_to_section_ind = theorem "pc_to_section_ind";
`!pc sections k. pc_to_section pc (Section k []::sections) = pc_to_section pc sections`,
recInduct pc_to_section_ind \\
rw [pc_to_section_def] \\

val asm_fetch_aux_simp_def = Define `
asm_fetch_aux_simp pc code =
 (case asm_fetch_aux pc code of
    | SOME (LabAsm (Jump (Lab n1 n2)) w bytes len) =>
      (case loc_to_pc n1 n2 code of
         | SOME pc' => SOME (if pc' = pc + 1 /\ SOME n1 = pc_to_section pc code /\ n2 <> 0 then Asm (Inst Skip) bytes len else LabAsm (Jump (Lab n1 n2)) w bytes len)
         | NONE => SOME (LabAsm (Jump (Lab n1 n2)) w bytes len)
      )
    | x => x
 )
`

val lab_simp_asm_fetch_aux_simp = Q.store_thm("lab_simp_asm_fetch_aux_simp",
`!s pc. asm_fetch_aux pc (lab_simp s) = asm_fetch_aux_simp pc s`,
recInduct lab_simp_ind \\
rw [lab_simp_def, NULL_EQ] >-
(
  rw[asm_fetch_aux_def, asm_fetch_aux_simp_def, loc_to_pc_def] \\
  every_case_tac \\ fs[] \\ rw []
) \\
rw [asm_fetch_aux_simp_def] \\
Cases_on `lines` \\


val lab_simp_asm_fetch_aux = Q.store_thm("state_rel_asm_fetch_aux",
`!s pc. asm_fetch_aux pc (lab_simp s) = asm_fetch_aux pc s \/
                             (?l w wl k k' n1 n2. asm_fetch_aux pc s = SOME (LabAsm (Jump (Lab n1 n2)) w wl k) /\
asm_fetch_aux (pc + 1) s = SOME (Label n1 n2 k') /\
asm_fetch_aux pc (lab_simp s) = SOME (Asm (Inst Skip) wl k))
  \/ s = []`

ho_match_mp_tac lab_simp_ind\\
rw [lab_simp_def] \\
fs [NULL_EQ] >- (rw [asm_fetch_aux_def] \\ first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]) \\
Cases_on `lines` \\ fs[asm_fetch_aux_def] \\
Cases_on `t` >-
(
  fs[lab_simp_sec_def, asm_fetch_aux_def] \\
    top_case_tac \\ fs [asm_fetch_aux_def] >-
    (
      first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]
    ) >-
    (
    rw[] \\ first_x_assum (qspec_then `pc - 1` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[]
    )
) \\
IF_CASES_TAC >-
(
  Cases_on `h` \\ fs[lab_simp_sec_def] \\
) \\

fs[lab_simp_sec_def, asm_fetch_aux_def] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]


    (
      every_case_tac \\ fs [asm_fetch_aux_def, lab_simp_def] \\
                     TRY (first_x_assum (qspec_then `pc - 1` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[] \\ NO_TAC) \\
                     TRY (first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[] \\ NO_TAC)
    )



                                        )
ho_match_mp_tac asm_fetch_aux_ind\\
simp[asm_fetch_aux_def] \\
conj_tac >-
(
  simp[lab_simp_def, lab_simp_sec_def] \\
  rw[]\\
  rw[lab_simp_def]
) \\
ntac 6 strip_tac\\
reverse IF_CASES_TAC \\
fs[] >-
(
  IF_CASES_TAC >-
  (
    fs[lab_simp_def] \\
Cases_on `ys` \\ fs[lab_simp_sec_def] \\
top_case_tac \\ fs[asm_fetch_aux_def] \\
every_case_tac \\ fs[asm_fetch_aux_def]\\
rw[lab_simp_def, lab_simp_sec_def, asm_fetch_aux_def]
  )
fs[lab_simp_def, lab_simp_sec_def, asm_fetch_aux_def] \\
)

(EVAL_TAC\\ rw[]) \\
EVAL_TAC
conj_tac >-
(
  rpt gen_tac \\
disch_then assume_tac \\
simp[Once lab_simp_def, lab_simp_sec_def] \\
fs []
                                     )
val state_rel_asm_fetch = Q.store_thm("state_rel_asm_fetch",
`state_rel s1 t1 ==>
   (asm_fetch s1 = asm_fetch t1 \/
                   (?wl k. asm_fetch t1 = SOME (Asm (Inst Skip) wl k) /\
?l w wl k. asm_fetch s1 = SOME (LabAsm (Jump l) w wl k)))`
rw [asm_fetch_def, state_rel_def] \\
                                      )

val lab_simp_correct = Q.store_thm("lab_simp_correct",
`!(s1:('a,'ffi) labSem$state) t1 res s2.
 (evaluate s1 = (res,s2)) /\ state_rel s1 t1 ==>
                             ?t2. (evaluate t1 = (res,t2)) /\ state_rel s2 t2`,
  ho_match_mp_tac evaluate_ind \\
  rw [] \\
  qhdtm_x_assum `evaluate` mp_tac \\
  simp [Once evaluate_def] \\
  IF_CASES_TAC >-
    (rw[] \\
     first_assum (part_match_exists_tac (el 2 o strip_conj) o concl) \\
     simp [] \\ simp [Once evaluate_def] \\ fs [state_rel_def] \\ rw [] \\ fs []) \\
  top_case_tac \\ fs [] \\
  >- (rw[] \\ CONV_TAC (QUANT_CONV $ LAND_CONV $ LAND_CONV $ REWR_CONV $ evaluate_def))
*)

val _ = export_theory ();
