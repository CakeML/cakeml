open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory stringTheory relationTheory rich_listTheory pairTheory arithmeticTheory finite_mapTheory
open miscLib miscTheory bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeLabelsTheory bytecodeTerminationTheory
open intLangTheory intLangExtraTheory toBytecodeTheory compilerTheory compilerTerminationTheory
open modLangProofTheory conLangProofTheory exhLangProofTheory patLangProofTheory intLangProofTheory bytecodeProofTheory free_varsTheory 
open replTheory printTheory inferPropsTheory inferSoundTheory terminationTheory

val _ = new_theory"printing"

(* TODO: move? *)

val FOLDL_emit_thm = store_thm("FOLDL_emit_thm",
  ``∀ls s. FOLDL (λs i. s with out := i::s.out) s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality])

(* value refinement *)

val exh_Cv_def = Define`
  exh_Cv v Cv ⇔
    ∃vp. v_pat (v_to_pat v) vp ∧ closed_pat vp ∧ syneq (v_to_Cv vp) Cv`

val v_bv_def = Define`
  v_bv (genv,gtagenv,exh,pp) v bv ⇔
    ∃v1 v2 vh Cv.
    v_to_i1 genv v v1 ∧
    v_to_i2 gtagenv v1 v2 ∧
    v_to_exh exh v2 vh ∧
    exh_Cv vh Cv ∧
    Cv_bv pp Cv bv`

val exh_Cv_syneq_trans = store_thm("exh_Cv_syneq_trans",
  ``∀v Cv Cv2. exh_Cv v Cv ∧ syneq Cv Cv2 ⇒ exh_Cv v Cv2``,
  rw[exh_Cv_def] >> metis_tac[syneq_trans])

val LIST_REL_exh_Cv_syneq_trans = store_thm("LIST_REL_exh_Cv_syneq_trans",
  ``∀vs Cvs Cvs2.
    LIST_REL syneq Cvs Cvs2
    ∧
    LIST_REL (exh_Cv) vs Cvs
    ⇒
    LIST_REL (exh_Cv) vs Cvs2``,
  rw[EVERY2_EVERY,EVERY_MEM] >> rfs[MEM_ZIP,PULL_EXISTS] >>
  metis_tac[exh_Cv_syneq_trans])

val LIST_REL_OPTREL_exh_Cv_syneq_trans = store_thm("LIST_REL_OPTREL_exh_Cv_syneq_trans",
  ``∀vs Cvs Cvs2.
    LIST_REL (OPTREL syneq) Cvs Cvs2
    ∧
    LIST_REL (OPTREL (exh_Cv)) vs Cvs
    ⇒
    LIST_REL (OPTREL (exh_Cv)) vs Cvs2``,
  rw[EVERY2_EVERY,EVERY_MEM] >> rfs[MEM_ZIP,PULL_EXISTS] >>
  fs[optionTheory.OPTREL_def] >>
  metis_tac[exh_Cv_syneq_trans,optionTheory.SOME_11,optionTheory.NOT_SOME_NONE])

val LIST_REL_sv_rel_exh_Cv_syneq_trans = store_thm("LIST_REL_sv_rel_exh_Cv_syneq_trans",
  ``∀vs Cvs Cvs2.
     LIST_REL (sv_rel syneq) Cvs Cvs2 ∧
     LIST_REL (sv_rel exh_Cv) vs Cvs ⇒
     LIST_REL (sv_rel exh_Cv) vs Cvs2``,
  rw[LIST_REL_EL_EQN] >>
  fs[evalPropsTheory.sv_rel_cases,PULL_EXISTS] >>
  rpt(first_x_assum(qspec_then`n`mp_tac)) >> simp[] >> rw[] >> fs[] >>
  metis_tac[exh_Cv_syneq_trans,LIST_REL_exh_Cv_syneq_trans])

val Cv_bv_can_Print = save_thm("Cv_bv_can_Print",prove(
  ``(∀Cv bv. Cv_bv pp Cv bv ⇒ IS_SOME (bv_to_string bv)) ∧
    (∀bvs ce env defs. benv_bvs pp bvs ce env defs ⇒ T)``,
  ho_match_mp_tac Cv_bv_ind >> simp[bv_to_string_def,bvs_to_chars_thm] >>
  rw[] >> pop_assum mp_tac >> simp[] >>
  simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rw[] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MEM_EL,EL_MAP])
  |> CONJUNCT1)

(* printing *)

val MAP_PrintC_thm = store_thm("MAP_PrintC_thm",
  ``∀ls bs bc0 bc1 bs'.
    bs.code = bc0 ++ (MAP PrintC ls) ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs' = bs with <| output := bs.output ++ ls; pc := next_addr bs.inst_length (bc0 ++ (MAP PrintC ls))|>
    ⇒
    bc_next^* bs bs'``,
  Induct >- (
    simp[] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[] >> rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (PrintC h)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality,IMPLODE_EXPLODE_I] >>
  qexists_tac`bc0 ++ [PrintC h]` >>
  simp[FILTER_APPEND,SUM_APPEND])

val code_labels_ok_MAP_PrintC = store_thm("code_labels_ok_MAP_PrintC",
  ``∀ls. code_labels_ok (MAP PrintC ls)``,
  Induct>>simp[]>>rw[]>>match_mp_tac code_labels_ok_cons>>simp[])
val _ = export_rewrites["code_labels_ok_MAP_PrintC"]

val word8 = ``Infer_Tapp [] TC_word8``

val print_bv_def = Define`
  print_bv ty bv =
    if ty = ^word8 then
      STRCAT "0wx" (word_to_hex_string ((n2w (Num (dest_Number bv))):word8))
    else THE (bv_to_string bv)`

val print_bv_print_v = prove(
  ``(∀genv v v1. v_to_i1 genv v v1 ⇒
      ∀gtagenv v2 exh vh Cv pp ty bv.
        v_to_i2 gtagenv v1 v2 ∧
        v_to_exh exh v2 vh ∧ exh_Cv vh Cv ∧
        Cv_bv pp Cv bv ∧
        (ty = ^word8 ⇔ ∃w. v = Litv (Word8 w))
        ⇒
        print_bv ty bv = print_v v) ∧
    (∀genv vs vs1. vs_to_i1 genv vs vs1 ⇒ T) ∧
    (∀genv env env1. env_to_i1 genv env env1 ⇒ T) ∧
    (∀genv map sh env. global_env_inv_flat genv map sh env ⇒ T) ∧
    (∀genv mods tops menv sh env. global_env_inv genv mods tops menv sh env ⇒ T)``,
  ho_match_mp_tac v_to_i1_ind >> simp[] >>
  conj_tac >- (
    simp[Once v_to_i2_cases,exh_Cv_def] >> rw[] >>
    simp[print_bv_def,print_v_def] >>
    fs[Once Cv_bv_cases,print_lit_def] >>
    rw[] >> fs[bv_to_string_def,bvs_to_chars_thm] >- (
      simp[EVERY_MAP,IMPLODE_EXPLODE_I,MAP_MAP_o,combinTheory.o_DEF,integerTheory.INT_ABS_NUM,CHR_ORD] ) >>
    Cases_on`b`>>simp[print_v_def,print_lit_def] ) >>
  rpt conj_tac >>
  simp[Once v_to_i2_cases] >>
  rw[] >> fs[exh_Cv_def] >>
  TRY (
    rw[]>>fs[Once Cv_bv_cases,print_v_def,print_bv_def,bv_to_string_def] >>
    NO_TAC) >>
  rator_x_assum`v_to_exh`mp_tac >>
  rw[Once v_to_exh_cases,PULL_EXISTS] >>
  rator_x_assum`v_pat`mp_tac >>
  rw[Once v_pat_cases,PULL_EXISTS] >>
  rator_x_assum`syneq`mp_tac >>
  rw[Once syneq_cases,PULL_EXISTS,LET_THM] >>
  rator_x_assum`Cv_bv`mp_tac >>
  rw[Once Cv_bv_cases,PULL_EXISTS] >>
  simp[print_v_def,print_bv_def,bv_to_string_def])
val print_bv_print_v = save_thm("print_bv_print_v",CONJUNCT1 print_bv_print_v)

val print_bv_str_def = Define`print_bv_str (v,_,t) w = "val "++v++":"++(inf_type_to_string t)++" = "++(print_bv t w)++"\n"`

val _ = Parse.overload_on("print_bv_list",``λts ws. FLAT (MAP (UNCURRY (print_bv_str)) (ZIP (ts,ws)))``)

val print_bv_list_print_envE = store_thm("print_bv_list_print_envE",
  ``∀tvs bvs types env data.
    LIST_REL (v_bv data) (MAP SND env) bvs ∧
    types = convert_env2 tvs ∧
    EVERY (λt. (∀n. t ≠ Infer_Tuvar n) ∧ inf_type_to_string t = type_to_string (convert_t t)) (MAP (SND o SND) tvs) ∧
    LIST_REL (λ(x,_,t) (y,v). x = y ∧ (t = Tapp [] TC_word8 ⇔ ∃w. v = Litv (Word8 w))) types env
    ⇒
    print_bv_list tvs bvs = print_envE types env``,
  REWRITE_TAC[convert_env2_def] >>
  Induct_on`env` >- ( simp[print_envE_def] ) >>
  qx_gen_tac`x`>>PairCases_on`x` >> simp[PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  fs[GSYM AND_IMP_INTRO] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  `∃tv t. tvs = tv::t` by (Cases_on`tvs`>>fs[]) >> rw[] >> fs[] >> rw[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  PairCases_on`tv` >> fs[] >>
  simp[print_envE_def,print_bv_str_def] >>
  PairCases_on`data` >> fs[v_bv_def] >>
  first_x_assum(mp_tac o MATCH_MP print_bv_print_v) >>
  simp[GSYM AND_IMP_INTRO] >>
  disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
  disch_then match_mp_tac >>
  Cases_on`tv2`>>fs[convert_t_def])

val compile_print_vals_thm = store_thm("compile_print_vals_thm",
  ``∀tvs map cs. let cs' = compile_print_vals tvs map cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
         ∧ cs'.next_label = cs.next_label
         ∧ EVERY ($~ o is_Label) code ∧
         code_labels_ok code ∧
    ∀bs bc0 bvs.
    bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ LIST_REL (λ(v,_,t) bv. ∃n. FLOOKUP map v = SOME n ∧
                           el_check n bs.globals = SOME (SOME bv) ∧
                           IS_SOME (bv_to_string bv) ∧
                           (t = ^word8 ⇒
                            ∃w. bv = Number &(w2n(w:word8)))) tvs bvs
    ⇒
    let bs' = bs with <|pc := next_addr bs.inst_length (bc0++code)
                       ;output := bs.output ++ print_bv_list tvs bvs|> in
    bc_next^* bs bs'``,
  Induct >> simp[compile_print_vals_def] >- (
    simp[Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >>
    simp[bc_state_component_equality] )>>
  qx_gen_tac`v` >>
  PairCases_on`v` >> simp[compile_print_vals_def] >>
  simp[FOLDL_emit_thm] >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  first_x_assum(qspecl_then[`map`,`cs1`]mp_tac) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE] >>
  simp[EVERY_MAP] >> fs[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  qmatch_assum_abbrev_tac`(compile_print_vals tvs map cs1').next_label = X` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  fs[Abbr`cs1'`] >> pop_assum kall_tac >>
  conj_tac >- rw[] >>
  conj_tac >- (
    rw[]>>
    rpt(match_mp_tac code_labels_ok_cons>>simp[])>>
    match_mp_tac code_labels_ok_append>>simp[IMPLODE_EXPLODE_I]>>
    rpt(match_mp_tac code_labels_ok_append>>simp[]>>(TRY conj_tac)>>TRY(simp[code_labels_ok_def,uses_label_thm]>>NO_TAC))) >>
  rpt gen_tac >>
  strip_tac >>
  fs[IMPLODE_EXPLODE_I] >>
  Q.PAT_ABBREV_TAC`PrintI = if v2 = Z then Y else [Print]` >>
  `bs.code = bc0 ++ (MAP PrintC ("val "++v0++":"++inf_type_to_string v2++" = ")) ++ ([Gread n] ++ PrintI ++[PrintC(#"\n")]) ++ c1` by (
    simp[] ) >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc:=next_addr bs.inst_length (bc0++l1)
                          ;output:=STRCAT bs.output ("val "++v0++":"++inf_type_to_string v2++" = ")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`"val "++v0++":"++inf_type_to_string v2++" = "`>>
    qexists_tac`bc0` >>
    simp[Abbr`l1`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  `bc_fetch bs1 = SOME (Gread n)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0++l1` >>
    simp[Abbr`l2`] ) >>
  qmatch_assum_rename_tac`IS_SOME (bv_to_string bv)`[] >>
  `bc_next^* bs1 (bs1 with <|pc:=next_addr bs.inst_length(bc0++l1++l2)
                            ;output := STRCAT bs1.output (print_bv v2 bv)++"\n"|>)` by (
    qunabbrev_tac`PrintI` >> qunabbrev_tac`l2` >>
    BasicProvers.CASE_TAC >- (
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def] >>
      fs[libTheory.el_check_def] >>
      simp[bump_pc_def] >> simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
      qspecl_then[`"0wx"`,`bs1`,`bc0++l1++[Gread n]`]mp_tac MAP_PrintC_thm >>
      simp[Abbr`bs1`] >>
      discharge_hyps >- simp[SUM_APPEND,FILTER_APPEND] >>
      qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ bc_next^* bs1' bs2` >>
      `bs1' = bs1` by (
        simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] ) >>
      pop_assum SUBST1_TAC >>
      map_every qunabbrev_tac[`bs1`,`bs1'`] >>
      strip_tac >>
      srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      `bc_fetch bs3 = SOME PrintWord8` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`[PrintC #"\n"]++c1` >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
      simp[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs3`,wordsTheory.w2n_lt,bump_pc_def] >>
      match_mp_tac RTC_SUBSET >>
      qmatch_abbrev_tac`bc_next bs3 bs2` >>
      `bc_fetch bs3 = SOME (PrintC #"\n")` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs3`] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`c1`>>simp[SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_thm,bc_eval1_def,IMPLODE_EXPLODE_I,bump_pc_def] >>
      simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] >>
      simp[print_bv_def] ) >>
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC(SUC 0))` >>
    simp[NRC] >>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def,EL_APPEND1]>>
    fs[libTheory.el_check_def] >>
    simp[Abbr`P`]>>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    `bc_fetch bs1 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++[Gread n]` >>
      simp[Abbr`bs1`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def]>>
    simp[Abbr`bs1`]>>
    simp[Abbr`P`] >>
    simp[PULL_EXISTS] >>
    fs[IS_SOME_EXISTS] >>
    qmatch_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME (PrintC(#"\n"))` by (
      match_mp_tac bc_fetch_next_addr >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`c1` >>
      simp[Abbr`bs1`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality,IMPLODE_EXPLODE_I] >>
    simp[FILTER_APPEND,SUM_APPEND,print_bv_def] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  pop_assum mp_tac >>
  rpt(qpat_assum`bc_next^* a Y`kall_tac) >>
  first_x_assum(qspecl_then[`bs2`,`bc0++l1++l2`,`ys`]mp_tac) >>
  simp[Abbr`bs2`,Abbr`bs1`,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  strip_tac >>
  qmatch_abbrev_tac`bc_next^* bs bs2'` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,Abbr`l1`] >>
    conj_tac >- (
      rw[Abbr`PrintI`,Abbr`l2`] >>
      REWRITE_TAC[FILTER_APPEND] >>
      simp_tac(srw_ss())[SUM_APPEND] >>
      simp[FILTER_APPEND,SUM_APPEND]) >>
    simp[print_bv_str_def]) >>
  metis_tac[RTC_TRANSITIVE,transitive_def] )

val _ = Parse.overload_on("print_ctor",``λx. STRCAT x " = <constructor>\n"``)
val _ = Parse.overload_on("print_ctors",``λls. FLAT (MAP (λ(x,y). print_ctor x) ls)``)

val compile_print_ctors_thm = store_thm("compile_print_ctors_thm",
  ``∀ls cs. let cs' = compile_print_ctors ls cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
      ∧ EVERY ($~ o is_Label) code
      ∧ code_labels_ok code
      ∧ cs'.next_label = cs.next_label ∧
      ∀bs bc0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ⇒
      let bs' = bs with <|pc := next_addr bs.inst_length bs.code
           ; output := STRCAT bs.output (print_ctors ls)|> in
      bc_next^* bs bs'``,
  Induct >- (
    simp[compile_print_ctors_def,Once SWAP_REVERSE] >>
    rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  simp[compile_print_ctors_def,FOLDL_emit_thm,IMPLODE_EXPLODE_I] >>
  rw[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd x y` >>
  first_x_assum(qspec_then`cs1`mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE,EVERY_MAP] >> fs[] >>
  qmatch_assum_abbrev_tac`(compile_print_ctors ls cs1).next_label = X` >>
  conj_tac >- (
    match_mp_tac code_labels_ok_append >> simp[]>>
    match_mp_tac code_labels_ok_append >> simp[]>>
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  qmatch_abbrev_tac`((compile_print_ctors ls cs1').next_label = X) ∧ Y` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  simp[Abbr`X`,Abbr`Y`] >>
  rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc := next_addr bs.inst_length (bc0++l1++l2)
                          ;output := bs.output ++ (x0++" = <constructor>\n")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`x0 ++ " = <constructor>\n"` >>
    qexists_tac`bc0` >>
    simp[Abbr`l1`,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++l1++l2`]mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
  qmatch_abbrev_tac`bc_next^* bs bs3` >>
  `bs2 = bs3` by (
    simp[Abbr`bs3`,bc_state_component_equality,semanticPrimitivesTheory.id_to_string_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val compile_print_dec_thm = store_thm("compile_print_dec_thm",
  ``∀tvs map d cs. let cs' = compile_print_dec tvs map d cs in
      ∃code. cs'.out = REVERSE code ++ cs.out
        ∧ EVERY ($~ o is_Label) code
        ∧ cs'.next_label = cs.next_label
        ∧ code_labels_ok code ∧
      ∀bs bc0 bvs.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ LIST_REL
        (λ(v,_,t) bv. ∃n. FLOOKUP map v = SOME n ∧
                    el_check n bs.globals = SOME (SOME bv) ∧
                    IS_SOME (bv_to_string bv) ∧
                    (t = ^word8 ⇒
                     ∃w. bv = Number &(w2n(w:word8))))
        tvs bvs
      ⇒
      let str =
        case d of
        | Dtype ts => print_envC ([],build_tdefs NONE ts)
        | Dexn cn ts => print_envC ([],[(cn, (LENGTH ts, TypeExn))])
        | d => print_bv_list tvs bvs in
      let bs' = bs with
        <|pc := next_addr bs.inst_length (bc0++code)
         ;output := bs.output ++ str|> in
      bc_next^* bs bs'``,
  Cases_on`d` >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`tvs`, `map`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[])
  >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`tvs`,`map`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac)
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    ntac 2 gen_tac >>
    Induct_on`REVERSE l` >- (
      simp[compile_print_types_def,Once SWAP_REVERSE] >>
      simp[Once SWAP_REVERSE] >>
      simp[print_envC_def,semanticPrimitivesTheory.build_tdefs_def,LENGTH_NIL] >>
      rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    gen_tac >> (disch_then (assume_tac o SYM)) >>
    simp[compile_print_types_def] >>
    gen_tac >>
    specl_args_of_then``compile_print_ctors``compile_print_ctors_thm mp_tac >>
    simp[] >>
    disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
    Q.ISPEC_THEN`l`mp_tac SNOC_CASES >>
    strip_tac >> fs[] >> rw[] >> fs[] >>
    Q.PAT_ABBREV_TAC`cs1 = compile_print_ctors X cs` >>
    first_x_assum(qspec_then`cs1`mp_tac) >>
    simp[Abbr`cs1`] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    simp[] >>
    simp[Once SWAP_REVERSE] >>
    conj_tac >- (
      simp[code_labels_ok_append]>>simp[] ) >>
    rpt strip_tac >>
    last_x_assum(qspecl_then[`bs with code := bc0 ++ c1`,`bc0`]mp_tac) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
    first_x_assum(qspecl_then[`bs1 with code := bs.code`]mp_tac) >>
    simp[Abbr`bs1`] >>
    simp[LENGTH_NIL] >>
    disch_then(qspec_then`bvs`mp_tac) >> simp[] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`] ) >>
    qmatch_abbrev_tac`bc_next^* bs bs2'` >>
    `bs2' = bs2` by (
      simp[Abbr`bs2`,Abbr`bs2'`] >>
      simp[bc_state_component_equality] >>
      simp[semanticPrimitivesTheory.build_tdefs_def,print_envC_def] >>
      simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] >>
      simp[UNCURRY,astTheory.mk_id_def] >>
      simp[LAMBDA_PROD] ) >>
    metis_tac[RTC_TRANSITIVE,transitive_def])
  >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`tvs`, `map`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[])
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    simp[compile_print_types_def] >>
    rw[] >>
    qspecl_then[`[s,l]`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
    simp[] >> rw[] >> simp[] >>
    simp[print_envC_def]))

val compile_print_err_thm = store_thm("compile_print_err_thm",
  ``∀cs. let cs' = compile_print_err cs in
    ∃code.
      cs'.out = REVERSE code ++ cs.out ∧
      between_labels code cs.next_label cs'.next_label ∧
      code_labels_ok code ∧
      ∀bs bc0 st0 tag bv.
        bs.code = bc0 ++ code ∧
        good_labels cs.next_label bc0 ∧
        bs.pc = next_addr bs.inst_length bc0 ∧
        bs.stack = (Block(block_tag+tag)(if tag = none_tag then [] else [bv]))::st0 ∧
        (tag ≠ none_tag ⇒ IS_SOME (bv_to_string bv))
      ⇒ ∃pc.
        let str = if tag ≠ none_tag then "raise " ++ (THE (bv_to_string bv)) ++ "\n" else "" in
        let bs' = bs with <| pc := pc
                           ; stack := st0
                           ; output := bs.output ++ str |> in
         bc_next^* bs bs' ∧
         if tag ≠ none_tag then bc_fetch bs' = SOME (Stop F) else
         pc = next_addr bs.inst_length (bc0 ++ code)``,
  simp[compile_print_err_def] >>
  rw[Once SWAP_REVERSE] >- ( EVAL_TAC >> simp[] )
  >- ( rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  Q.PAT_ABBREV_TAC`str:string = if tag ≠ none_tag then X else Y` >>
  `bc_fetch bs = SOME(Stack(Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
  `bc_fetch bs1 = SOME(Stack(TagEq(block_tag+none_tag)))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp_tac (srw_ss()) [Abbr`bs1`] >>
    qexists_tac`TAKE (LENGTH bc0 + 1) bs.code` >>
    simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND,IMPLODE_EXPLODE_I] >>
    NO_TAC) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`,bc_eval_stack_def] >>
  qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
  `bc_fetch bs1 = SOME(JumpIf (Lab cs.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp_tac (srw_ss()) [Abbr`bs1`] >>
    qexists_tac`TAKE (LENGTH bc0 + 2) bs.code` >>
    simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
    NO_TAC) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`] >>
  simp[PULL_EXISTS,bc_find_loc_def] >>
  exists_suff_gen_then mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  disch_then(qspec_then`LENGTH bc0 + 14`mp_tac o CONV_RULE (RESORT_FORALL_CONV(sort_vars["k"]))) >>
  disch_then exists_suff_tac >>
  simp[EL_APPEND1,EL_APPEND2,RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    rator_x_assum`good_labels`mp_tac >>
    rpt(pop_assum kall_tac) >>
    REWRITE_TAC[FILTER_APPEND] >>
    EVAL_TAC >> rpt strip_tac >>
    fsrw_tac[ARITH_ss][ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_MEM,FILTER_MAP] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  reverse(Cases_on`tag=none_tag`>>fs[]) >- (
    rfs[bc_fetch_def] >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
    `bc_fetch bs1 = SOME(Stack(PushInt 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp_tac (srw_ss()) [Abbr`bs1`] >>
      qexists_tac`TAKE (LENGTH bc0 + 3) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
      NO_TAC) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def] >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
    `bc_fetch bs1 = SOME(Stack El)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp_tac (srw_ss()) [Abbr`bs1`] >>
      qexists_tac`TAKE (LENGTH bc0 + 4) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
      NO_TAC) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def] >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
    qsuff_tac`∃bs3 p. bc_next^* bs1 bs3 ∧ bc_next^* bs3 (bs2 p) ∧ P p` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    exists_suff_gen_then (qspec_then`"raise "`mp_tac) MAP_PrintC_thm >>
    simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
    simp[Abbr`bs1`] >>
    disch_then(qspec_then`TAKE (LENGTH bc0 + 5) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    simp[TAKE_APPEND1,TAKE_APPEND2] >>
    discharge_hyps >- ( simp[SUM_APPEND,FILTER_APPEND] ) >>
    qmatch_abbrev_tac`bc_next^* bs1' bs3 ⇒ Z` >>
    strip_tac >> simp[Abbr`Z`] >> qexists_tac`bs3` >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 bs3 ∧ bc_next^* bs3 (bs2 p) ∧ P p` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    rw[] >>
    `bc_fetch bs3 = SOME(Print)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp_tac (srw_ss()) [Abbr`bs3`] >>
      qexists_tac`TAKE (LENGTH bc0 + 11) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >> NO_TAC) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs3`,Abbr`bs1`] >>
    fs[IS_SOME_EXISTS] >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
    qsuff_tac`∃bs3 p. bc_next^* bs1 bs3 ∧ bc_next^* bs3 (bs2 p) ∧ P p` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    exists_suff_gen_then (qspec_then`"\n"`mp_tac) MAP_PrintC_thm >>
    simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
    simp[Abbr`bs1`] >>
    disch_then(qspec_then`TAKE (LENGTH bc0 + 12) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    simp[TAKE_APPEND1,TAKE_APPEND2] >>
    discharge_hyps >- ( simp[SUM_APPEND,FILTER_APPEND] ) >>
    qmatch_abbrev_tac`bc_next^* bs1' bs3 ⇒ Z` >>
    strip_tac >> simp[Abbr`Z`] >> qexists_tac`bs3` >>
    qho_match_abbrev_tac`∃p. bc_next^* bs1 bs3 ∧ bc_next^* bs3 (bs2 p) ∧ P p` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    rw[] >>
    `bc_fetch bs3 = SOME(Stop F)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp_tac (srw_ss()) [Abbr`bs3`] >>
      qexists_tac`TAKE (LENGTH bc0 + 13) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      REWRITE_TAC[FILTER_APPEND] >>
      EVAL_TAC >>
      REWRITE_TAC[GSYM SUM_SUM_ACC] >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality] >>
    rfs[Abbr`P`,bc_fetch_def]) >>
  qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
  `bc_fetch bs1 = SOME(Stack Pop)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp_tac (srw_ss()) [Abbr`bs1`] >>
    qexists_tac`TAKE (LENGTH bc0 + 15) bs.code` >>
    simp[TAKE_APPEND2] >>
    simp_tac std_ss [FILTER_APPEND,SUM_APPEND] >>
    EVAL_TAC ) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`,bc_eval_stack_def] >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
  simp[Abbr`bs2`,bc_state_component_equality] >>
  simp[Abbr`P`,TAKE_APPEND2] >>
  simp_tac std_ss [FILTER_APPEND,SUM_APPEND] >>
  EVAL_TAC >> simp[ADD1] >>
  REWRITE_TAC[GSYM SUM_SUM_ACC] >>
  simp[SUM_APPEND])

val compile_print_top_thm = store_thm("compile_print_top_thm",
  ``∀tys map t cs.
    let cs' = compile_print_top tys map t cs in
    ∃code.
      cs'.out = REVERSE code ++ cs.out ∧
      between_labels code cs.next_label cs'.next_label ∧
      code_labels_ok code ∧
      ∀bs bc0 st0 tag bv bvs.
        bs.code = bc0 ++ code ∧
        good_labels cs.next_label bc0 ∧
        bs.pc = next_addr bs.inst_length bc0 ∧
        bs.stack = (Block(block_tag+tag)(if tag = none_tag then [] else [bv]))::st0 ∧
        (tag ≠ none_tag ⇒ IS_SOME (bv_to_string bv)) ∧
        (∀d. tag = none_tag ∧ t = Tdec d ⇒
         case tys of SOME tvs =>
         LIST_REL
         (λ(v,_,t) bv. ∃n. FLOOKUP map v = SOME n ∧
                     el_check n bs.globals = SOME (SOME bv) ∧
                     IS_SOME (bv_to_string bv) ∧
                     (t = ^word8 ⇒ ∃w. bv = Number &(w2n(w:word8))))
         tvs bvs | NONE => T)
        ⇒ ∃pc.
        (let str =
          if tag ≠ none_tag then "raise " ++ THE(bv_to_string bv) ++ "\n" else
          (case tys of NONE => ""
          | SOME types => (case t of
            | Tmod mn _ _ => "structure "++mn++" = <structure>\n"
            | Tdec d => (case d of
              | Dtype ts => print_envC ([],build_tdefs NONE ts)
              | Dexn cn ts => print_envC ([],[(cn, (LENGTH ts, TypeExn))])
              | d => print_bv_list types bvs))) in
         let bs' = bs with <| pc := pc
                            ; stack := st0
                            ; output := bs.output ++ str |> in
          bc_next^* bs bs' ∧
          bc_fetch bs' = SOME (Stop (tag = none_tag)))``,
  Cases_on`tys` >> Cases_on`t` >>
  simp[compile_print_top_def,FOLDL_emit_thm] >>
  rpt gen_tac >> simp[Once SWAP_REVERSE] >>
  specl_args_of_then``compile_print_err``compile_print_err_thm mp_tac >>
  simp[] >> disch_then(qx_choose_then`bcr`strip_assume_tac) >> simp[Once SWAP_REVERSE] >>
  TRY (
    specl_args_of_then``compile_print_dec``compile_print_dec_thm mp_tac >>
    simp[] >> strip_tac >> simp[Once SWAP_REVERSE] ) >>
  (conj_tac >- (
     rator_x_assum`between_labels`mp_tac >>
     EVAL_TAC >>
     REWRITE_TAC[FILTER_APPEND] >>
     simp[MEM_FILTER,EVERY_FILTER,EVERY_MAP,MEM_MAP] >>
     REWRITE_TAC[FILTER_APPEND] >> EVAL_TAC >>
     simp[ALL_DISTINCT_APPEND,MEM_FILTER,MEM_MAP] >>
     simp[FILTER_MAP,combinTheory.o_DEF] >>
     fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
     fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt,PULL_EXISTS] >>
     CCONTR_TAC >> fs[] >> res_tac >> fs[])) >>
  (conj_tac >-
    (rpt(match_mp_tac code_labels_ok_cons >> simp[]) >>
     EVAL_TAC >> simp[MEM_MAP] >>
     rpt(rator_x_assum`code_labels_ok`mp_tac) >>
     EVAL_TAC >> metis_tac[])) >>
  rpt gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`str:string = if tag ≠ none_tag then X else Y` >>
  last_x_assum(qspec_then`bs with code := bc0 ++ bcr`mp_tac) >>
  simp[] >> disch_then(qspec_then`bv`mp_tac) >> simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
  `bc_next^* bs (bs1 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    first_assum(match_exists_tac o concl) >>
    simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
  (reverse(Cases_on`tag=none_tag`>>fs[]) >- (
     rfs[bc_fetch_def] >>
     qexists_tac`bs1.pc` >>
     reverse conj_tac >- (
       simp[Abbr`bs1`] >> fs[] >>
       metis_tac[bc_fetch_aux_append_code,APPEND_ASSOC] ) >>
     qmatch_abbrev_tac`bc_next^* bs bs1'` >>
     `bs1' = bs1 with code := bs.code` by (
       simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] ) >>
     rw[] )) >>
  qho_match_abbrev_tac`∃p. bc_next^* bs (bs2 p) ∧ P p` >>
  (qsuff_tac`∃p. bc_next^* (bs1 with code := bs.code) (bs2 p) ∧ P p` >-
     metis_tac[RTC_TRANSITIVE,transitive_def]) >>
  qunabbrev_tac`bs1` >> fs[] >>
  TRY (
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality,Abbr`P`] >>
    match_mp_tac bc_fetch_next_addr >>
    simp[] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >> simp[] )
  >- (
    qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
    qsuff_tac`∃bs3 p. bc_next^* bs1 bs3 ∧ bs3 = (bs2 p) ∧ P p` >- metis_tac[] >>
    exists_suff_gen_then (qspec_then`"structure "++s++" = <structure>\n"`mp_tac) MAP_PrintC_thm >>
    simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
    simp[Abbr`bs1`] >>
    disch_then(qspec_then`TAKE (LENGTH bc0 + LENGTH bcr) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    simp[TAKE_APPEND1,TAKE_APPEND2,IMPLODE_EXPLODE_I] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ Z` >>
    `bs3 = bs2 bs3.pc` by (
      simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality,IMPLODE_EXPLODE_I] ) >>
    rw[] >> qexists_tac`bs3.pc` >> conj_tac >- metis_tac[] >>
    simp[Abbr`P`,Abbr`bs3`,Abbr`bs2`] >>
    match_mp_tac bc_fetch_next_addr >>
    simp[] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >> simp[] >>
    simp[TAKE_APPEND1,TAKE_APPEND2,IMPLODE_EXPLODE_I] >>
    REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
    EVAL_TAC >>
    REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
    EVAL_TAC >>
    simp[GSYM SUM_SUM_ACC,SUM_APPEND] ) >>
  qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ c1 ++ code ++ c2` >>
  first_x_assum(qspecl_then[`bs1 with code := bc0 ++ c1 ++ code`,`bc0 ++ c1`,`bvs`]mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs10 bs20` >>
  qho_match_abbrev_tac`∃p. bc_next^* bs1 (bs2 p) ∧ P p` >>
  `bs1 = bs10 with code := bs.code` by (
    simp[Abbr`bs1`,Abbr`bs10`,bc_state_component_equality] ) >>
  `bc_next^* bs1 (bs20 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    first_assum (match_exists_tac o concl) >>
    simp[] >> unabbrev_all_tac >>
    pop_assum kall_tac >>
    simp[bc_state_component_equality] ) >>
  `bs2 bs20.pc = bs20 with code := bs.code` by (
    simp[Abbr`bs2`,Abbr`bs20`,bc_state_component_equality] ) >>
  qexists_tac`bs20.pc` >>
  conj_tac >- metis_tac[] >>
  simp[Abbr`P`,Abbr`bs20`] >>
  match_mp_tac bc_fetch_next_addr >>
  simp[] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >> simp[])

val _ = export_theory()
