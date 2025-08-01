(*
  Correctness proof for stack_to_lab
*)

open preamble
     stackSemTheory stackPropsTheory
     stack_allocTheory stack_to_labTheory
     labSemTheory labPropsTheory
     stack_removeProofTheory
     stack_allocProofTheory
     stack_namesProofTheory
     semanticsPropsTheory
local open word_to_stackProofTheory data_to_word_gcProofTheory stack_rawcallProofTheory in end

val _ = new_theory"stack_to_labProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val get_labels_def = stackSemTheory.get_labels_def;
val get_reg_value_def = targetSemTheory.get_reg_value_def;

(* val _ = set_prover (fn (tm,_) => mk_thm([],tm)); remove *)

Overload Loc = “wordLang$Loc”

(* TODO: move *)

Theorem word_sh_word_shift:
   word_sh a b c = SOME z ⇒ z = word_shift a b c
Proof
  EVAL_TAC >> srw_tac[][] >> every_case_tac >> full_simp_tac(srw_ss())[] >>
  EVAL_TAC >> srw_tac[][]
QED

Theorem assert_T[simp]:
   assert T s = s
Proof
  srw_tac[][assert_def,state_component_equality]
QED

Theorem word_cmp_word_cmp:
   (word_cmp cmp (Word w1) (Word w2) = SOME T) ⇔ word_cmp cmp w1 w2
Proof
  Cases_on`cmp`>>srw_tac[][labSemTheory.word_cmp_def]>>
  srw_tac[][asmTheory.word_cmp_def]
QED

Theorem asm_fetch_aux_no_label:
   ∀pc code.
   asm_fetch_aux pc code = SOME (Label l1 l2 x) ⇒ F
Proof
  ho_match_mp_tac asm_fetch_aux_ind >>
  srw_tac[][asm_fetch_aux_def] >> Cases_on`y`>>full_simp_tac(srw_ss())[]
QED

Definition dest_to_loc_def:
  dest_to_loc regs dest =
    case dest of INL p => p | INR r => case FAPPLY regs r of Loc loc _ => loc
End

Definition dest_to_loc'_def:
  dest_to_loc' regs dest =
    case dest of INL p => p | INR r => case regs r of Loc loc _ => loc
End

Theorem find_code_lookup:
   find_code dest regs code = SOME p ⇒
    lookup (dest_to_loc regs dest) code = SOME p ∧
    (∀r. dest = INR r ⇒ r ∈ FDOM regs)
Proof
  Cases_on`dest`>>srw_tac[][find_code_def,dest_to_loc_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >> srw_tac[][]
QED

Theorem not_is_Label_compile_jump[simp]:
   is_Label (compile_jump dest) ⇔ F
Proof
  Cases_on`dest`>>EVAL_TAC
QED

Theorem word_cmp_not_NONE[simp]:
   word_cmp cmp (Word w1) (Word w2) ≠ NONE
Proof
  Cases_on`cmp`>>srw_tac[][labSemTheory.word_cmp_def]
QED

Theorem word_cmp_negate_alt[simp]:
   asm$word_cmp (negate cmp) w1 w2 ⇔ ¬word_cmp cmp w1 w2
Proof
  Cases_on`cmp`>>EVAL_TAC
QED

Theorem word_cmp_negate[simp]:
   labSem$word_cmp (negate cmp) (w1) (w2) =
   OPTION_MAP $~ (labSem$word_cmp cmp (w1) (w2))
Proof
  Cases_on`word_cmp cmp (w1) (w2)`>>fs[]>>
  Cases_on`word_cmp (negate cmp) (w1) (w2)`>>fs[] >>
  Cases_on`w1`>>Cases_on`w2`>>fs[word_cmp_def]>>
  Cases_on`cmp`>>fs[word_cmp_def]>>rw[]
QED

(* -- Lemmas about code_installed, loc_to_pc and asm_fetch_aux -- *)

Definition code_installed_def:
  (code_installed n [] code = T) ∧
  (code_installed n (x::xs) code ⇔
   if is_Label x then
     (case x of Label l1 l2 _ => loc_to_pc l1 l2 code = SOME n) ∧
     code_installed n xs code
   else
     asm_fetch_aux n code = SOME x ∧
     code_installed (n+1) xs code)
End

Theorem code_installed_append_imp:
   ∀l1 pc l2 code. code_installed pc (l1 ++ l2) code ⇒
   code_installed pc l1 code ∧
   code_installed (pc+LENGTH (FILTER ($~ o is_Label) l1)) l2 code
Proof
  Induct>>simp[code_installed_def]>>srw_tac[][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1]
QED

Triviality code_installed_get_labels_IMP:
  !top e n q pc.
      code_installed pc (append (FST (flatten top e n q))) c /\
      (l1,l2) ∈ get_labels e ==>
      ?v. loc_to_pc l1 l2 c = SOME v
Proof
  recInduct flatten_ind \\ rw []
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [flatten_def]
  \\ Cases_on `p` \\ fs [get_labels_def] THEN1
   (every_case_tac
    \\ TRY pairarg_tac \\ fs []
    \\ TRY pairarg_tac \\ fs [code_installed_def]
    \\ rw [] \\ res_tac \\ fs []
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ fs [code_installed_def]
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ fs [code_installed_def])
  \\ every_case_tac \\ fs []
  \\ TRY pairarg_tac \\ fs []
  \\ TRY pairarg_tac \\ fs [code_installed_def]
  \\ TRY pairarg_tac \\ fs [code_installed_def]
  \\ rw [] \\ res_tac \\ fs [code_installed_def]
  \\ fs [get_labels_def]
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
QED

(* TODO: these may already be proved in lab_filter or lab_to_target,
         they ought to move into labProps
*)
Triviality asm_fetch_aux_SOME_append:
  ∀pc code l code2.
  asm_fetch_aux pc code = SOME l ⇒
  asm_fetch_aux pc (code++code2) = SOME l
Proof
  ho_match_mp_tac asm_fetch_aux_ind>>simp[asm_fetch_aux_def]>>rw[]
QED

Triviality asm_fetch_aux_SOME_isPREFIX:
  ∀pc code l code2.
  asm_fetch_aux pc code = SOME l /\
  code ≼ code2 ==>
  asm_fetch_aux pc code2 = SOME l
Proof
  rw[]>>fs[IS_PREFIX_APPEND]>>
  metis_tac[asm_fetch_aux_SOME_append]
QED

Theorem loc_to_pc_APPEND:
    ∀n m code pc code2.
  loc_to_pc n m code = SOME pc ⇒
  loc_to_pc n m (code ++ code2) = SOME pc
Proof
  ho_match_mp_tac loc_to_pc_ind>>rw[]
  >-
    fs[loc_to_pc_def]
  >>
  simp[Once loc_to_pc_def]>>
  rw[]
  >-
    fs[Once loc_to_pc_def]
  >>
  TOP_CASE_TAC>>fs[]>>rfs[]>>
  TRY(fs[Once loc_to_pc_def]>>rfs[]>>NO_TAC)>>
  rw[]>>rfs[]>>qpat_x_assum`_=SOME pc` mp_tac>>
  simp[Once loc_to_pc_def]>>fs[]>>
  TOP_CASE_TAC>>rw[]>>
  fs[]
QED

Theorem code_installed_APPEND:
    ∀ls pc code code2.
  code_installed pc ls code ==>
  code_installed pc ls (code ++ code2)
Proof
  Induct>>simp[code_installed_def]>> rw[]
  >-
    (TOP_CASE_TAC>>fs[is_Label_def]>>
    metis_tac[loc_to_pc_APPEND])
  >>
    metis_tac[asm_fetch_aux_SOME_append]
QED

Theorem code_installed_isPREFIX:
    ∀ls pc code code2.
  code_installed pc ls code ∧
  code ≼ code2 ==>
  code_installed pc ls code2
Proof
  rw[]>>
  fs[IS_PREFIX_APPEND]>>
  metis_tac[code_installed_APPEND]
QED

Theorem loc_to_pc_isPREFIX:
    ∀n m code pc code2.
  loc_to_pc n m code = SOME pc /\
  code ≼ code2 ==>
  loc_to_pc n m code2 = SOME pc
Proof
  rw[]>>fs[IS_PREFIX_APPEND]>>metis_tac[loc_to_pc_APPEND]
QED

Triviality MAP_prog_to_section_FST:
  MAP (λs. case s of Section n v => n) (MAP prog_to_section prog) =
  MAP FST prog
Proof
  match_mp_tac LIST_EQ>>rw[EL_MAP]>>Cases_on`EL x prog`>>fs[prog_to_section_def]>>
  pairarg_tac>>fs[]
QED

Theorem MAP_prog_to_section_Section_num:
    MAP Section_num (MAP prog_to_section prog) =
  MAP FST prog
Proof
  fs[GSYM MAP_prog_to_section_FST, MAP_EQ_f]>>
  Cases>>fs[]
QED

(* Appending on the other side *)
Theorem asm_fetch_aux_SOME_append2:
     ∀pc code l code2.
     asm_fetch_aux pc code2 = SOME l ⇒
     asm_fetch_aux
     (LENGTH (FLAT (MAP (FILTER ($~ o is_Label) o Section_lines) code))+ pc) (code++code2) = SOME l
Proof
  Induct_on`code`>>fs[]>>
  Cases>>
  Induct_on`l`>>fs[asm_fetch_aux_def]>>rw[]>>fs[ADD1]
QED

(* loc_to_pc on the other side *)
Theorem loc_to_pc_append2:
    ∀k ll code code2 pc.
  ¬MEM k (MAP Section_num code) /\
  EVERY sec_labels_ok code ∧
  loc_to_pc k ll code2 = SOME pc ⇒
  loc_to_pc k ll (code++code2) =
    SOME (pc + (LENGTH (FLAT (MAP (FILTER ($~ o is_Label) o Section_lines) code))))
Proof
  Induct_on`code`>>fs[]>>
  Cases>>Induct_on`l`>>fs[]
  >-
    fs[loc_to_pc_def]
  >>
  Cases>>rw[]
  >-
    (simp[Once loc_to_pc_def]>>fs[])
  >>
    simp[Once loc_to_pc_def]>>
    res_tac>>fs[]
QED

Theorem code_installed_append2:
    ∀lines pc c1 c2 k.
  ¬MEM k (MAP Section_num c1) /\
  EVERY sec_labels_ok c1 ∧
  EVERY (sec_label_ok k) lines ∧
  code_installed pc lines c2 ==>
  code_installed
  (LENGTH (FLAT (MAP (FILTER ($~ o is_Label) o Section_lines) c1))+ pc)
    lines (c1 ++ c2)
Proof
  Induct>>fs[code_installed_def]>>
  rpt strip_tac>>
  IF_CASES_TAC
  >-
    (Cases_on`h`>>fs[]>>
    first_x_assum old_drule>>
    disch_then old_drule>>
    disch_then old_drule>>
    fs[] >> strip_tac>>
    match_mp_tac loc_to_pc_append2>>fs[]>>
    metis_tac[])
  >>
    fs[]>>
    CONJ_TAC>-
      metis_tac[asm_fetch_aux_SOME_append2,ADD_COMM]>>
    fs[]>>
    first_x_assum old_drule>>
    rpt(disch_then old_drule)>>
    fs[]
QED

Theorem ALOOKUP_PARTITION:
    ∀ls n v.
  ALOOKUP ls n = SOME v ⇒
  ∃ls1 ls2.
  ls = ls1 ++ [(n,v)] ++ ls2 ∧
  ¬MEM n (MAP FST ls1)
Proof
  Induct>>fs[]>>Cases>>fs[]>>rw[]
  >-
    (qexists_tac`[]`>>
    simp[])
  >>
    first_x_assum old_drule>>rw[]>>
    qexists_tac`(q,r)::ls1`>>simp[]
QED

Definition code_installed'_def:
  (code_installed' n [] code ⇔ T) /\
  (code_installed' n (x::xs) code ⇔
     if is_Label x then code_installed' n xs code
     else asm_fetch_aux n code = SOME x ∧ code_installed' (n + 1) xs code)
End

Theorem code_installed'_cons_label:
   !lines pos.
      is_Label h ==>
      code_installed' pos lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)
Proof
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def]
QED

Theorem code_installed'_cons_non_label = Q.prove(`
  !lines pos.
      ~is_Label h ==>
      code_installed' (pos+1) lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)`,
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def])
  |> Q.SPECL [`lines`,`0`] |> SIMP_RULE std_ss [];

Theorem code_installed'_simp:
   !lines. code_installed' 0 lines (Section n (lines ++ rest)::other)
Proof
  Induct \\ fs [code_installed'_def]
  \\ fs [labSemTheory.asm_fetch_aux_def]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ fs [code_installed'_cons_label,code_installed'_cons_non_label]
QED

Theorem loc_to_pc_skip_section:
   !lines.
      n <> p ==>
      loc_to_pc n 0 (Section p lines :: xs) =
      case loc_to_pc n 0 xs of
      | NONE => NONE
      | SOME k => SOME (k + LENGTH (FILTER (\x. ~(is_Label x)) lines))
Proof
  Induct \\ once_rewrite_tac [labSemTheory.loc_to_pc_def] \\ fs []
  THEN1 (every_case_tac \\ fs [])
  \\ strip_tac \\ IF_CASES_TAC \\ fs [] \\ CASE_TAC \\ fs []
QED

Theorem asm_fetch_aux_add:
   !ys pc rest.
      asm_fetch_aux (pc + LENGTH (FILTER (λx. ¬is_Label x) ys))
        (Section pos ys::rest) = asm_fetch_aux pc rest
Proof
  Induct \\ fs [labSemTheory.asm_fetch_aux_def,ADD1]
QED

Definition labs_correct_def:
  (labs_correct n [] code ⇔ T) /\
  (labs_correct n (x::xs) code ⇔
     if is_Label x then labs_correct n xs code /\
       (case x of
        | Label l1 l2 v2 => loc_to_pc l1 l2 code = SOME n
        | _ => T)
     else labs_correct (n + 1) xs code)
End

val is_Label_def = labSemTheory.is_Label_def

Theorem code_installed_eq:
   !pc xs code.
      code_installed pc xs code <=>
      code_installed' pc xs code /\ labs_correct pc xs code
Proof
  Induct_on `xs`
  \\ fs [code_installed_def,code_installed'_def,labs_correct_def]
  \\ ntac 3 strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `h` \\ fs [is_Label_def]
  \\ rw [] \\ eq_tac \\ fs []
QED

Theorem code_installed_cons:
   !xs ys pos pc.
      code_installed' pc xs rest ==>
      code_installed' (pc + LENGTH (FILTER (λx. ¬is_Label x) ys)) xs
        (Section pos ys :: rest)
Proof
  Induct \\ fs [] \\ fs [code_installed'_def]
  \\ ntac 4 strip_tac \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ res_tac \\ fs [asm_fetch_aux_add]
QED

Triviality code_installed_prog_to_section_lemma:
  !prog4 n prog3.
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed' pc (append (FST (flatten T prog3 n (next_lab prog3 2))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc
Proof
  Induct_on `prog4` \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []
  THEN1
   (fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac \\ fs []
    \\ once_rewrite_tac [labSemTheory.loc_to_pc_def]
    \\ fs [code_installed'_simp])
  \\ res_tac \\ fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac
  \\ fs [loc_to_pc_skip_section,code_installed_cons]
QED

val extract_labels_def = labPropsTheory.extract_labels_def
val extract_labels_append = labPropsTheory.extract_labels_append

Theorem labs_correct_hd:
    ∀extra l.
  ALL_DISTINCT (extract_labels (extra++l)) ∧
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (extra++l)) ⇒
  labs_correct (LENGTH (FILTER (\x. ~(is_Label x)) extra)) l (Section n (extra++l) ::code)
Proof
  Induct_on`l`>>fs[labs_correct_def]>>rw[]
  >-
    (first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,labSemTheory.is_Label_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND])
  >-
    (Cases_on`h`>>fs[]>>
    ntac 2 (pop_assum mp_tac)>>
    rpt (pop_assum kall_tac)>>
    Induct_on`extra`>>fs[extract_labels_def]>>rw[]
    >-
      (once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
      fs[])
    >>
    `n = n' ∧ n0 ≠ 0` by
      (Cases_on`h`>>fs[extract_labels_append,extract_labels_def])>>
    once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
    Cases_on`h`>>fs[extract_labels_def]>>
    IF_CASES_TAC>>fs[extract_labels_append,extract_labels_def])
  >>
    first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND]
QED

Definition labels_ok_def:
  labels_ok code ⇔
  (*Section names are distinct*)
  ALL_DISTINCT (MAP (λs. case s of Section n _ => n) code) ∧
  EVERY (λs. case s of Section n lines =>
    let labs = extract_labels lines in
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) labs ∧
    ALL_DISTINCT labs) code
End

Theorem labels_ok_imp:
   ∀code.
   labels_ok code ⇒
   EVERY sec_labels_ok code ∧
   ALL_DISTINCT (MAP Section_num code) ∧
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) code
Proof
  Induct_on`code` \\ simp[]
  \\ Cases \\ simp[]
  \\ fs[labels_ok_def]
  \\ strip_tac \\ fs[]
  \\ reverse conj_tac
  >- (
    strip_tac \\ fs[MEM_MAP,EXISTS_PROD] \\ fs[]
    \\ qmatch_assum_rename_tac`MEM sec code`
    \\ first_x_assum(qspec_then`sec`mp_tac) \\ simp[]
    \\ CASE_TAC \\ fs[] )
  \\ Induct_on`l` \\ fs[]
  \\ Cases \\ fs[]
QED

Theorem labels_ok_labs_correct:
    ∀code.
  labels_ok code ⇒
  EVERY ( λs. case s of Section n lines =>
      case loc_to_pc n 0 code of
       SOME pc => labs_correct pc lines code
      | _ => T) code
Proof
  Induct>>fs[labels_ok_def]>>Cases_on`h`>>fs[]>>
  rw[]
  >-
    (once_rewrite_tac[labSemTheory.loc_to_pc_def]>>fs[]>>
    assume_tac (Q.SPEC `[]` labs_correct_hd)>>fs[])
  >>
    fs[EVERY_MEM]>>rw[]>>res_tac>>
    Cases_on`s`>>fs[]>>
    `n ≠ n'` by
      (fs[MEM_MAP]>>
      last_x_assum kall_tac>>
      last_x_assum (qspec_then`Section n' l'` assume_tac)>>rfs[])>>
    fs[loc_to_pc_skip_section]>>
    BasicProvers.EVERY_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>
    pop_assum kall_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    rpt (pop_assum kall_tac)>>
    qid_spec_tac`x`>>
    Induct_on`l'`>>rw[labs_correct_def]>>fs[AND_IMP_INTRO]
    >-
      (first_assum match_mp_tac>>
      Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
    >-
      (Cases_on`h`>>fs[]>>
      `n'' ≠ n` by
        (fs[extract_labels_def]>>
        first_x_assum(qspec_then`n'',n0` mp_tac)>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>
      ntac 5 (pop_assum kall_tac)>>
      ntac 2 (pop_assum mp_tac)>>
      rpt (pop_assum kall_tac)>>
      map_every qid_spec_tac [`n''`,`n0`,`l`]>>
      Induct>> once_rewrite_tac [labSemTheory.loc_to_pc_def]>>fs[]>>
      rw[]>>fs[is_Label_def,extract_labels_def,AND_IMP_INTRO]
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (first_assum match_mp_tac>>
        Cases_on`h`>>fs[extract_labels_def])
      >>
        rveq>>fs[loc_to_pc_skip_section]>>
        (first_x_assum(qspecl_then[`n0`,`n''`] mp_tac)>>
        impl_tac>- (Cases_on`h`>>fs[extract_labels_def])>>
        fs[]))
    >>
      first_x_assum (qspec_then`x+1` mp_tac)>>
      impl_tac
      >-
        (Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
      >>
       fs[]
QED

Theorem labs_correct_append:
    ∀ls pc.
  labs_correct pc (ls ++ rest) code ⇒
  labs_correct pc ls code
Proof
  Induct>>fs[labs_correct_def]>>rw[]
QED

Theorem code_installed_prog_to_section:
   !prog4 n prog3.
      labels_ok (MAP prog_to_section prog4) ∧
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed pc (append (FST (flatten T prog3 n (next_lab prog3 2))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc
Proof
  rpt strip_tac \\ fs [code_installed_eq]
  \\ old_drule code_installed_prog_to_section_lemma \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ imp_res_tac labels_ok_labs_correct
  \\ fs[EVERY_MEM,MEM_MAP]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then`prog_to_section (n,prog3)` mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC>>fs[stack_to_labTheory.prog_to_section_def]
  \\ pairarg_tac>>fs[]>>rveq>>fs[]
  \\ metis_tac[labs_correct_append]
QED

(* -- End code_installed lemmas  -- *)

Definition state_rel_def:
  state_rel (s:('a,'c,'ffi)stackSem$state) (t:('a,'c,'ffi)labSem$state) ⇔
    (∀n v. FLOOKUP s.regs n = SOME v ⇒ t.regs n = v) ∧
    (∀n v. FLOOKUP s.fp_regs n = SOME v ⇒ t.fp_regs n = v) ∧
    t.mem = s.memory ∧
    t.mem_domain = s.mdomain ∧
    t.shared_mem_domain = s.sh_mdomain ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    (∀n prog. lookup n s.code = SOME prog ⇒
      call_args prog t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg ∧
      ∃pc. code_installed pc
             (append (FST (flatten T prog n (next_lab prog 2)))) t.code ∧
           loc_to_pc n 0 t.code = SOME pc) ∧
    (* These two conjuncts are needed for Install *)
    domain s.code = set (MAP Section_num t.code) ∧
    EVERY sec_labels_ok t.code ∧
    ¬t.failed ∧
    t.link_reg ≠ t.len_reg ∧ t.link_reg ≠ t.ptr_reg ∧
    t.link_reg ≠ t.len2_reg ∧ t.link_reg ≠ t.ptr2_reg ∧
    ~(t.link_reg ∈ s.ffi_save_regs) /\
    (!k i n. k ∈ s.ffi_save_regs ==> t.io_regs n i k = NONE) /\
    (* might need to be cc_save_regs *)
    (!k n. k ∈ s.ffi_save_regs ==> t.cc_regs n k = NONE) /\
    (∀x. x ∈ s.mdomain ⇒ w2n x MOD (dimindex (:'a) DIV 8) = 0) ∧
    (∀x. x ∈ s.sh_mdomain ⇒ w2n x MOD (dimindex (:'a) DIV 8) = 0) ∧
    s.code_buffer = t.code_buffer ∧
    s.compile = (λc p. t.compile c (MAP prog_to_section p)) ∧
    (t.compile_oracle = λn. let (c,p,_)  = s.compile_oracle n in
                           (c,MAP prog_to_section p)) ∧
    (∀k. let (c,ps,_) = s.compile_oracle k in
      EVERY (λ(n,p).
        call_args p t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg ∧
        EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p) ∧
        ALL_DISTINCT (extract_labels p)) ps ∧
        (* This last conjunct might not be necessary *)
        ALL_DISTINCT (MAP FST ps) ) ∧
    ¬s.use_stack ∧
    ¬s.use_store ∧
    ¬s.use_alloc ∧
    good_dimindex(:'a)
End

Theorem loc_check_IMP_loc_to_pc:
   loc_check s.code (l1,l2) /\ state_rel s t1 ==>
    ?v. loc_to_pc l1 l2 t1.code = SOME v
Proof
  rw [loc_check_def] \\ fs [state_rel_def,EXTENSION]>>
  qpat_x_assum`!x._ ⇔ _`(qspec_then `l1` assume_tac)>> rfs[]>>
  fs [domain_lookup] \\ res_tac \\ fs []
  \\ imp_res_tac code_installed_get_labels_IMP \\ fs []
QED

Theorem state_rel_dec_clock:
   state_rel s t ⇒ state_rel (dec_clock s) (dec_clock t)
Proof
  srw_tac[][state_rel_def,stackSemTheory.dec_clock_def,labSemTheory.dec_clock_def] >>
  metis_tac[]
QED

Theorem state_rel_with_pc:
   state_rel s t ⇒ state_rel s (upd_pc pc t)
Proof
  srw_tac[][state_rel_def,upd_pc_def] >>
  metis_tac[]
QED

Theorem state_rel_with_clock:
   state_rel s t ⇒ state_rel (s with clock := k) (t with clock := k)
Proof
  srw_tac[][state_rel_def] >> metis_tac[]
QED

Theorem set_var_upd_reg:
   state_rel s t ⇒
   state_rel (set_var a b s) (upd_reg a b t)
Proof
  srw_tac[][state_rel_def,upd_reg_def,set_var_def,FUN_EQ_THM,APPLY_UPDATE_THM,FLOOKUP_UPDATE] >>
  srw_tac[][]>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[] \\ metis_tac []
QED

Theorem set_var_Word_upd_reg[simp]:
   state_rel s t ⇒
   state_rel (set_var a (Word b) s) (upd_reg a (Word b) t)
Proof
   METIS_TAC[set_var_upd_reg,wordSemTheory.is_word_def]
QED

Theorem set_fp_var_upd_fp_reg:
   state_rel s t ⇒
   state_rel (set_fp_var a b s) (upd_fp_reg a b t)
Proof
  srw_tac[][state_rel_def,upd_fp_reg_def,set_fp_var_def,FUN_EQ_THM,APPLY_UPDATE_THM,FLOOKUP_UPDATE] >>
  srw_tac[][]>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[] \\ metis_tac []
QED

Theorem mem_store_upd_mem:
   state_rel s t ∧ mem_store x y s = SOME s1 ⇒
   state_rel s1 (upd_mem x y t)
Proof
  srw_tac[][state_rel_def,upd_mem_def,stackSemTheory.mem_store_def,FUN_EQ_THM,APPLY_UPDATE_THM] >>
  srw_tac[][APPLY_UPDATE_THM] >> rev_full_simp_tac(srw_ss())[] >>
  fs[]
  >-
    metis_tac[]
  >>
  first_x_assum(qspec_then`k` assume_tac)>>rfs[]
QED

Theorem state_rel_read_reg_FLOOKUP_regs:
   state_rel s t ∧
   FLOOKUP s.regs x = SOME y ⇒
   y = read_reg x t
Proof
  srw_tac[][state_rel_def]>>full_simp_tac(srw_ss())[FLOOKUP_DEF]
QED

Theorem state_rel_read_fp_reg_FLOOKUP_fp_regs:
   state_rel s t ∧
   get_fp_var n s = SOME x ⇒
   x = read_fp_reg n t
Proof
  srw_tac[][state_rel_def,get_fp_var_def,read_fp_reg_def]>>
  full_simp_tac(srw_ss())[FLOOKUP_DEF]
QED

Theorem state_rel_get_var_imm:
   state_rel s t ∧
   get_var_imm r s = SOME x ⇒
   reg_imm r t = x
Proof
  Cases_on`r` \\ srw_tac[][get_var_imm_def] \\ full_simp_tac(srw_ss())[get_var_def]
  \\ metis_tac[state_rel_read_reg_FLOOKUP_regs]
QED

Theorem inst_correct:
   inst i s1 = SOME s2 ∧
   state_rel s1 t1 ⇒
   state_rel s2 (asm_inst i t1)
Proof
  simp[inst_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][assign_def,word_exp_def] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[LET_THM,get_vars_def,get_var_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac state_rel_read_reg_FLOOKUP_regs >> rfs[] >> rw[] >>
  imp_res_tac state_rel_read_fp_reg_FLOOKUP_fp_regs >> rfs[] >> rw[] >>
  imp_res_tac word_sh_word_shift >>
  full_simp_tac(srw_ss())[wordLangTheory.word_op_def] >> srw_tac[][] >>
  imp_res_tac state_rel_read_reg_FLOOKUP_regs >> rfs[] >> rw[] >>
  TRY ( full_simp_tac(srw_ss())[binop_upd_def] >> match_mp_tac set_var_upd_reg >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  TRY ( match_mp_tac set_fp_var_upd_fp_reg >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  TRY ( Cases_on`b`>>full_simp_tac(srw_ss())[binop_upd_def] >> NO_TAC) >>
  TRY (
    rename1 `mem_load` >>
    full_simp_tac(srw_ss())[stackSemTheory.mem_load_def,labSemTheory.mem_load_def,labSemTheory.addr_def] >>
    full_simp_tac(srw_ss())[word_exp_def,LET_DEF] \\ every_case_tac \\ full_simp_tac(srw_ss())[]>>
    res_tac \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] >>
    TRY ( qpat_x_assum`Loc _ _ = read_reg _ _`(assume_tac o SYM) ) >>
    TRY(qpat_x_assum`Word _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[]) >>
    `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( full_simp_tac(srw_ss())[state_rel_def] ) >> full_simp_tac(srw_ss())[] >>
    imp_res_tac state_rel_read_reg_FLOOKUP_regs >> rfs[] >> rw[] >>
    qmatch_assum_rename_tac`c1 + c2 ∈ s1.mdomain` >>
    `w2n (c1 + c2) MOD (dimindex (:'a) DIV 8) = 0` by metis_tac [state_rel_def] >>
    rfs[]>>
    full_simp_tac(srw_ss())[] \\ match_mp_tac set_var_upd_reg \\ full_simp_tac(srw_ss())[]) >>
  TRY (
    rename1`mem_store` >>
    full_simp_tac(srw_ss())[stackSemTheory.word_exp_def,LET_THM,IS_SOME_EXISTS] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.get_var_def] >> rpt var_eq_tac >>
    res_tac >>
    TRY ( qpat_x_assum`Loc _ _ = read_reg _ _`(assume_tac o SYM) ) >>
    TRY(qpat_x_assum`Word _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[]) >>
    `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( full_simp_tac(srw_ss())[state_rel_def] ) >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[labSemTheory.mem_store_def,labSemTheory.addr_def] >>
    imp_res_tac state_rel_read_reg_FLOOKUP_regs >> rfs[] >> rw[] >>
    qmatch_assum_abbrev_tac`mem_store cc _ _ = _` >>
    `cc ∈ s1.mdomain` by full_simp_tac(srw_ss())[stackSemTheory.mem_store_def] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    simp[] >>
    imp_res_tac mem_store_upd_mem >>
    qpat_x_assum`Word _ = _`(assume_tac o SYM) >> fs[]>> rfs[]) >>
  TRY (
    rename1`mem_store32`
    \\ fs[wordSemTheory.mem_store_32_def]
    \\ every_case_tac \\ fs[]
    \\ fs[mem_store32_def,addr_def]
    \\ fs[word_exp_def,wordLangTheory.word_op_def]
    \\ qpat_x_assum`IS_SOME _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM)
    \\ fs[]
    \\ fs[get_var_def]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ qhdtm_x_assum`FLOOKUP`mp_tac
    \\ match_mp_tac SWAP_IMP
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM)
    \\ simp[wordSemTheory.mem_store_32_def]
    \\ `s1.memory = t1.mem ∧ t1.mem_domain = s1.mdomain ∧ t1.be = s1.be` by fs[state_rel_def]
    \\ fs[] \\ strip_tac
    \\ TRY (qpat_x_assum`Word _ = read_reg _ _`(assume_tac o SYM)\\ fs[])
    \\ rveq
    \\ fs[GSYM upd_mem_def]
    \\ match_mp_tac (GEN_ALL mem_store_upd_mem)
    \\ asm_exists_tac
    \\ simp[stackSemTheory.mem_store_def]
    \\ simp[stackSemTheory.state_component_equality]
    \\ rveq \\ simp[]) >>
  TRY (
    qhdtm_x_assum`mem_load_32`mp_tac
    \\ fs[wordSemTheory.mem_load_32_def,labSemTheory.mem_load32_def,labSemTheory.addr_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ fs[word_exp_def,wordLangTheory.word_op_def]
    \\ qpat_x_assum`IS_SOME _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM) \\ fs[]
    \\ fs[get_var_def]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ qhdtm_x_assum`FLOOKUP`mp_tac
    \\ match_mp_tac SWAP_IMP
    \\ TRY (
         disch_then old_drule
         \\ disch_then (assume_tac o SYM) \\ fs[] )
    \\ `s1.memory = t1.mem ∧ t1.mem_domain = s1.mdomain ∧ t1.be = s1.be` by fs[state_rel_def]
    \\ fs[] \\ strip_tac) >>
  TRY (
    rename1`mem_store_byte_aux`
    \\ fs[wordSemTheory.mem_store_byte_aux_def]
    \\ every_case_tac \\ fs[]
    \\ fs[mem_store_byte_def,addr_def]
    \\ fs[word_exp_def,wordLangTheory.word_op_def]
    \\ qpat_x_assum`IS_SOME _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM)
    \\ fs[]
    \\ fs[get_var_def]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ qhdtm_x_assum`FLOOKUP`mp_tac
    \\ match_mp_tac SWAP_IMP
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM)
    \\ simp[wordSemTheory.mem_store_byte_aux_def]
    \\ `s1.memory = t1.mem ∧ t1.mem_domain = s1.mdomain ∧ t1.be = s1.be` by fs[state_rel_def]
    \\ fs[] \\ strip_tac
    \\ TRY (qpat_x_assum`Word _ = read_reg _ _`(assume_tac o SYM)\\ fs[])
    \\ rveq
    \\ fs[GSYM upd_mem_def]
    \\ match_mp_tac (GEN_ALL mem_store_upd_mem)
    \\ asm_exists_tac
    \\ simp[stackSemTheory.mem_store_def]
    \\ simp[stackSemTheory.state_component_equality]
    \\ rveq \\ simp[]) >>
  TRY (
    qhdtm_x_assum`mem_load_byte_aux`mp_tac
    \\ fs[wordSemTheory.mem_load_byte_aux_def,labSemTheory.mem_load_byte_def,labSemTheory.addr_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ fs[word_exp_def,wordLangTheory.word_op_def]
    \\ qpat_x_assum`IS_SOME _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ disch_then old_drule
    \\ disch_then (assume_tac o SYM) \\ fs[]
    \\ fs[get_var_def]
    \\ old_drule (GEN_ALL state_rel_read_reg_FLOOKUP_regs)
    \\ qhdtm_x_assum`FLOOKUP`mp_tac
    \\ match_mp_tac SWAP_IMP
    \\ TRY (
         disch_then old_drule
         \\ disch_then (assume_tac o SYM) \\ fs[] )
    \\ `s1.memory = t1.mem ∧ t1.mem_domain = s1.mdomain ∧ t1.be = s1.be` by fs[state_rel_def]
    \\ fs[] \\ strip_tac) >>
    fs[get_fp_var_def]>>res_tac>>fs[]
QED

Theorem flatten_leq:
   ∀t x y z. z ≤ SND (SND (flatten t x y z))
Proof
  ho_match_mp_tac flatten_ind >> srw_tac[][]>>
  ONCE_REWRITE_TAC[flatten_def] >>
  CASE_TAC >> simp[] >> full_simp_tac(srw_ss())[] >>
  TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >>
  rw[]
QED

Theorem no_ret_correct:
   ∀t p y z. FST(SND(flatten t p y z)) ⇒ ∀s. IS_SOME (FST (evaluate (p,s)))
Proof
  ho_match_mp_tac flatten_ind >> rw[] >>
  pop_assum mp_tac \\
  Cases_on`p`>>simp[Once flatten_def,stackSemTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[IS_SOME_EXISTS] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >>
  TRY pairarg_tac >> fs[] >> rw[stackSemTheory.evaluate_def] >>
  TRY pairarg_tac >> fs[] >> rw[] >> fs[stackSemTheory.evaluate_def] >>
  fs[EVAL ``flatten t Skip m n``] >>
  every_case_tac >> fs[] >>
  METIS_TAC[NOT_SOME_NONE,FST,option_CASES]
QED

val s = ``s:('a,'c,'ffi) labSem$state``;

Theorem compile_jump_correct:
   asm_fetch_aux pc code = SOME (compile_jump dest) ∧
   loc_to_pc (dest_to_loc' regs dest) 0 code = SOME pc' ∧
   (∀r. dest = INR r ⇒ ∃p. read_reg r s = Loc p 0) ∧
   ^s.pc = pc ∧ s.code = code ∧ s.regs = regs ∧ s.clock ≠ 0
   ⇒
   evaluate s = evaluate (upd_pc pc' (dec_clock s))
Proof
  Cases_on`dest`>>srw_tac[][compile_jump_def,dest_to_loc'_def] >>
  simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
  CASE_TAC >> full_simp_tac(srw_ss())[]
QED

Datatype:
  result_view = Vloc num num | Vtimeout | Verr
End

Definition result_view_def:
  (result_view (Result (Loc n1 n2)) = Vloc n1 n2) ∧
  (result_view (Exception (Loc n1 n2)) = Vloc n1 n2) ∧
  (result_view TimeOut = Vtimeout) ∧
  (result_view _ = Verr)
End
val _ = export_rewrites["result_view_def"];

Definition halt_word_view_def:
  (halt_word_view (Word 0w) = Halt Success) ∧
  (halt_word_view (Word _) = Halt Resource_limit_hit) ∧
  (halt_word_view _ = Error)
End
val _ = export_rewrites["halt_word_view_def"];

Definition halt_view_def:
  (halt_view (SOME (Halt w)) = SOME (halt_word_view w)) ∧
  (halt_view (SOME (FinalFFI outcome)) = SOME (Halt(FFI_outcome outcome))) ∧
  (halt_view _ = NONE)
End
val _ = export_rewrites["halt_view_def"];

val finish_tac =
  rename1`halt_view (SOME z)` \\ Cases_on`z` \\ fs[] >>
  imp_res_tac loc_to_pc_isPREFIX>>
  imp_res_tac code_installed_isPREFIX>>fs[]>>
  TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[]) >>
  TRY (
    map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
    reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,evaluate_mono] >>
    gen_tac >>
    qpat_abbrev_tac`ss:('a,'c,'ffi)labSem$state = _ _` >>
    first_x_assum(qspec_then`ss`mp_tac) >>
    impl_tac >- (
      simp[Abbr`ss`] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
      full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
      every_case_tac >> full_simp_tac(srw_ss())[]) >>
    simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
    strip_tac >>
    last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
    last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
    simp[] >> NO_TAC ) >>
  TRY(rename1 `FFI_outcome` >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,
          inc_pc_def,dec_clock_def,upd_reg_def,lab_to_loc_def] >>
      qexists_tac `ck + ck' + 1` >> simp[] >>
      qmatch_goalsub_abbrev_tac `evaluate a1` >>
      first_x_assum(qspec_then `a1` mp_tac) >>
      impl_tac >- (
       simp[Abbr`a1`] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
       full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
       full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
       full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
       every_case_tac >> full_simp_tac(srw_ss())[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`a1`] >> NO_TAC) >>
  simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,
       inc_pc_def,dec_clock_def,upd_reg_def,lab_to_loc_def] >>
  map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
  qpat_abbrev_tac`ss:('a,'c,'ffi)labSem$state = _ _` >>
  first_x_assum(qspec_then`ss`mp_tac) >>
  (impl_tac >- (
     simp[Abbr`ss`] >>
     srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
     full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
     full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
     full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
     every_case_tac >> full_simp_tac(srw_ss())[])) >>
  simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
  first_x_assum(qspec_then`ck'`mp_tac) \\ simp[] >>
  first_x_assum(qspec_then`ck'`mp_tac) \\ simp[];

(* Proving that stack_to_lab generates labels_ok *)
val sextract_labels_def = stackPropsTheory.extract_labels_def

Theorem next_lab_non_zero:
    ∀p. 2 ≤ next_lab p 2
Proof
  once_rewrite_tac [next_lab_EQ_MAX] \\ fs [MAX_DEF]
QED

Theorem stack_to_lab_lab_pres:
    ∀t p n nl.
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p) ∧
  ALL_DISTINCT (extract_labels p) ∧ ~t ∧
  next_lab p 2 ≤ nl ⇒
  let (cp,nr,nl') = flatten t p n nl in
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels (append cp)) ∧
  ALL_DISTINCT (extract_labels (append cp)) ∧
  (∀lab. MEM lab (extract_labels (append cp)) ⇒ MEM lab (extract_labels p) ∨ (nl ≤ SND lab ∧ SND lab < nl')) ∧
  nl ≤ nl'
Proof
  HO_MATCH_MP_TAC flatten_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [flatten_def]>>fs[extract_labels_def,sextract_labels_def]
  >-
    (Cases_on`s`>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def,sextract_labels_def,compile_jump_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    TRY
      (fs[ALL_DISTINCT_APPEND,extract_labels_append]>>rw[]>>
      CCONTR_TAC>>fs[]>>res_tac>>fs[]>>NO_TAC)
    >>
    `2 ≤ nl` by metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[extract_labels_append,ALL_DISTINCT_APPEND,extract_labels_def]>>
    `next_lab q 2 ≤ m'` by fs[]>>
    fs[]>>rfs[]>>
    `r < nl ∧ r' < nl` by
      fs[MAX_DEF]>>
    rw[]>>
    CCONTR_TAC>>fs[]>>
    res_tac>>fs[]>>
    imp_res_tac extract_labels_next_lab>>fs[]>>
    metis_tac[])
  >>
    (rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    `2 ≤ nl` by
      metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[ALL_DISTINCT_APPEND]>>
    qpat_x_assum`A=(cp,_,nl')` mp_tac>>
    BasicProvers.EVERY_CASE_TAC>>strip_tac>>rveq>>fs[extract_labels_def,extract_labels_append,ALL_DISTINCT_APPEND]>>
    TRY
      (rw[]>>
      CCONTR_TAC>>fs[]>>
      res_tac>>fs[]>>
      imp_res_tac extract_labels_next_lab>>fs[])>>
    metis_tac[])
QED

Theorem stack_to_lab_lab_pres_T:
    ∀t p n nl.
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p) ∧
  ALL_DISTINCT (extract_labels p) ∧ t ∧
  next_lab p 2 ≤ nl ⇒
  let (cp,nr,nl') = flatten t p n nl in
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (append cp)) ∧
  ALL_DISTINCT (extract_labels (append cp)) ∧
  (∀lab. MEM lab (extract_labels (append cp)) ⇒
         MEM lab (extract_labels p) ∨ SND lab < nl') ∧
  nl ≤ nl'
Proof
  fs [] \\ rpt gen_tac
  \\ Cases_on `flatten T p n nl = flatten F p n nl` THEN1
   (strip_tac
    \\ mp_tac (stack_to_lab_lab_pres |> SIMP_RULE std_ss [] |> SPEC_ALL) \\ fs []
    \\ pairarg_tac \\ fs [] \\ fs [EVERY_MEM,FORALL_PROD] \\ rw [] \\ res_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ Cases_on `p` \\ once_rewrite_tac [flatten_def] \\ simp []
  \\ rename [`Seq p1 p2`]
  \\ disch_then kall_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ once_rewrite_tac [next_lab_def] \\ fs []
  \\ rename [`flatten F p2 n nl1 = (ys,nr2,nl2)`]
  \\ fs [stackPropsTheory.extract_labels_def,extract_labels_append,ALL_DISTINCT_APPEND]
  \\ once_rewrite_tac [next_lab_EQ_MAX] \\ fs []
  \\ strip_tac
  \\ `next_lab p1 2 ≤ nl` by
      (ntac 2 (pop_assum mp_tac) \\ once_rewrite_tac [next_lab_EQ_MAX] \\ fs [])
  \\ qspecl_then [`F`,`p1`,`n`,`nl`] mp_tac stack_to_lab_lab_pres \\ simp []
  \\ strip_tac
  \\ qspecl_then [`F`,`p2`,`n`,`nl1`] mp_tac stack_to_lab_lab_pres \\ simp []
  \\ strip_tac
  \\ fs [EVERY_MEM]
  \\ simp_tac std_ss [FORALL_PROD]
  \\ `1 < nl` by
     (qpat_x_assum `next_lab p2 2 ≤ nl` mp_tac
      \\ once_rewrite_tac [next_lab_EQ_MAX] \\ fs [])
  \\ rw []
  \\ res_tac \\ fs []
  \\ CCONTR_TAC \\ res_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rveq \\ fs []
  \\ imp_res_tac extract_labels_next_lab \\ fs []
  \\ metis_tac []
QED

Theorem flatten_T_F:
  ~is_Seq p_2 ==>
  flatten T p_2 p_1 m = flatten F p_2 p_1 m
Proof
  Cases_on `p_2` \\ fs [stack_to_labTheory.is_Seq_def]
  \\ once_rewrite_tac [flatten_def] \\ simp []
QED

Theorem prog_to_section_labels_ok:
    EVERY (λn,p.
    let labs = extract_labels p in
    EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
    ALL_DISTINCT labs) prog ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  labels_ok (MAP prog_to_section prog)
Proof
  strip_tac>>
  fs[labels_ok_def,MAP_prog_to_section_FST,Once EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]>>
  rw[]>>fs[prog_to_section_def]>>
  first_x_assum old_drule>> rw[]>>
  pairarg_tac>>fs[]>>
  old_drule stack_to_lab_lab_pres_T>>fs[]>>
  disch_then(qspecl_then[`next_lab p_2 2`] assume_tac)>>rfs[]>>
  simp[extract_labels_append]>>rw[]
  >-
    (qsuff_tac`2 ≤ m` >> fs[]>>
    metis_tac[LESS_EQ_TRANS,next_lab_non_zero])
  >>
    fs[ALL_DISTINCT_APPEND]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[]>>
    imp_res_tac extract_labels_next_lab>>fs[]
  >- (fs [EVERY_MEM] \\ res_tac \\ fs [])
  \\ Cases_on `MEM (p_1,1) (extract_labels p_2)`
  >- (fs [EVERY_MEM] \\ res_tac \\ fs [])
  \\ fs [flatten_T_F]
  \\ drule stack_to_lab_lab_pres \\ fs []
  \\ qexists_tac `next_lab p_2 2` \\ fs []
  \\ disj2_tac \\ CCONTR_TAC \\ fs []
  \\ pop_assum (qspec_then `(p_1,1)` mp_tac) \\ fs []
  \\ `2 ≤ next_lab p_2 2` by fs [next_lab_non_zero]  \\ fs []
QED

Theorem flatten_correct:
   ∀prog s1 t r s2 n l (t1:('a,'c,'ffi)labSem$state).
     evaluate (prog,s1) = (r,s2) ∧ r ≠ SOME Error ∧
     state_rel s1 t1 ∧
     call_args prog t1.ptr_reg t1.len_reg t1.ptr2_reg t1.len2_reg t1.link_reg ∧
     code_installed t1.pc (append (FST (flatten t prog n l))) t1.code
     ⇒
     ∃ck t2.
     case halt_view r of
     | SOME res =>
       evaluate (t1 with clock := t1.clock + ck) =
         (res,t2) ∧ t2.ffi = s2.ffi
     | NONE =>
       (∀ck1. evaluate (t1 with clock := t1.clock + ck + ck1) =
         evaluate (t2 with clock := t2.clock + ck1)) ∧
       t2.len_reg = t1.len_reg ∧
       t2.ptr_reg = t1.ptr_reg ∧
       t2.len2_reg = t1.len2_reg ∧
       t2.ptr2_reg = t1.ptr2_reg ∧
       t2.link_reg = t1.link_reg ∧
       t1.code ≼ t2.code ∧
       case OPTION_MAP result_view r of
       | NONE =>
         t2.pc = t1.pc + LENGTH (FILTER ($~ o is_Label)
                           (append (FST(flatten t prog n l)))) ∧
         state_rel s2 t2
       | SOME (Vloc n1 n2) =>
           (∀n. IS_SOME (lookup n s2.code) ⇒ IS_SOME (loc_to_pc n 0 t2.code)) ∧
           ∀w. loc_to_pc n1 n2 t2.code = SOME w ⇒
               w = t2.pc ∧
               state_rel s2 t2
       | SOME Vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
       | _ => F
Proof
  recInduct stackSemTheory.evaluate_ind >>
  conj_tac >- (
    rename [`Skip`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    qexists_tac`0`>>simp[] >>
    METIS_TAC[with_same_clock,state_rel_def,IS_PREFIX_REFL] ) >>
  conj_tac >- (
    rename [`Halt`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var v s`>>full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    simp[] >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    qexists_tac`1`>>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    full_simp_tac(srw_ss())[get_var_def] >>
    full_simp_tac(srw_ss())[call_args_def,state_rel_def] >> rev_full_simp_tac(srw_ss())[] >>
    res_tac >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[]) >>
  conj_tac >- (
    rename [`Alloc`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  conj_tac >- (
    rename [`StoreConsts`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  conj_tac >- (
    rename [`Inst`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`inst i s`>>full_simp_tac(srw_ss())[]>>rpt var_eq_tac>>simp[]>>
    imp_res_tac inst_correct >>
    qexists_tac`1`>>
    full_simp_tac(srw_ss())[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    Cases_on`(asm_inst i t1).failed` >- full_simp_tac(srw_ss())[state_rel_def] >>
    simp[dec_clock_def,asm_inst_consts] >>
    qexists_tac`inc_pc (asm_inst i t1)` >>
    simp[inc_pc_def,asm_inst_consts] >>
    full_simp_tac(srw_ss())[state_rel_def,asm_inst_consts] >>
    METIS_TAC[]) >>
  conj_tac >- (
    rename [`Get`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  conj_tac >- (
    rename [`Set`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  conj_tac >- (
    rename [`OpCurrHeap`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  conj_tac >- (
    rename [`Tick`] >>
    simp[stackSemTheory.evaluate_def,flatten_def] >>
    rpt gen_tac >> strip_tac >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    Cases_on`s.clock=0`>>full_simp_tac(srw_ss())[]>>rpt var_eq_tac>>full_simp_tac(srw_ss())[]>-(
      qexists_tac`1`>>simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      Cases_on`t1.failed`>>full_simp_tac(srw_ss())[]>-full_simp_tac(srw_ss())[state_rel_def]>>
      simp[dec_clock_def] >>
      `t1.clock = 0` by full_simp_tac(srw_ss())[state_rel_def] >>
      qexists_tac`inc_pc t1` >>
      simp[inc_pc_def,empty_env_def] >>
      full_simp_tac(srw_ss())[state_rel_def]) >>
    qexists_tac`0`>>simp[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    Cases_on`t1.failed`>>full_simp_tac(srw_ss())[]>-full_simp_tac(srw_ss())[state_rel_def]>>
    qexists_tac`inc_pc (dec_clock t1)` >>
    full_simp_tac(srw_ss())[inc_pc_def,stackSemTheory.dec_clock_def,labSemTheory.dec_clock_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    fsrw_tac[ARITH_ss][] >>
    metis_tac[]) >>
  conj_tac >- (
    rename [`Seq`] >>
    srw_tac[][] >>
    qhdtm_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    strip_tac >>
    pairarg_tac >> full_simp_tac(srw_ss())[] >>
    qhdtm_x_assum`code_installed`mp_tac >>
    simp[Once flatten_def] >>
    Cases_on `t` THEN1
     (simp[UNCURRY] >> strip_tac >>
      full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] >>
      imp_res_tac code_installed_append_imp >>
      full_simp_tac(srw_ss())[Q.SPEC`Seq _ _`next_lab_thm] >>
      full_simp_tac(srw_ss())[call_args_def] >>
      reverse (Cases_on`res`)>>full_simp_tac(srw_ss())[]>-(
        rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
        first_x_assum old_drule >>
        disch_then old_drule >>
        disch_then old_drule >>
        strip_tac >>
        rename1`halt_view (SOME x)` \\ Cases_on`x` \\ fs[] >>
        TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[]) >>
        res_tac >>
        qexists_tac`ck`>>fsrw_tac[ARITH_ss][]>>
        TRY ( qexists_tac`t2` >> simp[] >> NO_TAC) >>
        metis_tac[] ) >>
      first_x_assum old_drule >>
      disch_then old_drule >>
      simp[] >>
      disch_then old_drule >> simp[] >>
      strip_tac >>
      first_x_assum old_drule >>
      CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``code_installed`` o fst o strip_comb))))) >>
      imp_res_tac code_installed_isPREFIX>>
      fsrw_tac[ARITH_ss][] >>
      fs [code_installed_def] >>
      disch_then old_drule >>
      strip_tac >>
      rename1`halt_view r` \\ Cases_on`r` \\ fs[] >>
      TRY(rename1`halt_view (SOME x)` \\ Cases_on`x` \\ fs[]) >>
      TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[])
      >- (
        CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``state_rel`` o fst o strip_comb))) >>
        asm_exists_tac >> simp[] >>
        simp[Q.SPECL[`b`,`Seq _ _`]flatten_def,UNCURRY] >>
        qexists_tac`ck+ck'`>>simp[FILTER_APPEND]>>srw_tac[][] >>
        last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
        fsrw_tac[ARITH_ss][]>>
        metis_tac[IS_PREFIX_TRANS]) >>
      res_tac >>
      ((CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``state_rel`` o fst o strip_comb))) >>
        asm_exists_tac >> simp[] ) ORELSE
       (CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`t2'` >> simp[])) >>
      qexists_tac`ck+ck'`>>simp[]>>srw_tac[][] >>
      last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
      fsrw_tac[ARITH_ss][]>>
      metis_tac[IS_PREFIX_TRANS]) >>
    simp[UNCURRY] >> strip_tac >>
    imp_res_tac code_installed_append_imp >>
    full_simp_tac(srw_ss())[Q.SPEC`Seq _ _`next_lab_thm] >>
    full_simp_tac(srw_ss())[call_args_def] >>
    reverse (Cases_on`res`)>>full_simp_tac(srw_ss())[]>-(
      rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
      first_x_assum old_drule >>
      disch_then old_drule >>
      disch_then old_drule >>
      strip_tac >>
      rename1`halt_view (SOME x)` \\ Cases_on`x` \\ fs[] >>
      TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[]) >>
      res_tac >>
      qexists_tac`ck`>>fsrw_tac[ARITH_ss][]>>
      TRY ( qexists_tac`t2` >> simp[] >> NO_TAC) >>
      metis_tac[] ) >>
    first_x_assum old_drule >>
    disch_then old_drule >>
    simp[] >>
    disch_then old_drule >> simp[] >>
    strip_tac >>
    first_x_assum old_drule >>
    CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``code_installed`` o fst o strip_comb))))) >>
    imp_res_tac code_installed_isPREFIX>>
    fsrw_tac[ARITH_ss][] >>
    disch_then old_drule >>
    strip_tac >>
    rename1`halt_view r` \\ Cases_on`r` \\ fs[] >>
    TRY(rename1`halt_view (SOME x)` \\ Cases_on`x` \\ fs[]) >>
    TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[])
    >- (
      CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``state_rel`` o fst o strip_comb))) >>
      asm_exists_tac >> simp[] >>
      simp[Q.SPECL[`F`,`Seq _ _`]flatten_def,UNCURRY] >>
      qexists_tac`ck+ck'`>>simp[FILTER_APPEND]>>srw_tac[][] >>
      last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
      fsrw_tac[ARITH_ss][]>>
      metis_tac[IS_PREFIX_TRANS]) >>
    res_tac >>
    ((CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``state_rel`` o fst o strip_comb))) >>
      asm_exists_tac >> simp[] ) ORELSE
     (CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`t2'` >> simp[])) >>
    qexists_tac`ck+ck'`>>simp[]>>srw_tac[][] >>
    last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
    fsrw_tac[ARITH_ss][]>>
    metis_tac[IS_PREFIX_TRANS]) >>
  conj_tac >- (
    rename [`Return`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var n s`>>full_simp_tac(srw_ss())[]>> Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    rpt var_eq_tac >> simp[] >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    `get_var n s = SOME (read_reg n t1)` by (
      full_simp_tac(srw_ss())[state_rel_def,get_var_def] >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
    full_simp_tac(srw_ss())[] >>
    qexists_tac`1`>>simp[] >> rev_full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      qexists_tac`t1 with clock := t1.clock + 1` >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      fs[state_rel_def] \\ metis_tac[IS_SOME_EXISTS]) >>
    simp[dec_clock_def] >>
    qmatch_assum_rename_tac`_ = SOME pc` >>
    qexists_tac`upd_pc pc t1` >>
    simp[upd_pc_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    metis_tac[IS_SOME_EXISTS]) >>
  conj_tac >- (
    rename [`Raise`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var n s`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    rpt var_eq_tac >> simp[] >>
    qexists_tac`1`>>simp[]>>
    full_simp_tac(srw_ss())[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    `get_var n s = SOME (read_reg n t1)` by (
      full_simp_tac(srw_ss())[state_rel_def,get_var_def] >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
    full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      qexists_tac`t1 with clock := t1.clock + 1` >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      fs[state_rel_def] \\ metis_tac[IS_SOME_EXISTS]) >>
    simp[dec_clock_def] >>
    qmatch_assum_rename_tac`_ = SOME pc` >>
    qexists_tac`upd_pc pc t1` >>
    simp[upd_pc_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    metis_tac[IS_SOME_EXISTS]) >>
  conj_tac >- (
    rename [`If`] >>
    rw[] >>
    fs[stackSemTheory.evaluate_def] >>
    Cases_on`get_var r1 s`>>fs[]>>
    Cases_on`get_var_imm ri s`>>fs[]>>
    qpat_x_assum`_ = (r,_)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac >>
    fs[Q.SPECL[`b`,`If _ _ _ _ _`]flatten_def,LET_THM] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    Cases_on`c1=Skip`>>fs[]>-(
      Cases_on`c2=Skip`>>fs[] >- (
        fs[Q.SPECL[`b`,`Skip`]flatten_def]>>
        rpt var_eq_tac >>
        full_simp_tac(srw_ss())[stackSemTheory.evaluate_def]>>
        rpt var_eq_tac >> simp[] >>
        map_every qexists_tac[`0`,`t1`] >>
        simp[] ) >>
      full_simp_tac(srw_ss())[Q.SPECL[`b`,`Skip`]flatten_def]>>
      rpt var_eq_tac >>
      full_simp_tac(srw_ss())[stackSemTheory.evaluate_def]>>
      full_simp_tac(srw_ss())[code_installed_def] >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      qmatch_goalsub_rename_tac`if xx then _ else _` >>
      Cases_on`xx`>>fs[] >- (
        rpt var_eq_tac >> simp[] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def] >>
        qpat_abbrev_tac`pc = LENGTH _ + _` >>
        old_drule state_rel_with_pc >> strip_tac >>
        first_x_assum old_drule >>
        simp[call_args_def,next_lab_thm] >>
        simp[upd_pc_def] >> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      full_simp_tac(srw_ss())[Q.SPEC`If _ _ _ _ _`next_lab_thm] >>
      old_drule (GEN_ALL state_rel_with_pc) >>
      disch_then(qspec_then`t1.pc+1`strip_assume_tac) >>
      first_x_assum old_drule >>
      full_simp_tac(srw_ss())[call_args_def] >>
      imp_res_tac code_installed_append_imp >>
      disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
      strip_tac >>
      simp[dec_clock_def,ADD1] >>
      fs[inc_pc_def,upd_pc_def] >>
      Cases_on`r`>>fs[] >- (
        first_x_assum(old_drule)>>simp[]>>
        simp[FILTER_APPEND]>> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>fs[] ) >>
      rveq >>
      reverse TOP_CASE_TAC \\ fs[]
      >- (
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[dec_clock_def,inc_pc_def] >>
        first_x_assum(old_drule)>>simp[] )
      \\ first_x_assum old_drule \\ simp[] \\ strip_tac >>
      TOP_CASE_TAC \\ fs[] >>
      qexists_tac`ck`>>simp[] >>
      qexists_tac`t2`>>simp[FILTER_APPEND]) >>
    Cases_on`c2=Skip`>>full_simp_tac(srw_ss())[]>-(
      full_simp_tac(srw_ss())[Q.SPECL[`b`,`Skip`]flatten_def]>>
      rpt var_eq_tac >>
      full_simp_tac(srw_ss())[stackSemTheory.evaluate_def]>>
      full_simp_tac(srw_ss())[code_installed_def] >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      qmatch_asmsub_rename_tac`if xx then _ else _` >>
      reverse(Cases_on`xx`)>>fs[] >- (
        rpt var_eq_tac >> simp[] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def] >>
        qpat_abbrev_tac`pc = LENGTH _ + _` >>
        old_drule state_rel_with_pc >> strip_tac >>
        first_x_assum old_drule >>
        simp[call_args_def,next_lab_thm] >>
        simp[upd_pc_def] >> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      full_simp_tac(srw_ss())[Q.SPEC`If _ _ _ _ _`next_lab_thm] >>
      old_drule (GEN_ALL state_rel_with_pc) >>
      disch_then(qspec_then`t1.pc+1`strip_assume_tac) >>
      first_x_assum old_drule >>
      full_simp_tac(srw_ss())[call_args_def] >>
      imp_res_tac code_installed_append_imp >>
      disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
      strip_tac >>
      simp[dec_clock_def,ADD1] >>
      fs[inc_pc_def,upd_pc_def] >>
      Cases_on`r`>>fs[] >- (
        first_x_assum old_drule >>
        simp[] >> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>fs[FILTER_APPEND] ) >>
      first_x_assum old_drule >>
      simp[] >> strip_tac >>
      reverse TOP_CASE_TAC \\ fs[]
      >- (
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[dec_clock_def,inc_pc_def] >>
        qexists_tac`ck` \\ simp[]) >>
      qexists_tac`ck`>>simp[] >>
      qexists_tac`t2`>>simp[] >>
      TOP_CASE_TAC >> fs[FILTER_APPEND]) >>
    Cases_on`nr1`>>full_simp_tac(srw_ss())[] >- (
      full_simp_tac(srw_ss())[code_installed_def] >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      qmatch_asmsub_rename_tac`if xx then _ else _` >>
      (Cases_on`xx`)>>fs[] >- (
        `IS_SOME r` by metis_tac[no_ret_correct,FST,SND] >>
        full_simp_tac(srw_ss())[IS_SOME_EXISTS] >>
        rpt var_eq_tac >> simp[] >>
        rfs[call_args_def,FILTER_APPEND] >>
        simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
        imp_res_tac code_installed_append_imp >>
        imp_res_tac code_installed_append_imp >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        old_drule (GEN_ALL state_rel_with_pc) >>
        disch_then(qspec_then`t1.pc+1`mp_tac) >>
        strip_tac >> rfs[] >>
        first_x_assum old_drule >> fs[] >>
        disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
        strip_tac >>
        reverse TOP_CASE_TAC \\ fs[upd_pc_def] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def]
        \\ simp[inc_pc_def,dec_clock_def] \\ rfs[]
        \\ qexists_tac`ck+1`>>simp[] >>
        qexists_tac`t2`>>simp[]) >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      simp[get_pc_value_def] >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      full_simp_tac(srw_ss())[code_installed_def] >>
      fs[FILTER_APPEND] >>
      qmatch_assum_abbrev_tac`code_installed pc (append ys) _` >>
      old_drule state_rel_with_pc >> strip_tac >>
      rfs[] >>
      first_x_assum old_drule >>
      full_simp_tac(srw_ss())[call_args_def] >>
      full_simp_tac(srw_ss())[Q.SPEC`If _ _ _ _ _ `next_lab_thm] >>
      disch_then(qspecl_then[`F`,`n`,`m'`]mp_tac)>>simp[] >>
      strip_tac >>
      fs[upd_pc_def,ADD1] >> rfs[] >>
      qexists_tac`ck` >>
      TOP_CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,upd_pc_def,dec_clock_def] >>
      qexists_tac`t2` >> simp[] >>
      fs[Abbr`pc`] >>
      CASE_TAC \\ fs[] >>
      CASE_TAC \\ fs[]) >>
    Cases_on`nr2`>>full_simp_tac(srw_ss())[] >- (
      full_simp_tac(srw_ss())[code_installed_def] >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      qmatch_asmsub_rename_tac`if xx then _ else _` >>
      reverse (Cases_on`xx`)>>fs[] >- (
        `IS_SOME r` by metis_tac[no_ret_correct,FST,SND] >>
        full_simp_tac(srw_ss())[IS_SOME_EXISTS] >>
        rpt var_eq_tac >> simp[] >>
        rfs[call_args_def,FILTER_APPEND] >>
        simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
        imp_res_tac code_installed_append_imp >>
        imp_res_tac code_installed_append_imp >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        old_drule (GEN_ALL state_rel_with_pc) >>
        disch_then(qspec_then`t1.pc+1`mp_tac) >>
        strip_tac >> rfs[] >>
        first_x_assum old_drule >> fs[] >>
        disch_then(qspecl_then[`F`,`n`,`m'`]mp_tac)>>simp[] >>
        strip_tac >>
        reverse TOP_CASE_TAC \\ fs[upd_pc_def] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def]
        \\ simp[inc_pc_def,dec_clock_def] \\ rfs[]
        \\ qexists_tac`ck+1`>>simp[] >>
        qexists_tac`t2`>>simp[]) >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      simp[get_pc_value_def] >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      full_simp_tac(srw_ss())[code_installed_def] >>
      fs[FILTER_APPEND] >>
      qmatch_assum_abbrev_tac`code_installed pc (append xs) _` >>
      old_drule state_rel_with_pc >> strip_tac >>
      first_x_assum old_drule >>
      full_simp_tac(srw_ss())[call_args_def] >>
      full_simp_tac(srw_ss())[Q.SPEC`If _ _ _ _ _ `next_lab_thm] >>
      disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
      strip_tac >>
      fs[upd_pc_def,ADD1] >> first_x_assum old_drule >> fs[] >> strip_tac >>
      qexists_tac`ck` >>
      TOP_CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,upd_pc_def,dec_clock_def] >>
      qexists_tac`t2` >> simp[] ) >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    `get_var r1 s = SOME (read_reg r1 t1) ∧
     get_var_imm ri s = SOME (reg_imm ri t1)` by (
      fs[state_rel_def] >>
      Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
    rfs[] >>
    ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
    qmatch_asmsub_rename_tac`if xx then _ else _` >>
    Cases_on`xx`>>fs[] >- (
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      full_simp_tac(srw_ss())[code_installed_def] >>
      qmatch_assum_abbrev_tac`code_installed pc (append xs) _` >>
      old_drule state_rel_with_pc >> strip_tac >> rfs[] >>
      first_x_assum old_drule >>
      full_simp_tac(srw_ss())[call_args_def] >>
      disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
      full_simp_tac(srw_ss())[FILTER_APPEND,ADD1,upd_pc_def] >>
      strip_tac >>
      qexists_tac`ck+1` >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,upd_pc_def,dec_clock_def] >>
      fsrw_tac[ARITH_ss][] >>
      qexists_tac`t2` >> simp[] >>
      TOP_CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,upd_pc_def,dec_clock_def]) >>
    imp_res_tac code_installed_append_imp >>
    imp_res_tac code_installed_append_imp >>
    imp_res_tac code_installed_append_imp >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
    qmatch_assum_abbrev_tac`code_installed pc (append ys) _` >>
    old_drule state_rel_with_pc >> strip_tac >> rfs[] >>
    first_x_assum old_drule >>
    full_simp_tac(srw_ss())[call_args_def] >>
    disch_then(qspecl_then[`F`,`n`,`m'`]mp_tac)>>simp[] >>
    strip_tac >>
    full_simp_tac(srw_ss())[upd_pc_def] >>
    reverse TOP_CASE_TAC \\ fs[] \\ rfs[]
    >- (
      qexists_tac`ck+1`>>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,inc_pc_def,dec_clock_def] ) >>
    reverse TOP_CASE_TAC >> fs[]
    >- (
      qexists_tac`ck+1`>>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,inc_pc_def,dec_clock_def] >>
      qexists_tac`t2` >> simp[] >>
      CASE_TAC \\ fs[]) >>
    qexists_tac`ck+2`>>simp[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    simp[inc_pc_def,dec_clock_def] >>
    first_x_assum(strip_assume_tac o CONV_RULE(HO_REWR_CONV FORALL_NUM)) >>
    fsrw_tac[ARITH_ss][ADD1] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    simp[get_pc_value_def,upd_pc_def,dec_clock_def,inc_pc_def] >>
    simp[Abbr`pc`,FILTER_APPEND] >>
    imp_res_tac asm_fetch_aux_SOME_isPREFIX>>
    fs[]>>
    imp_res_tac loc_to_pc_isPREFIX>>fs[]>>
    qpat_abbrev_tac`pc = LENGTH _ + _` >>
    qexists_tac`upd_pc pc t2`>>simp[upd_pc_def] >>
    fs[Abbr`pc`,FILTER_APPEND]>>
    metis_tac[state_rel_with_pc,upd_pc_def]) >>
  conj_tac >- (
    rename [`While`]
    \\ srw_tac[][stackSemTheory.evaluate_def]
    \\ `flatten t (While cmp r1 ri c1) n l = flatten F (While cmp r1 ri c1) n l`
             by (once_rewrite_tac [flatten_def] \\ fs [])
    \\ fs [] \\ pop_assum kall_tac
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      strip_tac \\ rveq \\ full_simp_tac(srw_ss())[]
      \\ qhdtm_x_assum`code_installed`mp_tac
      \\ simp[Once flatten_def]
      \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
      \\ simp[code_installed_def] \\ strip_tac
      \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ imp_res_tac state_rel_read_reg_FLOOKUP_regs
      \\ imp_res_tac state_rel_get_var_imm
      \\ qpat_x_assum`_ = read_reg _  _`(assume_tac o SYM)
      \\ simp[]
      \\ full_simp_tac(srw_ss())[GSYM word_cmp_word_cmp]
      \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
      \\ simp[get_pc_value_def]
      \\ imp_res_tac code_installed_append_imp
      \\ full_simp_tac(srw_ss())[code_installed_def]
      \\ simp[Once flatten_def]
      \\ simp[FILTER_APPEND]
      \\ qexists_tac`1` \\ simp[]
      \\ (fn g => subterm (fn tm => qexists_tac `^tm with <| clock := t1.clock|>` g) (#2 g)) >> simp[]
      \\ simp[dec_clock_def,upd_pc_def]
      \\ simp[GSYM upd_pc_def]
      \\ match_mp_tac state_rel_with_pc
      \\ simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      strip_tac \\ rveq \\ full_simp_tac(srw_ss())[]
      \\ rev_full_simp_tac(srw_ss())[]
      \\ qhdtm_x_assum`code_installed`mp_tac
      \\ simp[Once flatten_def]
      \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
      \\ simp[code_installed_def]
      \\ strip_tac
      \\ simp[flatten_def,FILTER_APPEND]
      \\ imp_res_tac code_installed_append_imp
      \\ full_simp_tac(srw_ss())[code_installed_def]
      \\ first_x_assum(qspecl_then[`F`,`n`,`l`,`upd_pc (t1.pc +1) t1`]mp_tac)
      \\ full_simp_tac(srw_ss())[call_args_def]
      \\ impl_tac >- metis_tac[state_rel_with_pc]
      \\ strip_tac
      \\ rename1`halt_view r` \\ Cases_on`r` \\ fs[]
      \\ rename1`halt_view (SOME x)` \\ Cases_on`x` \\ fs[]
      \\ TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[])
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ imp_res_tac state_rel_read_reg_FLOOKUP_regs
      \\ pop_assum (assume_tac o SYM)
      \\ imp_res_tac state_rel_get_var_imm
      \\ qexists_tac`ck+1` \\ simp[]
      \\ imp_res_tac asm_fetch_aux_SOME_isPREFIX
      \\ imp_res_tac loc_to_pc_isPREFIX
      \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def]
      \\ imp_res_tac word_cmp_word_cmp \\ full_simp_tac(srw_ss())[]
      \\ fsrw_tac[ARITH_ss][dec_clock_def,inc_pc_def,upd_pc_def]
      \\ qexists_tac`t2` \\ simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      strip_tac \\ rveq \\ full_simp_tac(srw_ss())[]
      \\ qhdtm_x_assum`code_installed`mp_tac
      \\ simp[Once flatten_def]
      \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
      \\ simp[code_installed_def] \\ strip_tac
      \\ imp_res_tac code_installed_append_imp
      \\ full_simp_tac(srw_ss())[code_installed_def]
      \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ imp_res_tac state_rel_read_reg_FLOOKUP_regs
      \\ imp_res_tac state_rel_get_var_imm
      \\ qpat_x_assum`_ = read_reg _  _`(assume_tac o SYM)
      \\ simp[]
      \\ full_simp_tac(srw_ss())[GSYM word_cmp_word_cmp]
      \\ first_x_assum(qspecl_then[`F`,`n`,`l`,`inc_pc t1`]mp_tac)
      \\ simp[] \\ full_simp_tac(srw_ss())[call_args_def]
      \\ impl_tac
      >- ( simp[inc_pc_def,GSYM upd_pc_def] \\ metis_tac[state_rel_with_pc] )
      \\ strip_tac
      \\ fsrw_tac[ARITH_ss][inc_pc_def,dec_clock_def]
      \\ qexists_tac`ck+1`\\simp[]
      \\ qexists_tac`t2` \\ simp[]
      \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[STOP_def]
    \\ qhdtm_x_assum`code_installed`mp_tac
    \\ simp[Once flatten_def]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ simp[code_installed_def] \\ strip_tac
    \\ imp_res_tac code_installed_append_imp
    \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ first_x_assum(qspecl_then[`F`,`n`,`l`,`inc_pc t1`]mp_tac)
    \\ impl_tac
    >- (
      simp[inc_pc_def,GSYM upd_pc_def,state_rel_with_pc]
      \\ full_simp_tac(srw_ss())[call_args_def] )
    \\ strip_tac
    \\ `s.clock ≠ 0`
    by (
      imp_res_tac stackSemTheory.evaluate_clock
      \\ decide_tac )
    \\ `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def]
    \\ `t2.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def]
    \\ first_x_assum(qspecl_then[`F`,`n`,`l`,`dec_clock (upd_pc t1.pc t2)`]mp_tac)
    \\ impl_tac
    >- (
      simp[flatten_def,code_installed_def]
      \\ CONJ_TAC>-
        (match_mp_tac state_rel_dec_clock
        \\ match_mp_tac state_rel_with_pc
        \\ simp[] )>>
      imp_res_tac code_installed_isPREFIX>>
      imp_res_tac loc_to_pc_isPREFIX>>
      imp_res_tac asm_fetch_aux_SOME_isPREFIX>>
      fs[])
    \\ strip_tac
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ imp_res_tac state_rel_read_reg_FLOOKUP_regs
    \\ imp_res_tac state_rel_get_var_imm
    \\ qpat_x_assum`_ = read_reg _  _`(assume_tac o SYM)
    \\ fs[upd_pc_def,dec_clock_def]
    \\ fs[inc_pc_def,GSYM word_cmp_word_cmp,get_pc_value_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- (
      imp_res_tac asm_fetch_aux_SOME_isPREFIX>>
      imp_res_tac loc_to_pc_isPREFIX>>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,inc_pc_def,dec_clock_def]
      \\ qexists_tac`ck+ck'+1` \\ simp[]
      \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,upd_pc_def,dec_clock_def]
      \\ rfs[] )>>
    imp_res_tac asm_fetch_aux_SOME_isPREFIX>>
    imp_res_tac loc_to_pc_isPREFIX
    \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def]
    \\ simp[inc_pc_def,dec_clock_def]
    \\ qexists_tac`ck+ck'+1` \\ simp[]
    \\ qexists_tac`t2'` \\ rw[]
    \\ last_x_assum(qspec_then`ck'+ck1`mp_tac) \\ simp[] \\ strip_tac
    \\ simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def]
    \\ fsrw_tac[ARITH_ss][inc_pc_def,dec_clock_def,upd_pc_def]
    \\ first_x_assum(qspec_then`ck1`mp_tac) \\ simp[]
    \\ metis_tac[IS_PREFIX_TRANS]) >>
  conj_tac >- (
    rename [`JumpLower`] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[Q.SPECL[`b`,`JumpLower _ _ _`]flatten_def] >>
    qhdtm_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    Cases_on`get_var r1 s`>>full_simp_tac(srw_ss())[]>> Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var r2 s`>>full_simp_tac(srw_ss())[]>> Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[code_installed_def] >>
    `get_var r1 s = SOME (read_reg r1 t1) ∧
     get_var r2 s = SOME (read_reg r2 t1)` by (
      full_simp_tac(srw_ss())[state_rel_def,get_var_def] >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
    reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >> simp[] >>
      qexists_tac`1`>>simp[]>>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      full_simp_tac(srw_ss())[GSYM word_cmp_word_cmp] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      qexists_tac`inc_pc t1` >>
      simp[dec_clock_def,inc_pc_def]>>
      full_simp_tac(srw_ss())[state_rel_def] >>
      metis_tac[]) >>
    ntac 2 CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >> simp[empty_env_def] >>
      `t1.clock = 0` by full_simp_tac(srw_ss())[state_rel_def] >>
      qexists_tac`0`>>simp[]>>
      qexists_tac`t1`>>simp[]>>
      full_simp_tac(srw_ss())[state_rel_def] ) >>
    ntac 2 CASE_TAC >> full_simp_tac(srw_ss())[]>>
    srw_tac[][] >> simp[] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[find_code_def] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    imp_res_tac state_rel_dec_clock >>
    old_drule state_rel_with_pc >>
    pop_assum kall_tac >> strip_tac >>
    first_x_assum old_drule >> full_simp_tac(srw_ss())[] >>
    disch_then old_drule >> simp[] >>
    strip_tac >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    full_simp_tac(srw_ss())[GSYM word_cmp_word_cmp,get_pc_value_def] >>
    `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def] >> simp[] >>
    full_simp_tac(srw_ss())[dec_clock_def,upd_pc_def] >>
    qexists_tac`ck`>>
    fsrw_tac[ARITH_ss][] >>
    qexists_tac`t2` >>
    simp[] ) >>
  conj_tac >- (
    rename [`RawCall`] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[Q.SPECL[`b`,`RawCall _`]flatten_def] >>
    qhdtm_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    simp [CaseEq"option"] >> strip_tac >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    imp_res_tac state_rel_dec_clock >>
    old_drule state_rel_with_pc >>
    pop_assum kall_tac >> strip_tac >>
    first_x_assum old_drule >> full_simp_tac(srw_ss())[pair_case_eq] >>
    Cases_on `s.clock = 0` THEN1
     (fs [] \\ rveq \\ fs []
      \\ qexists_tac `0` \\ fs []
      \\ qexists_tac `t1` \\ fs []
      \\ fs [state_rel_def]) >>
    fs [pair_case_eq,CaseEq"option"] >>
    rveq \\ fs [] >>
    Cases_on `prog` \\ fs [dest_Seq_def] \\ rveq \\ fs [call_args_def] >>
    fs [Q.SPECL [`T`,`Seq p1 p2`]flatten_def] >>
    rpt (pairarg_tac \\ fs []) >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] >>
    drule code_installed_append_imp >>
    simp [code_installed_def] >>
    rename [`flatten F body dest m7 = _`] >>
    `append ys = append (FST (flatten F body dest m7))` by fs [] >>
    pop_assum (fn th => once_rewrite_tac [th]) >>
    strip_tac >>
    imp_res_tac state_rel_dec_clock >>
    rename [`loc_to_pc dest 1 t1.code = SOME pc1`] >>
    drule state_rel_with_pc >>
    disch_then (qspec_then `pc1` assume_tac) >>
    disch_then drule >>
    fs [upd_pc_def,dec_clock_def] >>
    disch_then drule >>
    strip_tac >>
    `t1.clock <> 0` by fs [state_rel_def] >>
    fs [] >>
    qexists_tac `ck` \\ fs [] >>
    reverse TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    fs [code_installed_def,labSemTheory.get_pc_value_def] >>
    fs [upd_pc_def,dec_clock_def] >>
    qexists_tac `t2` >> fs [] ) >>
  conj_tac >- (
    rename [`Call`] >>
    srw_tac[][] >>
    qhdtm_x_assum`code_installed`mp_tac >>
    simp[Once flatten_def] >> strip_tac >>
    qhdtm_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    BasicProvers.TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>-(
      reverse (Cases_on `handler`)
      THEN1 (fs [] \\ BasicProvers.TOP_CASE_TAC \\ fs []) >>
      fs [] >>
      BasicProvers.TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
        srw_tac[][] >> simp[] >>
        map_every qexists_tac[`0`,`t1`] >>
        full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[state_rel_def,empty_env_def] ) >>
      `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> simp[] >> full_simp_tac(srw_ss())[] >>
      imp_res_tac state_rel_dec_clock >>
      Cases_on`dest`>>full_simp_tac(srw_ss())[find_code_def,compile_jump_def,code_installed_def] >- (
        first_assum(fn th => first_assum(
          tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
        old_drule state_rel_with_pc >>
        qhdtm_x_assum`state_rel`kall_tac >>
        strip_tac >>
        first_x_assum old_drule >>
        simp[] >>
        disch_then old_drule >> simp[] >>
        strip_tac >> full_simp_tac(srw_ss())[] >>
        `t1.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
        CASE_TAC >> full_simp_tac(srw_ss())[] >>
        TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
        full_simp_tac(srw_ss())[dec_clock_def,upd_pc_def] >>
        map_every qexists_tac[`ck`,`t2`]>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
      qpat_x_assum`_ = SOME _`mp_tac >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      strip_tac >>
      first_assum(fn th => first_assum(
        tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
      old_drule state_rel_with_pc >>
      qhdtm_x_assum`state_rel`kall_tac >>
      strip_tac >>
      first_x_assum old_drule >>
      simp[] >>
      disch_then old_drule >> simp[] >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_rename_tac`FLOOKUP s.regs r = SOME _` >>
      `read_reg r t1 = Loc n 0` by (
        full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] ) >>
      `t1.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] >>
      TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
      full_simp_tac(srw_ss())[dec_clock_def,upd_pc_def] >>
      map_every qexists_tac[`ck`,`t2`]>>full_simp_tac(srw_ss())[] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
    split_pair_case_tac >>
    var_eq_tac >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >> srw_tac[][] >>
      map_every qexists_tac[`0`,`t1`] >>
      full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[state_rel_def,empty_env_def] ) >>
    `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def] >>
    split_pair_case_tac >>
    simp[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    pairarg_tac >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    strip_tac >>
    qpat_x_assum`code_installed _.pc _ _`mp_tac >>
    qpat_abbrev_tac`prefix = misc$List _` >>
    strip_tac >>
    `code_installed t1.pc (append prefix) t1.code`
    by (
      Cases_on`handler` \\ fs[] >>
      imp_res_tac code_installed_append_imp >> fs[] >>
      pop_assum mp_tac >>
      BasicProvers.TOP_CASE_TAC >>
      BasicProvers.TOP_CASE_TAC >>
      simp[UNCURRY] >> strip_tac >>
      imp_res_tac code_installed_append_imp >> fs[] >>
      imp_res_tac code_installed_append_imp >> fs[]) >>
    full_simp_tac(srw_ss())[call_args_def] >> var_eq_tac >>
    imp_res_tac find_code_lookup >>
    `dest_to_loc (s.regs \\ t1.link_reg) dest = dest_to_loc' t1.regs dest` by (
      fs [dest_to_loc_def,dest_to_loc'_def] >>
      TOP_CASE_TAC >>
      fs [find_code_def,option_case_eq,CaseEq"word_loc",num_case_eq] >>
      rveq >> fs [DOMSUB_FAPPLY_THM,FLOOKUP_DEF] >>
      qhdtm_x_assum`state_rel`mp_tac >>
      simp[state_rel_def,FLOOKUP_DEF]) >>
    full_simp_tac(srw_ss())[] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    fs[Abbr`prefix`,code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def,lab_to_loc_def,get_pc_value_def] >>
    simp[inc_pc_def,dec_clock_def,upd_reg_def] >>
    qpat_abbrev_tac`regs = _ t1.regs` >>
    `loc_to_pc (dest_to_loc' regs dest) 0 t1.code = SOME pc` by (
      ntac 2 (last_x_assum(qspec_then`ARB`kall_tac))>>
      qpat_x_assum`_ ⇒ ∀x. _`kall_tac >>
      qhdtm_x_assum`loc_to_pc`mp_tac >>
      simp[dest_to_loc'_def] >>
      CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] ) >>
    old_drule(GEN_ALL compile_jump_correct) >>
    disch_then old_drule >>
    strip_tac >>
    qmatch_assum_abbrev_tac`code_installed pc (append (FST (flatten T _ nx lx))) _` >>
    last_x_assum(qspecl_then[`T`,`nx`,`lx`,`t1 with <| pc := pc; regs := regs; clock := s.clock-1 |>`]mp_tac) >>
    impl_tac >- (
      simp[] >>
      conj_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
      ntac 2 (last_x_assum(qspec_then`ARB`kall_tac)) >>
      qpat_x_assum`_ ⇒ ∀x. _`kall_tac >>
      full_simp_tac(srw_ss())[state_rel_def,stackSemTheory.dec_clock_def,set_var_def,FLOOKUP_UPDATE] >>
      simp[Abbr`regs`,APPLY_UPDATE_THM,lab_to_loc_def] >> srw_tac[][] >>
      metis_tac[] ) >>
    strip_tac >>
    `t1.clock = s.clock` by metis_tac[state_rel_def] >>
    Cases_on`r`>>full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`t1 with <| regs := regs; pc := t1.pc+1; clock := ck + (ck1+t1.clock)|>`
        (mp_tac o Q.GENL[`ck`,`ck1`])) >> simp[] >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (
        ntac 2 (last_x_assum(qspec_then`ARB`kall_tac))>>
        qpat_x_assum`_ ⇒ ∀x. _`kall_tac >>
        qpat_x_assum`_ _ _ _`kall_tac >>
        qpat_x_assum`_ = (_,_)`kall_tac >>
        rpt strip_tac >> full_simp_tac(srw_ss())[] >>
        simp[Abbr`regs`,APPLY_UPDATE_THM] >>
        full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
        full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> full_simp_tac(srw_ss())[]) >>
      strip_tac >>
      CONV_TAC(HO_REWR_CONV EXISTS_NUM) >> disj2_tac >>
      simp[ADD1] >> pop_assum kall_tac >>
      simp[dec_clock_def,upd_pc_def] >>
      rename1`halt_view (SOME z)` \\ Cases_on`z` \\ fs[] >>
      rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[]
      >- (
        qpat_x_assum`_ = (_,_)`mp_tac >>
        IF_CASES_TAC >> simp[] >> strip_tac >>
        qpat_x_assum`¬ _`mp_tac >> simp_tac bool_ss [] >> strip_tac >> rveq >>
        rev_full_simp_tac(srw_ss())[] >>
        first_x_assum old_drule >>
        simp[] >> full_simp_tac(srw_ss())[] >>
        imp_res_tac loc_to_pc_isPREFIX>>fs[]>>
        imp_res_tac code_installed_isPREFIX>>fs[]>>
        disch_then old_drule >> simp[] >>
        disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
        impl_tac >- (
          fs[code_installed_def]
          \\ every_case_tac \\ fs[UNCURRY,code_installed_def]
          \\ imp_res_tac code_installed_append_imp \\ fs[]
          \\ imp_res_tac code_installed_append_imp \\ fs[]
          \\ rfs[] ) >>
        strip_tac >>
        Cases_on`handler`>>full_simp_tac(srw_ss())[]>-(
          qexists_tac`ck+ck'` >>
          qexists_tac`t2'` >>
          conj_tac >- (
            fs [get_pc_value_def] >>
            gen_tac >>
            first_x_assum(qspec_then`ck1`mp_tac) >>
            first_x_assum(qspec_then`ck'+ck1`mp_tac) >>
            first_x_assum(qspec_then`ck'+ck1`mp_tac) >>
            simp[] ) >>
          simp[] >>
          simp[Once flatten_def,ADD1]>>
          metis_tac[IS_PREFIX_TRANS] ) >>
        qexists_tac`ck+ck'+1` >>
        every_case_tac >> fs[] >> fs[] >>
        pairarg_tac >> fs[] >>
        simp[Once flatten_def] >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        imp_res_tac code_installed_append_imp >>
        full_simp_tac(srw_ss())[code_installed_def] >>
        simp[ADD1,FILTER_APPEND] >>
        qpat_abbrev_tac`pc3 = LENGTH _ + _` >>
        qexists_tac`t2' with pc := pc3` >> simp[] >>
        conj_tac >- (
          fs [get_pc_value_def]>>
          gen_tac >>
          first_x_assum(qspec_then`ck1+1`mp_tac) >>
          first_x_assum(qspec_then`ck1+ck'+1`mp_tac) >>
          first_x_assum(qspec_then`ck1+ck'+1`mp_tac) >>
          simp[] >> srw_tac[][] >>
          fsrw_tac[ARITH_ss][] >>
          imp_res_tac asm_fetch_aux_SOME_isPREFIX>>
          imp_res_tac loc_to_pc_isPREFIX>>
          simp[Once labSemTheory.evaluate_def,asm_fetch_def] >> rfs[] >>
          simp[get_pc_value_def,upd_pc_def,dec_clock_def,Abbr`pc3`] >>
          qpat_x_assum`_ = t2.pc`(assume_tac o SYM) >> simp[] >>
          imp_res_tac code_installed_append_imp >>
          full_simp_tac(srw_ss())[code_installed_def] >>
          imp_res_tac loc_to_pc_isPREFIX>>
          simp[]) >>
        imp_res_tac state_rel_with_pc >>
        full_simp_tac(srw_ss())[upd_pc_def]>>
        metis_tac[IS_PREFIX_TRANS] ) >>
      Cases_on`handler` \\ fs[] >>
      split_pair_case_tac \\ fs[] >>
      pairarg_tac \\ fs[] >> rw[] >>
      rev_full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][code_installed_def] >>
      imp_res_tac code_installed_append_imp >>
      fsrw_tac[ARITH_ss][code_installed_def] >>
      imp_res_tac code_installed_append_imp >>
      fsrw_tac[ARITH_ss][code_installed_def] >>
      rw[] \\ fs[] >>
      qpat_x_assum`_ = (NONE,_)`mp_tac >>
      IF_CASES_TAC >> simp[] >> strip_tac >>
      fs[] >> rveq >>
      imp_res_tac loc_to_pc_isPREFIX>>fs[]>>
      qpat_x_assum`_ = t2.pc`(assume_tac o SYM) >>
      first_x_assum old_drule >> simp[] >>
      disch_then(qspecl_then[`F`,`n`,`m'`]mp_tac)>>simp[] >>
      imp_res_tac code_installed_isPREFIX>>
      fs[]>>
      strip_tac >>
      simp[Once flatten_def] >>
      simp[FILTER_APPEND,ADD1] >>
      map_every qexists_tac[`ck+ck'`,`t2'`] >>
      simp[] >>
      rw[]
      >-
        (first_x_assum(qspec_then`ck1`mp_tac) >>
         qpat_x_assum`∀x. evaluate _ = _`(qspec_then`ck1+ck'`mp_tac) >>
        simp[])
      >>
        metis_tac[IS_PREFIX_TRANS])>>
    qmatch_asmsub_rename_tac`halt_view (SOME z)` \\ Cases_on`z` \\ fs[] >>
    rveq >> fs[]
    >- (
      rename1`result_view (Result w)` \\ Cases_on`w` \\ rfs[] >>
      qpat_x_assum`_ = (SOME _ ,_)`mp_tac >>
      IF_CASES_TAC >> simp[] >> strip_tac >> fs[] >> rveq >> rfs[] >>
      imp_res_tac loc_to_pc_isPREFIX>>fs[]>>
      imp_res_tac code_installed_isPREFIX>>fs[]>>
      first_x_assum old_drule >> simp[] >>
      disch_then(qspecl_then[`F`,`n`,`l`]mp_tac)>>simp[] >>
      qpat_x_assum`_ = t2.pc`(assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
      impl_tac >- (
        Cases_on`handler` >> fs[] >>
        every_case_tac >> fs[code_installed_def] >>
        pairarg_tac >> fs[code_installed_def] >>
        imp_res_tac code_installed_append_imp >> fs[] ) >>
      strip_tac >>
      finish_tac
      )
    >- (
      rename1`SOME (Exception w)` >> Cases_on`w` \\ fs[] >>
      qpat_x_assum`_ = (SOME _ ,_)`mp_tac >>
      TOP_CASE_TAC >>
      ((strip_tac >> var_eq_tac >> rveq >> full_simp_tac(srw_ss())[] >>
        every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
        rev_full_simp_tac(srw_ss())[] >>
        qexists_tac`ck+1`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        gen_tac >>
        qpat_abbrev_tac`ss:('a,'c,'ffi)labSem$state = _ _` >>
        first_x_assum(qspec_then`ss`mp_tac) >>
        impl_tac >- (
          simp[Abbr`ss`] >>
          srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
          full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
          full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
          full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
          every_case_tac >> full_simp_tac(srw_ss())[]) >>
        simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
        first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
        first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
        first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
        NO_TAC) ORELSE
       (ntac 2 TOP_CASE_TAC >>
        IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> strip_tac >> rveq)) >>
      pairarg_tac >> full_simp_tac(srw_ss())[] >>
      fs[code_installed_def] >>
      imp_res_tac code_installed_append_imp >>
      pop_assum mp_tac >>
      simp_tac(srw_ss()++ARITH_ss)[code_installed_def] >>
      strip_tac >>
      qpat_x_assum`∀x. (loc_to_pc _ _ _ = _) ⇒ _`mp_tac >>
      simp[] >> strip_tac >> rev_full_simp_tac(srw_ss())[] >>
      imp_res_tac loc_to_pc_isPREFIX \\ fs[] \\
      first_x_assum old_drule >>
      disch_then(qspecl_then[`F`,`n`,`m'`]mp_tac)>>simp[] >>
      impl_tac >- (
        qpat_x_assum`_ = t2.pc`(assume_tac o SYM) >>
        imp_res_tac code_installed_append_imp >>
        metis_tac[code_installed_isPREFIX]) >>
      strip_tac >>
      finish_tac) >>
    TRY (
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,
           inc_pc_def,dec_clock_def,lab_to_loc_def,upd_reg_def] >>
      qexists_tac`ck+1` >> simp[] >>
      qmatch_goalsub_abbrev_tac`labSem$evaluate ss` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      impl_tac >- (
        simp[Abbr`ss`] >>
        fs[lab_to_loc_def,get_pc_value_def] >>
        srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
        full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
        full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> full_simp_tac(srw_ss())[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
      NO_TAC) >>
    TRY (
      qexists_tac`ck+1`>>simp[] >>
      qexists_tac`t2`>>simp[] >>
      gen_tac >>
      qmatch_goalsub_abbrev_tac`labSem$evaluate ss` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      impl_tac >- (
        simp[Abbr`ss`] >>
        fs[lab_to_loc_def,get_pc_value_def] >>
        srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
        full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
        full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> full_simp_tac(srw_ss())[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
      NO_TAC)) >>
  conj_tac >- (
    rename [`Install`] >>
    rw[stackSemTheory.evaluate_def]>>
    fs[case_eq_thms]>>
    pairarg_tac>>fs[]>>
    fs[get_var_def]>>
    imp_res_tac state_rel_read_reg_FLOOKUP_regs>>
    fs[case_eq_thms]>>
    rw[]>> rfs[]>>
    qpat_x_assum`code_installed _ _ _` mp_tac>>
    simp[Once flatten_def]>> strip_tac>>
    fs[code_installed_def]>>
    qpat_x_assum`state_rel s _` mp_tac>>
    simp[Once state_rel_def]>>
    strip_tac>>fs[prog_to_section_def]>>
    pairarg_tac>>fs[]>>
    qmatch_asmsub_abbrev_tac`t1.compile cfg new_code`>>
    rw[]>>qexists_tac`2`>>
    simp[Once labSemTheory.evaluate_def]>>
    simp[asm_fetch_def]>>
    fs[call_args_def]>>rw[]>>fs[]>>simp[]>>
    fs[get_pc_value_def,lab_to_loc_def]>>
    simp[inc_pc_def,dec_clock_def,upd_reg_def]>>
    (* Do the install *)
    simp[Once labSemTheory.evaluate_def]>>
    simp[asm_fetch_def]>>
    simp[APPLY_UPDATE_THM]>>
    qpat_x_assum`Word _ = _` (assume_tac o SYM)>>
    qpat_x_assum`Word _ = _` (assume_tac o SYM)>>
    fs[prog_to_section_def,shift_seq_def]>>
    pairarg_tac>>fs[]>>
    qabbrev_tac `tt = t1 with
        <|regs :=
            (t1.ptr_reg =+ Loc k 0)
              (λa.
                 get_reg_value (t1.cc_regs 0 a)
                   (if t1.link_reg = a then Loc n l
                    else read_reg a t1) Word); pc := t1.pc+2;
          cc_regs := shift_seq 1 t1.cc_regs;
          code := t1.code ++ new_code;
          compile_oracle := shift_seq 1 t1.compile_oracle;
          code_buffer := cb;
          clock:=t1.clock|>`>>
    qexists_tac`tt` >>
    fs[Abbr`tt`]>>
    CONJ_TAC>-
      (rw[]>>fs[shift_seq_def,Abbr`new_code`])>>
    CONJ_TAC>-
      simp[append_def,append_aux_def,flatten_def]>>
    fs[state_rel_def]>>
    qmatch_goalsub_abbrev_tac`fromAList ls`>>
    `new_code = MAP prog_to_section ls` by
      (unabbrev_all_tac>>fs[prog_to_section_def])>>
    `labels_ok new_code` by
      (first_x_assum(qspec_then`0` assume_tac)>>
      rfs[]>>
      match_mp_tac prog_to_section_labels_ok>>
      fs[EVERY_MEM,FORALL_PROD]>>
      metis_tac[])>>
    old_drule labels_ok_imp>>
    simp[]>>
    rw[]
    >-
      (fs[APPLY_UPDATE_THM,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE,call_args_def]>>
      pop_assum mp_tac>>
      IF_CASES_TAC>-
        simp[]>>
      IF_CASES_TAC>-
        (simp[get_reg_value_def]>>
        rw[]>>fs[])>>
      simp[])
    >-
      (fs[lookup_union,case_eq_thms]
      >-
        (qmatch_asmsub_abbrev_tac`fromAList pp`>>
        fs[lookup_fromAList]>>
        imp_res_tac ALOOKUP_MEM>>
        first_x_assum(qspec_then`0` assume_tac)>>
        rfs[EVERY_MEM,FORALL_PROD]>>
        metis_tac[])
      >>
        metis_tac[])
    >-
      (pop_assum mp_tac>>simp[lookup_union]>>
      reverse TOP_CASE_TAC>> strip_tac
      >-
        (first_x_assum old_drule>>rw[]>>
        metis_tac[loc_to_pc_APPEND,code_installed_APPEND])
      >>
        fs[lookup_fromAList]>>
        old_drule code_installed_prog_to_section >>
        disch_then old_drule>>strip_tac>>
        `~MEM n' (MAP Section_num t1.code)` by
           (unabbrev_all_tac>>fs[EXTENSION,domain_lookup]>>
           simp[MAP_prog_to_section_Section_num]>>
           metis_tac[option_CLAUSES])>>
        old_drule loc_to_pc_append2>>simp[]>>
        disch_then old_drule>>
        simp[]>> strip_tac>>
        old_drule code_installed_append2>> simp[]>>
        rewrite_tac[Once CONJ_COMM]>>
        disch_then old_drule>>
        simp[]>>
        disch_then match_mp_tac>>
        imp_res_tac ALOOKUP_MEM>>
        fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,FORALL_PROD,prog_to_section_def,PULL_EXISTS]>>
        rpt (first_x_assum old_drule)>>
        pairarg_tac>>fs[EVERY_MEM])
    >-
      (fs[domain_union]>>AP_TERM_TAC>>
      rfs[MAP_prog_to_section_Section_num]>>
      fs[domain_fromAList])
    >-
      fs[shift_seq_def]
    >>
      (fs[shift_seq_def]>>pairarg_tac>>fs[]>>
      first_x_assum(qspec_then`k'+1` assume_tac)>>rfs[]>>
      fs[GSYM ADD1,GENLIST_CONS]>>
      rfs[MAP_prog_to_section_Section_num]>>
      fs[o_DEF]))>>
  conj_tac >- (
    rename [`ShMemOp`] >>rpt gen_tac>>strip_tac>>
    ‘∀w:'a word. TAKE 1 (word_to_bytes w F) = [get_byte 0w w F]’
      by(fs[state_rel_def,good_dimindex_def,word_to_bytes_def,
            CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV word_to_bytes_aux_def]) >>
    Cases_on ‘op’>>
    fs[stackSemTheory.evaluate_def,flatten_def]>>
    fs[word_exp_def,IS_SOME_EXISTS,wordLangTheory.word_op_def]>>
    gs[case_eq_thms]>>
    rveq>>fs[]>>
    gs[sh_mem_op_def,sh_mem_store_def,sh_mem_load_def,
       sh_mem_store_byte_def,sh_mem_load_byte_def,
       sh_mem_store32_def,sh_mem_load32_def]>>
    imp_res_tac state_rel_read_reg_FLOOKUP_regs>>
    pop_assum (assume_tac o GSYM)>>
    gs[case_eq_thms]>>rveq>>fs[]
    >>~- ([‘Halt (FFI_outcome _)’],
          fs[code_installed_def,call_args_def] >>
          simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
          gs[share_mem_op_def,share_mem_load_def,
             share_mem_store_def,addr_def]>>
          TRY (qpat_x_assum ‘get_var r _ = _’ assume_tac>>
               fs[stackSemTheory.dec_clock_def,stackSemTheory.get_var_def]>>
               drule_then drule state_rel_read_reg_FLOOKUP_regs>>strip_tac>>
               pop_assum $ assume_tac o GSYM>> fs[])>>
          rpt (CASE_TAC>>fs[])>>
          fs[state_rel_def,dec_clock_def,inc_pc_def]>>
          gs[])>>
    TRY (qexists_tac ‘0’>>qexists_tac ‘t1’>>fs[state_rel_def]>>NO_TAC)>>
    qpat_x_assum ‘call_args (ShMemOp _ _ _) _ _ _ _ _’ mp_tac
    >>~- ([‘call_args (ShMemOp Load _ _) _ _ _ _ _’],
         strip_tac>>
         qexists_tac`0`>>
                    qexists_tac ‘dec_clock t1
                    with <| regs := t1.regs⦇r ↦ Word (word_of_bytes F 0w new_bytes)⦈;
                            io_regs := shift_seq 1 t1.io_regs;
                            pc:=t1.pc+1; ffi := new_ffi|>’ >>
         simp[]>>
         fs[code_installed_def,call_args_def] >>
         simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
         gs[share_mem_op_def,share_mem_load_def,share_mem_store_def,addr_def]>>
         fs[state_rel_def,stackSemTheory.dec_clock_def,dec_clock_def,inc_pc_def]>>
         gs[]>>
         fs[code_installed_def,call_args_def,shift_seq_def] >>
         fs[FLOOKUP_UPDATE]>>
         conj_tac >> rpt strip_tac>-
          (FULL_CASE_TAC>>gs[APPLY_UPDATE_THM])>>
         metis_tac[])
    >>~- ([‘call_args (ShMemOp Load8 _ _) _ _ _ _ _’],
         strip_tac>>
         qexists_tac`0`>>
                    qexists_tac ‘dec_clock t1
                    with <| regs := t1.regs⦇r ↦ Word (word_of_bytes F 0w new_bytes)⦈;
                            io_regs := shift_seq 1 t1.io_regs;
                            pc:=t1.pc+1; ffi := new_ffi|>’ >>
         simp[]>>
         fs[code_installed_def,call_args_def] >>
         simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
         gs[share_mem_op_def,share_mem_load_def,share_mem_store_def,addr_def]>>
         fs[state_rel_def,stackSemTheory.dec_clock_def,dec_clock_def,inc_pc_def]>>
         gs[]>>
         fs[code_installed_def,call_args_def,shift_seq_def] >>
         fs[FLOOKUP_UPDATE]>>
         conj_tac >> rpt strip_tac>-
          (FULL_CASE_TAC>>gs[APPLY_UPDATE_THM])>>
         metis_tac[])
    >>~- ([‘call_args (ShMemOp Load32 _ _) _ _ _ _ _’],
         strip_tac>>
         qexists_tac`0`>>
                    qexists_tac ‘dec_clock t1
                    with <| regs := t1.regs⦇r ↦ Word (word_of_bytes F 0w new_bytes)⦈;
                            io_regs := shift_seq 1 t1.io_regs;
                            pc:=t1.pc+1; ffi := new_ffi|>’ >>
         simp[]>>
         fs[code_installed_def,call_args_def] >>
         simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
         gs[share_mem_op_def,share_mem_load_def,share_mem_store_def,addr_def]>>
         fs[state_rel_def,stackSemTheory.dec_clock_def,dec_clock_def,inc_pc_def]>>
         gs[]>>
         fs[code_installed_def,call_args_def,shift_seq_def] >>
         fs[FLOOKUP_UPDATE]>>
         conj_tac >> rpt strip_tac>-
          (FULL_CASE_TAC>>gs[APPLY_UPDATE_THM])>>
         metis_tac[])>>
    (* Store *)
    strip_tac>>
    qexists_tac`0` >>
    qexists_tac`dec_clock t1 with <| io_regs := shift_seq 1 t1.io_regs;
                           pc:=t1.pc+1; ffi := new_ffi|>` >>
    fs[state_rel_def,stackSemTheory.dec_clock_def,dec_clock_def,inc_pc_def]>>
    fs[code_installed_def,call_args_def] >>
    gs[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    gs[share_mem_op_def,share_mem_load_def,share_mem_store_def,addr_def]>>
    gs[get_var_def]>>
    last_assum $ qspecl_then [‘a’,‘Word x’] assume_tac>>
    last_assum $ qspecl_then [‘r’,‘Word w'’] assume_tac>>
    res_tac>>fs[]>>
    fs[dec_clock_def,shift_seq_def,inc_pc_def]>>metis_tac[])>>
  conj_tac >- (
    rename [`CodeBufferWrite`] >>
    rw[stackSemTheory.evaluate_def,flatten_def]>>
    fs[case_eq_thms]>>
    rw[]>>
    qexists_tac`1`>>qexists_tac`t1 with <|code_buffer := new_cb;pc:=t1.pc+1|>`>>
    fs[code_installed_def,call_args_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    fs[get_var_def]>>
    imp_res_tac state_rel_read_reg_FLOOKUP_regs>>
    ntac 2 (pop_assum (mp_tac o SYM))>>
    ntac 2 strip_tac>>simp[]>>
    fs[state_rel_def,dec_clock_def,inc_pc_def]>>
    metis_tac[])>>
  conj_tac >- (
    rename [`DataBufferWrite`] >>
    rw[stackSemTheory.evaluate_def]>>fs[state_rel_def]
  )>>
  conj_tac >- (
    rename [`FFI`] >>
    srw_tac[][stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var len s`>>full_simp_tac(srw_ss())[]>>Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var ptr s`>>full_simp_tac(srw_ss())[]>>Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var len2 s`>>full_simp_tac(srw_ss())[]>>Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var ptr2 s`>>full_simp_tac(srw_ss())[]>>Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    last_x_assum mp_tac >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
    srw_tac[][] >> simp[] >>
    full_simp_tac(srw_ss())[code_installed_def,call_args_def] >>
    reverse(Cases_on `call_FFI s.ffi (ExtCall ffi_index) x' x`)
    >- (fs[] >> rveq >> fs[halt_view_def] >>
        qexists_tac `2` >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        rpt var_eq_tac >>
        simp[lab_to_loc_def,get_pc_value_def] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def,upd_reg_def,dec_clock_def,inc_pc_def,APPLY_UPDATE_THM] >>
    simp[lab_to_loc_def,get_pc_value_def] >>
        IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
        IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
        IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
        IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
        `get_var t1.ptr_reg s = SOME (read_reg t1.ptr_reg t1) ∧
         get_var t1.len_reg s = SOME (read_reg t1.len_reg t1) ∧
         get_var t1.ptr2_reg s = SOME (read_reg t1.ptr2_reg t1) ∧
         get_var t1.len2_reg s = SOME (read_reg t1.len2_reg t1)` by (
          full_simp_tac(srw_ss())[state_rel_def,get_var_def] >> res_tac >> full_simp_tac(srw_ss())[] ) >>
        full_simp_tac(srw_ss())[] >>
        `s.memory = t1.mem ∧ s.mdomain = t1.mem_domain ∧ s.be = t1.be` by full_simp_tac(srw_ss())[state_rel_def] >>
        full_simp_tac(srw_ss())[] >>
        `t1.ffi = s.ffi` by(fs[state_rel_def]) >>
        fs[]) >>
    fs[] >> rveq >> fs[] >>
    qexists_tac `2` >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    rpt var_eq_tac >>
    simp[lab_to_loc_def,get_pc_value_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def,upd_reg_def,dec_clock_def,inc_pc_def,APPLY_UPDATE_THM] >>
    simp[lab_to_loc_def,get_pc_value_def] >>
    IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
    IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
    IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
    IF_CASES_TAC >- full_simp_tac(srw_ss())[state_rel_def] >>
    `get_var t1.ptr_reg s = SOME (read_reg t1.ptr_reg t1) ∧
     get_var t1.len_reg s = SOME (read_reg t1.len_reg t1) ∧
     get_var t1.ptr2_reg s = SOME (read_reg t1.ptr2_reg t1) ∧
     get_var t1.len2_reg s = SOME (read_reg t1.len2_reg t1)` by (
      full_simp_tac(srw_ss())[state_rel_def,get_var_def] >> res_tac >> full_simp_tac(srw_ss())[] ) >>
    full_simp_tac(srw_ss())[] >>
    `s.memory = t1.mem ∧ s.mdomain = t1.mem_domain ∧ s.be = t1.be` by full_simp_tac(srw_ss())[state_rel_def] >>
    full_simp_tac(srw_ss())[] >>
    `t1.ffi = s.ffi` by(fs[state_rel_def]) >>
    fs[] >>
    (fn g => subterm (fn tm => qexists_tac `^tm with <| clock := t1.clock|>` g) (#2 g)) >> simp[] >>
    full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DRESTRICT] >> rev_full_simp_tac(srw_ss())[] >>
    simp[] >>
    reverse conj_tac
    >- (full_simp_tac(srw_ss())[shift_seq_def] >>
        srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[]) >>
    rpt strip_tac >>
    qmatch_assum_rename_tac `FLOOKUP s.regs k = SOME v` >>
    res_tac >>
    Cases_on `t1.io_regs 0 (ExtCall ffi_index) k` >> full_simp_tac(srw_ss())[get_reg_value_def] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[]) >>
  conj_tac >-
   (rename [`LocValue`]
    \\ srw_tac[][stackSemTheory.evaluate_def]
    \\ full_simp_tac(srw_ss())[flatten_def,code_installed_def]
    \\ simp [Once evaluate_def] \\ qexists_tac `1`
    \\ full_simp_tac(srw_ss())[asm_fetch_def,lab_to_loc_def]
    \\ fs [get_pc_value_def]
    \\ CASE_TAC
    THEN1 (imp_res_tac loc_check_IMP_loc_to_pc \\ fs [])
    \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,upd_reg_def]
    \\ (fn g => subterm (fn tm =>
         qexists_tac `^tm with <| clock := t1.clock|>` g) (#2 g))
    \\ fs[state_rel_def,set_var_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM]
    \\ srw_tac[][] \\ res_tac \\ fs []) >>
  srw_tac[][stackSemTheory.evaluate_def] >>
  full_simp_tac(srw_ss())[state_rel_def]
QED

Theorem flatten_call_correct:
   evaluate (Call NONE (INL start) NONE,s1) = (res,s2) ∧
   state_rel (s1:(α,'c,'ffi)stackSem$state) t1 ∧
   loc_to_pc start 0 t1.code = SOME t1.pc ∧
   res ≠ SOME Error ∧
   (res ≠ SOME TimeOut ⇒
     (∃w. res = SOME(Halt (Word w))) ∨
     (∃f. res = SOME(FinalFFI f)) ∨
     (∃n. res = SOME(Result(Loc n 0)) ∧
       (∀s:(α,'c,'ffi)stackSem$state. subspt s1.code s.code ∧ s.clock ≠ 0 ⇒
           ∃t. evaluate (Call NONE (INL n) NONE,s) = (SOME (Halt (Word 0w)),t) ∧
               t.ffi = s.ffi ∧ t.clock = s.clock - 1)))
   ⇒
   ∃ck r2 t2.
     evaluate ((t1:('a,'c,'ffi)labSem$state)with clock := t1.clock - 1 + ck) = (r2,t2) ∧
     (∀f. res = SOME (FinalFFI f) ⇒ r2 = Halt(FFI_outcome f)) ∧
     (∀w. res = SOME (Halt w) ⇒ r2 =
      (case w of | Word 0w => Halt Success
                 | Word _ => Halt Resource_limit_hit
                 | _ => Error)) ∧
     (∀n. res = SOME(Result(Loc n 0)) ⇒ r2 = Halt Success) ∧
        (*
        (evaluate (t1 with clock := t1.clock - 1 + ck) =
           (,t2)) ∧
           *)
     t2.ffi = s2.ffi ∧
     r2 ≠ Error ∧ (res = SOME TimeOut ⇒ r2 = TimeOut)
     (* (FST (evaluate (t1 with clock := t1.clock - 1 + ck)) ≠ Error)*)
Proof
  srw_tac[][stackSemTheory.evaluate_def] >>
  last_x_assum mp_tac >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >- (
    srw_tac[][] >> qexists_tac`0`>>simp[] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    simp[Once labSemTheory.evaluate_def] ) >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[find_code_def] >>
  first_assum(fn th => first_assum(
    tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
  full_simp_tac(srw_ss())[] >> rveq >>
  old_drule flatten_correct >> simp[] >>
  imp_res_tac state_rel_dec_clock >>
  disch_then old_drule >> simp[] >>
  disch_then old_drule >> simp[] >>
  simp[dec_clock_def] >>
  `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def] >>
  rename1`halt_view (SOME z)` \\ Cases_on`z` \\ fs[] >>
  fsrw_tac[ARITH_ss][] >> strip_tac >>
  TRY ( qexists_tac`ck`>>rw[]>>NO_TAC ) >> rw[] >>
  TRY (
    qexists_tac`ck`
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[]
    \\ simp[Once labSemTheory.evaluate_def] \\ NO_TAC) >>
  first_x_assum(qspec_then`r with clock := r.clock+1`mp_tac) >>
  impl_tac >- (
    imp_res_tac stackPropsTheory.evaluate_mono >>
    fs[] ) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  strip_tac >>
  first_assum(fn th => first_assum(
    tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
  rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
  rveq >>
  old_drule flatten_correct >> simp[] >>
  `loc_to_pc n 0 t2.code = SOME t2.pc` by metis_tac[IS_SOME_EXISTS] \\ fs[] \\
  simp[stackSemTheory.dec_clock_def] >>
  `r with clock := r.clock = r` by simp[stackSemTheory.state_component_equality] >> simp[] >>
  disch_then old_drule >> simp[] >>
  once_rewrite_tac[CONJ_COMM] >>
  fs[state_rel_def] >>
  res_tac >>
  rfs[] >>
  disch_then old_drule >> strip_tac >>
  ntac 6 (first_x_assum(qspec_then`ck'`mp_tac)) >>
  rw[] \\
  qexists_tac`ck+ck'`>>simp[]
QED

Definition halt_assum_def:
  halt_assum (:('ffi#'c)) code <=>
   !(s:(α,'c,'ffi)stackSem$state).
     subspt code s.code /\ s.clock <> 0 ==>
     ∃t. evaluate (Call NONE (INL 1) NONE,s) = (SOME (Halt (Word 0w)),t) /\
         t.ffi = s.ffi /\ t.clock = s.clock - 1
End

Theorem flatten_semantics:
   halt_assum (:'ffi#'c) (s1:(α,'c,'ffi)stackSem$state).code /\
   state_rel s1 (s2:('a,'c,'ffi)labSem$state) /\
   loc_to_pc start 0 s2.code = SOME s2.pc /\
   semantics start s1 <> Fail ==>
   semantics s2 = semantics start s1
Proof
  simp[GSYM AND_IMP_INTRO,halt_assum_def] >> strip_tac >>
  ntac 2 strip_tac >>
  simp[stackSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    srw_tac[][] >>
    simp[labSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      (*qhdtm_x_assum`stackSem$evaluate`kall_tac >>*)
      last_x_assum(qspec_then`k+k'+1`mp_tac) >> simp[] >>
      spose_not_then strip_assume_tac >>
      old_drule(GEN_ALL stackPropsTheory.evaluate_add_clock) >>
      disch_then(qspec_then `k' + 1` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      strip_tac >> fs[] >>
      old_drule(GEN_ALL flatten_call_correct) >>
      imp_res_tac state_rel_with_clock >>
      first_x_assum(qspec_then`k+(k'+1)`strip_assume_tac) >>
      disch_then old_drule >> simp[] >>
      `r <> TimeOut` by(CCONTR_TAC >> fs[]) >> fs[] >>
      `r <> Error` by(CCONTR_TAC >> fs[]) >> fs[] >>
      Cases_on `r` >> fs[] >>
      qpat_x_assum `FST _ = _` mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >> fs[] >> rveq >>
      old_drule(GEN_ALL evaluate_ADD_clock) >> simp[] >>
      rpt strip_tac >> first_x_assum(qspec_then `ck + k` assume_tac) >>
      fs[] >> rw[]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      srw_tac[][] >>
      qmatch_assum_abbrev_tac`stackSem$evaluate (e,s) = _` >>
      qmatch_assum_abbrev_tac`labSem$evaluate l = _` >>
      qispl_then[`e`,`s`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
      qispl_then[`l`](mp_tac o Q.GEN`extra`) labPropsTheory.evaluate_add_clock_io_events_mono >>
      simp[Abbr`s`,Abbr`l`] >>
      ntac 2 strip_tac >>
      unabbrev_all_tac >>
      old_drule(GEN_ALL flatten_call_correct) >>
      old_drule state_rel_with_clock >> strip_tac >>
      disch_then old_drule >>
      impl_tac
      >- (simp[] >> Cases_on `r` >> fs[] >>
          last_x_assum(qspec_then `k` mp_tac) >> simp[]) >>
      strip_tac >> fs[] >>
      Cases_on `r2 = TimeOut`
      >- (fs[] >> Cases_on `r` >> fs[] >> last_x_assum(qspec_then `k` assume_tac) >>
          rfs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
      fs[] >>
      dxrule(GEN_ALL labPropsTheory.evaluate_ADD_clock) >>
      disch_then(qspec_then `k'` mp_tac) >> simp[] >>
      dxrule(GEN_ALL labPropsTheory.evaluate_ADD_clock) >>
      disch_then(qspec_then `k - 1 + ck` mp_tac) >> simp[] >>
      `k' + (k - 1 + ck) = k - 1 + ck + k'` by decide_tac >>
      simp[] >> rpt strip_tac >>
      last_x_assum(qspec_then `k` mp_tac) >> strip_tac >>
      rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
      rfs[state_component_equality]) >>
    qmatch_assum_abbrev_tac`stackSem$evaluate (e,s) = _` >>
    qispl_then[`e`,`s`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
    disch_then(qspec_then`1`strip_assume_tac) >> rev_full_simp_tac(srw_ss())[] >>
    first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
    unabbrev_all_tac >>
    old_drule (GEN_ALL flatten_call_correct) >> simp[] >>
    old_drule (GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k+1`strip_assume_tac) >>
    disch_then old_drule >> simp[] >>
    impl_tac >- (
      last_x_assum(qspec_then`k+1`mp_tac) >>full_simp_tac(srw_ss())[]>> srw_tac[][]) >>
    strip_tac >>
    qpat_x_assum `evaluate _ = (SOME _,_)` assume_tac >>
    dxrule(GEN_ALL stackPropsTheory.evaluate_add_clock) >>
    disch_then(qspec_then `1` mp_tac) >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    strip_tac >> fs[] >> rveq >>
    last_x_assum(qspec_then `k+1` mp_tac) >> rpt strip_tac >>
    fs[] >> rfs[] >> fs[] >> metis_tac[]) >>
  strip_tac >>
  simp[labSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    last_x_assum(qspec_then`k+1`mp_tac) >>
    (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >> spose_not_then strip_assume_tac >>
    old_drule (GEN_ALL flatten_call_correct) >>
    old_drule (GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k+1`strip_assume_tac) >>
    disch_then old_drule >> simp[] >>
    conj_tac >- (
      spose_not_then strip_assume_tac >>
      first_x_assum(qspec_then`k+1`mp_tac) >> full_simp_tac(srw_ss())[] >>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      last_x_assum(qspec_then`s`mp_tac)>>simp[]>>
      metis_tac[]) >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k+1`mp_tac)>>simp[] >>
    Cases_on`q`>>full_simp_tac(srw_ss())[]>>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    qmatch_assum_abbrev_tac`FST p = _` >>
    Cases_on`p`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum (assume_tac o SYM) >>
    old_drule labPropsTheory.evaluate_ADD_clock >> simp[] >>
    qexists_tac`ck`>>simp[]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    last_x_assum(qspec_then`k+1`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    simp[] >>
    spose_not_then strip_assume_tac >>
    old_drule (GEN_ALL flatten_call_correct) >>
    old_drule (GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then`k+1`strip_assume_tac) >>
    disch_then old_drule >> simp[] >>
    conj_tac >- (
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'`>>full_simp_tac(srw_ss())[]>> srw_tac[][]>>
      metis_tac[FST,SND,PAIR]) >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k+1`mp_tac)>>simp[] >>
    Cases_on`q`>>full_simp_tac(srw_ss())[]>>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]>>
    qhdtm_x_assum`labSem$evaluate`mp_tac >>
    old_drule(labPropsTheory.evaluate_ADD_clock)>>
    disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
  strip_tac >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    let val s = ``s:('a,'c,'ffi) labSem$state``
        val t = ``s:('a,'c,'ffi) stackSem$state``
    in
    metis_tac[
      LESS_EQ_EXISTS,
      labPropsTheory.evaluate_add_clock_io_events_mono,
      stackPropsTheory.evaluate_add_clock_io_events_mono,
      EVAL``(^s with clock := k).clock``,
      EVAL``((^s with clock := k1) with clock := k2)``,
      EVAL``(^t with clock := k).clock``,
      EVAL``((^t with clock := k1) with clock := k2)``]
    end) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)` g) (#2 g)) >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`stackSem$evaluate (e,s) = _` >>
  qispl_then[`e`,`s`](mp_tac o Q.GEN`extra`) stackPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`1`strip_assume_tac) >> rev_full_simp_tac(srw_ss())[] >>
  first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
  unabbrev_all_tac >>
  old_drule (GEN_ALL flatten_call_correct) >> simp[] >>
  old_drule (GEN_ALL state_rel_with_clock) >>
  disch_then(qspec_then`k+1`strip_assume_tac) >>
  disch_then old_drule >> simp[] >>
  impl_tac >- (
    last_x_assum(qspec_then`k+1`mp_tac) >>full_simp_tac(srw_ss())[]>> srw_tac[][]) >>
  strip_tac >>
  reverse conj_tac >> strip_tac >- (
    qexists_tac`ck+k`>>simp[]>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[IS_PREFIX_APPEND]>>rev_full_simp_tac(srw_ss())[]>>simp[]>>
    simp[EL_APPEND1])>>
  qispl_then[`ck`,`s2 with clock := k`]mp_tac(GEN_ALL labPropsTheory.evaluate_add_clock_io_events_mono)>>
  simp[]>>strip_tac>>
  qexists_tac`k+1`>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND]>> simp[]>>
  simp[EL_APPEND1]
QED

Definition make_init_def:
  make_init code coracle regs save_regs (s:('a,'c,'ffi) labSem$state) =
    <| regs    := FEMPTY |++ (MAP (\r. r, read_reg r s) regs)
     ; fp_regs    := FEMPTY (*TODO: is this right? *)
     ; memory  := s.mem
     ; mdomain := s.mem_domain
     ; sh_mdomain := s.shared_mem_domain
     ; use_stack := F
     ; use_store := F
     ; use_alloc := F
     ; compile := (λc p. s.compile c (MAP prog_to_section p))
     ; compile_oracle := coracle
     ; code_buffer := s.code_buffer
     ; clock   := s.clock
     ; code    := code
     ; ffi     := s.ffi
     ; ffi_save_regs := save_regs
     ; be      := s.be |> :(α,'c,'ffi)stackSem$state
End

val make_init_semantics = flatten_semantics
  |> Q.INST [`s1`|->`make_init code coracle regs save_regs (s:('a,'c,'ffi)labSem$state)`,`s2`|->`s`]
  |> SIMP_RULE std_ss [EVAL ``(make_init code coracle regs save_regs s).code``];

Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload stack_names_compile[local] = ``stack_names$compile``
Overload stack_alloc_compile[local] = ``stack_alloc$compile``
Overload stack_remove_compile[local] = ``stack_remove$compile``

Definition full_make_init_def:
  full_make_init stack_conf data_conf max_heap sp offset bitmaps code s4 save_regs data_sp coracle =
  let ggc = is_gen_gc data_conf.gc_kind in
  let jump = stack_conf.jump in
  let code1 = stack_alloc$compile data_conf (stack_rawcall$compile code) in
  let code2 = compile jump offset ggc max_heap sp InitGlobals_location code1 in
  let code3 = fromAList (compile stack_conf.reg_names code2) in
  let coracle1 = (I ## MAP prog_comp ## I) o coracle in
  let coracle2 = (I ## MAP (prog_comp jump offset sp) ## I) o coracle1 in
  let coracle3 = (I ## compile stack_conf.reg_names ## I) o coracle2 in
  let s3 = make_init code3 coracle3 (MAP (find_name stack_conf.reg_names) [2;3;4]) save_regs s4 in
  let s2 = make_init stack_conf.reg_names (fromAList code2) coracle2 s3 in
  let s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp (fromAList code1) s2 in
    (make_init data_conf (fromAList code) coracle s1,
     make_init_opt ggc max_heap bitmaps data_sp coracle1 jump offset sp (fromAList code1) s2)
End

Theorem full_make_init_buffer:
    (FST(full_make_init a b c d e f g h i j k)).code_buffer.buffer = [] ∧
  (FST(full_make_init a b c d e f g h i j k)).data_buffer.buffer = []
Proof
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
     stack_removeProofTheory.make_init_any_def] >>
  every_case_tac>>fs[]>>
  EVAL_TAC>>
  pop_assum mp_tac>>fs[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>rw[]>>
  fs [stack_removeProofTheory.init_prop_def]
QED

Theorem full_make_init_ffi:
    (FST(full_make_init a b c d e f g h i j k)).ffi = h.ffi
Proof
  fs [full_make_init_def,stack_allocProofTheory.make_init_def] >>
  fs [stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC
QED

Theorem full_make_init_compile:
   (FST(full_make_init a b c d e f g h i j k)).compile =
   (λc. (λp. h.compile c (MAP prog_to_section (MAP (prog_comp a.reg_names) (MAP (prog_comp a.jump e d) p)))) o MAP prog_comp)
Proof
  fs [full_make_init_def,stack_allocProofTheory.make_init_def]
  \\ simp[stack_removeProofTheory.make_init_any_def,
          stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac stackPropsTheory.evaluate_consts \\ fs[]
  \\ EVAL_TAC \\ fs[]
  \\ EVAL_TAC \\ fs[]
QED

Definition memory_assumption_def:
  memory_assumption rnames (bitmaps:'a word list) data_sp t =
    ∃ptr2 ptr3 ptr4 bitmap_ptr.
      read_reg (find_name rnames 2) t = Word ptr2 ∧
      read_reg (find_name rnames 3) t = Word ptr3 ∧
      read_reg (find_name rnames 4) t = Word ptr4 ∧
      t.mem ptr2 = Word bitmap_ptr ∧
      t.mem (ptr2 + bytes_in_word) =
          Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
      t.mem (ptr2 + 2w * bytes_in_word) =
          Word (bitmap_ptr + bytes_in_word * n2w data_sp +
                bytes_in_word * n2w (LENGTH bitmaps)) ∧
      t.mem (ptr2 + 3w * bytes_in_word) = Word t.code_buffer.position ∧
      t.mem (ptr2 + 4w * bytes_in_word) =
          Word (t.code_buffer.position + n2w t.code_buffer.space_left) ∧
      t.code_buffer.buffer = [] /\
      ptr2 ≤₊ ptr4 ∧ byte_aligned ptr2 /\
      byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
      1024w * bytes_in_word ≤₊ ptr4 - ptr2 /\
     (word_list bitmap_ptr (MAP Word bitmaps) *
      word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp *
      word_list_exists ptr2
        (w2n (-1w * ptr2 + ptr4) DIV w2n (bytes_in_word:'a word)))
       (fun2set (t.mem,t.mem_domain))
End

Triviality halt_assum_lemma:
  halt_assum (:'ffi#'c)
     (fromAList (stack_names$compile f
       (compile jump off gen max_heap k l code)))
Proof
  fs [halt_assum_def] \\ rw []
  \\ fs [stackSemTheory.evaluate_def,
         stackSemTheory.find_code_def]
  \\ fs [stack_namesTheory.compile_def,
         stack_namesTheory.prog_comp_def,
         stack_removeTheory.compile_def,
         stack_removeTheory.init_stubs_def,
         subspt_def,
         lookup_fromAList,domain_fromAList,
         EVAL ``stack_names$comp f (halt_inst 0w)``]
  \\ first_x_assum(qspec_then`1`mp_tac) \\ simp[]
  \\ fs [stackSemTheory.evaluate_def,EVAL ``inst (Const n 0w) (dec_clock s)``,
         get_var_def,FLOOKUP_UPDATE]
QED

Triviality FLOOKUP_regs:
  !regs n v f s.
      FLOOKUP (FEMPTY |++ MAP (λr. (r,read_reg r s)) regs) n = SOME v ==>
      read_reg n s = v
Proof
  recInduct SNOC_INDUCT \\ fs [FUPDATE_LIST,FOLDL_SNOC,MAP_SNOC]
  \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ Cases_on `x = n` \\ fs []
QED

(*
Triviality FLOOKUP_fp_regs:
  !regs n v f s.
      FLOOKUP (FEMPTY |++ MAP (λr. (r,read_fp_reg r s)) regs) n = SOME v ==>
      s.fp_regs n = v
Proof
  recInduct SNOC_INDUCT \\ fs [FUPDATE_LIST,FOLDL_SNOC,MAP_SNOC]
  \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ Cases_on `x = n` \\ fs [read_fp_reg_def]
QED*)

Theorem state_rel_make_init:
   state_rel (make_init code coracle regs save_regs s) (s:('a,'c,'ffi) labSem$state) <=>
    (∀n prog.
     lookup n code = SOME (prog) ⇒
     call_args prog s.ptr_reg s.len_reg s.ptr2_reg s.len2_reg s.link_reg ∧
     ∃pc.
       code_installed pc (append (FST (flatten T prog n (next_lab prog 2)))) s.code ∧
       loc_to_pc n 0 s.code = SOME pc) ∧ ¬s.failed ∧
    s.compile_oracle = (λn. (λ(c,p,_). (c, MAP prog_to_section p)) (coracle n)) ∧
    (∀k.
      (λ(c,ps,_).
         EVERY
           (λ(n,p).
              call_args p s.ptr_reg s.len_reg s.ptr2_reg s.len2_reg s.link_reg ∧
              EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p) ∧
              ALL_DISTINCT (extract_labels p)) ps ∧
         ALL_DISTINCT (MAP FST ps)) (coracle k)) ∧
    s.link_reg ≠ s.len_reg ∧ s.link_reg ≠ s.ptr_reg ∧
    s.link_reg ≠ s.len2_reg ∧ s.link_reg ≠ s.ptr2_reg ∧
    s.link_reg ∉ save_regs ∧
    domain code = set (MAP Section_num s.code) ∧
    EVERY sec_labels_ok s.code ∧
    (∀k i n. k ∈ save_regs ⇒ s.io_regs n i k = NONE) ∧
    (∀k n. k ∈ save_regs ⇒ s.cc_regs n k = NONE) ∧
    (∀x. x ∈ s.mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
    (∀x. x ∈ s.shared_mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
    good_dimindex(:'a)
Proof
  fs [state_rel_def,make_init_def,FLOOKUP_regs]
  \\ eq_tac \\ strip_tac \\ fs []
  \\ metis_tac [FLOOKUP_regs]
QED

Triviality MAP_FST_compile_compile:
  MAP FST (compile jump off gen max_heap k InitGlobals_location
              (stack_alloc$compile c
                 (stack_rawcall$compile code))) =
    0::1::2::gc_stub_location::MAP FST code
Proof
  fs [stack_removeTheory.compile_def,stack_removeTheory.init_stubs_def,
      stack_allocTheory.compile_def,stack_rawcallTheory.compile_def,
      stack_allocTheory.stubs_def,stack_removeTheory.prog_comp_def]
  \\ rename [`comp_top ii`]
  \\ Induct_on `code` \\ fs []
  \\ fs [stack_removeTheory.prog_comp_def,FORALL_PROD,
         stack_allocTheory.prog_comp_def]
QED

val sextract_labels_def = stackPropsTheory.extract_labels_def

Theorem next_lab_non_zero[allow_rebind]:
    ∀p. 1 ≤ next_lab p 1 /\
        2 ≤ next_lab p 2
Proof
  once_rewrite_tac [next_lab_EQ_MAX] \\ fs [MAX_DEF]
QED

(*
Theorem stack_to_lab_lab_pres:
    ∀p n nl.
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels p) ∧
  ALL_DISTINCT (extract_labels p) ∧
  next_lab p 1 ≤ nl ⇒
  let (cp,nr,nl') = flatten p n nl in
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (append cp)) ∧
  ALL_DISTINCT (extract_labels (append cp)) ∧
  (∀lab. MEM lab (extract_labels (append cp)) ⇒ MEM lab (extract_labels p) ∨ (nl ≤ SND lab ∧ SND lab < nl')) ∧
  nl ≤ nl'
Proof
  HO_MATCH_MP_TAC flatten_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [flatten_def]>>fs[extract_labels_def,sextract_labels_def]
  >-
    (Cases_on`s`>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def,sextract_labels_def,compile_jump_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    TRY
      (fs[ALL_DISTINCT_APPEND,extract_labels_append]>>rw[]>>
      CCONTR_TAC>>fs[]>>res_tac>>fs[]>>NO_TAC)
    >>
    `1 ≤ nl` by metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[extract_labels_append,ALL_DISTINCT_APPEND,extract_labels_def]>>
    `next_lab q 1 ≤ m'` by fs[]>>
    fs[]>>rfs[]>>
    `r < nl ∧ r' < nl` by
      fs[MAX_DEF]>>
    rw[]>>
    CCONTR_TAC>>fs[]>>
    res_tac>>fs[]>>
    imp_res_tac extract_labels_next_lab>>fs[]>>
    metis_tac[])
  >>
    (rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    `1 ≤ nl` by
      metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[ALL_DISTINCT_APPEND]>>
    qpat_x_assum`A=(cp,_,nl')` mp_tac>>
    BasicProvers.EVERY_CASE_TAC>>strip_tac>>rveq>>fs[extract_labels_def,extract_labels_append,ALL_DISTINCT_APPEND]>>
    TRY
      (rw[]>>
      CCONTR_TAC>>fs[]>>
      res_tac>>fs[]>>
      imp_res_tac extract_labels_next_lab>>fs[])>>
    metis_tac[])
QED
*)

Triviality MAP_prog_to_section_FST:
  MAP (λs. case s of Section n v => n) (MAP prog_to_section prog) =
  MAP FST prog
Proof
  match_mp_tac LIST_EQ>>rw[EL_MAP]>>Cases_on`EL x prog`>>fs[prog_to_section_def]>>
  pairarg_tac>>fs[]
QED

Triviality extract_label_store_list_code:
  ∀a t ls.
  extract_labels (store_list_code a t ls) = []
Proof
  ho_match_mp_tac stack_removeTheory.store_list_code_ind>>
  EVAL_TAC>>fs[]
QED

Theorem stack_to_lab_compile_lab_pres:
    EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST prog) ∧
  EVERY (λn,p.
    let labs = extract_labels p in
    EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
    ALL_DISTINCT labs) prog ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  labels_ok (compile c c2 c3 sp offset prog)
Proof
  rw[labels_ok_def,stack_to_labTheory.compile_def]
  >-
    (fs[MAP_prog_to_section_FST,MAP_FST_compile_compile]>>
    fs[EVERY_MEM]>>CCONTR_TAC>>fs[]>>res_tac>>fs[] >>
    pop_assum mp_tac >> EVAL_TAC) >>
  fs[EVERY_MAP,prog_to_section_def,EVERY_MEM,FORALL_PROD]>>
  rw[]>>pairarg_tac>>fs[extract_labels_def,extract_labels_append]>>
  Q.ISPECL_THEN [`T`,`p_2`,`p_1`,`next_lab p_2 2`] mp_tac stack_to_lab_lab_pres_T>>
  impl_keep_tac>-
      (*stack_names*)
    (fs[stack_namesTheory.compile_def,MEM_MAP]>>
     Cases_on`y`>>fs[stack_namesTheory.prog_comp_def,GSYM stack_names_lab_pres]>>
     (*stack_remove*)
     fs[stack_removeTheory.compile_def,stack_removeTheory.init_stubs_def,MEM_MAP]>>
     EVAL_TAC>>BasicProvers.EVERY_CASE_TAC>>
     EVAL_TAC>>fs[extract_label_store_list_code]>>
     Cases_on`y`>>fs[stack_removeTheory.prog_comp_def,GSYM stack_remove_lab_pres]>>
     (*stack_alloc*)
      fs[stack_allocTheory.compile_def,stack_allocTheory.stubs_def,MEM_MAP]>>
      EVAL_TAC >> TRY TOP_CASE_TAC >>
      EVAL_TAC >> TRY TOP_CASE_TAC >>
      EVAL_TAC >> Cases_on`y`>>
      TRY (rw [] \\ EVAL_TAC) >>
      fs[stack_allocTheory.prog_comp_def]>>
      Q.SPECL_THEN [`q''`,`next_lab r'' 2`,`r''`] mp_tac stack_alloc_lab_pres>>
      fs [] >>
      (impl_tac>-
        (fs [stack_rawcallTheory.compile_def] >>
         rename [`comp_top ii`] >>
         fs [MEM_MAP,EXISTS_PROD] >>
         rveq >> fs [stack_rawcallProofTheory.extract_labels_comp]>>
         res_tac>>fs[EVERY_MEM,FORALL_PROD]>>
         metis_tac[]))>>
      rw[]>>pairarg_tac>>fs[])>>
  Cases_on `is_Seq p_2` THEN1
   (fs[EVERY_MEM]>>rw[]>>res_tac>>fs[ALL_DISTINCT_APPEND]
    >- (qsuff_tac`2 ≤ m` >> fs[]>>
        metis_tac[LESS_EQ_TRANS,next_lab_non_zero])
    >> CCONTR_TAC>>fs[]>>res_tac>>fs[]
    >> imp_res_tac extract_labels_next_lab>>fs[])
  >> fs [flatten_T_F]
  >> Q.ISPECL_THEN [`F`,`p_2`,`p_1`,`next_lab p_2 2`] mp_tac stack_to_lab_lab_pres
  >> impl_tac THEN1 fs []
  >> simp [] >> ntac 2 strip_tac
  >> rpt strip_tac >> fs [ALL_DISTINCT_APPEND]
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [])
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [])
  \\ CCONTR_TAC \\ fs [EVERY_MEM] \\ res_tac \\ fs []
QED

Definition good_code_def:
  good_code sp code ⇔
   ALL_DISTINCT (MAP FST code) ∧
   EVERY (λ(k,prog). stack_num_stubs ≤ k ∧ alloc_arg prog) code ∧
   EVERY (λp. call_args p 1 2 3 4 0) (MAP SND code) ∧
   EVERY (λp. reg_bound p sp) (MAP SND code) ∧
   EVERY
   (λ(n,p).
      EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p) ∧
      ALL_DISTINCT (extract_labels p)) code
End

Definition contain_def:
  contain b = Abbrev b
End

Theorem full_make_init_semantics:
   full_make_init stack_conf data_conf max_heap sp offset
    (bitmaps:'a word list) code t save_regs data_sp coracle = (s,opt) ∧
   good_dimindex(:'a) ∧
   t.code = stack_to_lab$compile stack_conf data_conf max_heap sp offset code ∧
   t.compile_oracle = (λn.
     let (c,p,b) = coracle n in
       (c,compile_no_stubs stack_conf.reg_names stack_conf.jump offset sp p)) ∧
   ¬t.failed ∧
   memory_assumption stack_conf.reg_names bitmaps data_sp t ∧
   max_stack_alloc ≤ max_heap ∧
   t.link_reg ∉ save_regs ∧ t.pc = 0 ∧
   (∀k i n. k ∈ save_regs ⇒ t.io_regs n i k = NONE) ∧
   (∀k n. k ∈ save_regs ⇒ t.cc_regs n k = NONE) ∧
   (∀x. x ∈ t.mem_domain ⇒ w2n x MOD (dimindex(:'a) DIV 8) = 0) ∧
   (∀x. x ∈ t.shared_mem_domain ⇒ w2n x MOD (dimindex(:'a) DIV 8) = 0) ∧
   good_code sp code ∧
   (∀n. good_code sp (FST(SND(coracle n)))) ∧
   10 <= sp ∧
   EVERY (λr. (find_name stack_conf.reg_names (r+sp-2)) ∈ save_regs) [2;3;4] ∧
   find_name stack_conf.reg_names 4 = t.len2_reg ∧
   find_name stack_conf.reg_names 3 = t.ptr2_reg ∧
   find_name stack_conf.reg_names 2 = t.len_reg ∧
   find_name stack_conf.reg_names 1 = t.ptr_reg ∧
   find_name stack_conf.reg_names 0 = t.link_reg ∧
   BIJ (find_name stack_conf.reg_names) UNIV UNIV
   ⇒
   Abbrev (opt <> NONE /\ (semantics InitGlobals_location s ≠ Fail ⇒
   semantics t = semantics InitGlobals_location s))
Proof
  srw_tac[][full_make_init_def,GSYM contain_def]
  \\ last_x_assum mp_tac \\ LET_ELIM_TAC
  \\ rewrite_tac [contain_def]
  (* Prove the syntactic things for the oracle sequences *)
  \\ `semantics 0 s2 ≠ Fail ⇒ semantics t = semantics 0 s2`
  by (
    strip_tac
    \\ (GSYM stack_namesProofTheory.make_init_semantics
        |> Q.GENL[`code`,`f`,`s`,`start`,`oracle`]
        |> Q.ISPECL_THEN[`code2`,`stack_conf.reg_names`,`s3`,`0`,`coracle2`]mp_tac)
    \\ simp[]
    \\ impl_tac
    >- (
      simp[Abbr`s3`] \\ fs[good_code_def]
      \\ simp[make_init_def]
      \\ simp[Abbr`code2`]
      \\ simp[stack_removeTheory.compile_def,
              stack_removeProofTheory.prog_comp_eta,
              stack_removeTheory.init_stubs_def,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[Abbr`code1`,stack_allocTheory.compile_def,
              stack_allocProofTheory.prog_comp_lambda,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[stack_rawcallTheory.compile_def,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\  fs[ALL_DISTINCT_APPEND]
      \\ EVAL_TAC
      \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,FORALL_PROD]
      \\ CCONTR_TAC \\ fs[] \\ res_tac
      \\ fs[backend_commonTheory.stack_num_stubs_def] )
    \\ disch_then (SUBST_ALL_TAC)
    \\ simp[Abbr`s3`]
    \\ match_mp_tac make_init_semantics
    \\ conj_tac
    >- ( simp[Abbr`code3`,Abbr`code2`,halt_assum_lemma] )
    \\ conj_tac
    >- (
      simp[state_rel_make_init] \\ fs[good_code_def]
      \\ conj_tac
      >- (
        simp[Abbr`code3`,lookup_fromAList]
        \\ simp[stack_to_labTheory.compile_def]
        \\ qmatch_goalsub_abbrev_tac`ALOOKUP code3`
        \\ `EVERY (λp. call_args p t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg) (MAP SND code3)`
        by (
          rpt(qpat_x_assum`find_name _ _ = _`(sym_sub_tac))
          \\ match_mp_tac (GEN_ALL stack_namesProofTheory.stack_names_call_args)
          \\ qexists_tac`code2` \\ simp[]
          \\ match_mp_tac (GEN_ALL stack_removeProofTheory.stack_remove_call_args)
          \\ first_assum(part_match_exists_tac (fst o dest_conj) o (rconc o SYM_CONV o rand o concl))
          \\ simp[Abbr`code1`]
          \\ match_mp_tac (GEN_ALL stack_allocProofTheory.stack_alloc_call_args)
          \\ simp [stack_rawcallProofTheory.stack_alloc_call_args])
        \\ ntac 3 strip_tac
        \\ conj_tac
        >- (
          imp_res_tac ALOOKUP_MEM \\
          fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]
          \\ metis_tac[] )
        \\ match_mp_tac code_installed_prog_to_section
        \\ simp[Abbr`code2`,Abbr`code1`,Abbr`ggc`,Abbr`code3`,Abbr`jump`]
        \\ (stack_to_lab_compile_lab_pres
            |> SIMP_RULE(srw_ss()++LET_ss)[stack_to_labTheory.compile_def]
            |> match_mp_tac)
        \\ simp[]
        \\ fs[EVERY_MEM,EVERY_MAP,EXISTS_PROD,FORALL_PROD]
        \\ rw[] \\ strip_tac \\ res_tac
        \\ rfs[backend_commonTheory.stack_num_stubs_def,stackLangTheory.gc_stub_location_eq] )
      \\ conj_tac
      >- (
        simp[FUN_EQ_THM,Abbr`coracle3`,Abbr`coracle2`,Abbr`coracle1`,compile_no_stubs_def]
        \\ simp[UNCURRY] )
      \\ conj_tac >-(
        strip_tac>>
        first_x_assum(qspec_then`k` assume_tac)>>fs[]>>
        Cases_on`coracle k`>>Cases_on`r`>>rfs[]>>
        unabbrev_all_tac>>fs[]>>
        old_drule stack_alloc_call_args>>
        strip_tac>>
        fs[stack_allocTheory.compile_def,PAIR_MAP]>>
        (* call_args preservation *)
        old_drule (stack_remove_call_args |> SIMP_RULE (srw_ss()) [EQ_SYM_EQ,Once CONJ_COMM] |> GEN_ALL) >> simp[]>>
        fs[stack_removeTheory.compile_def,FORALL_AND_THM,GSYM AND_IMP_INTRO]>>
        disch_then kall_tac>>
        disch_then(qspecl_then[`offset`,`sp`,`stack_conf.jump`] assume_tac)>>
        old_drule (stack_names_call_args |> SIMP_RULE (srw_ss()) [EQ_SYM_EQ,Once CONJ_COMM] |> GEN_ALL)>>
        simp[]>>
        disch_then(qspec_then`stack_conf.reg_names` assume_tac)>>rfs[]>>
        fs[Once EVERY_MEM,stack_namesTheory.compile_def,MEM_MAP,PULL_EXISTS,UNCURRY]>>
        reverse conj_tac>-
          fs[MAP_MAP_o,o_DEF,ETA_AX,prog_comp_eta,stack_allocProofTheory.prog_comp_lambda,UNCURRY]>>
        simp[FORALL_PROD,PULL_FORALL,prog_comp_eta,stack_allocProofTheory.prog_comp_lambda,stack_namesTheory.prog_comp_def]>>
        ntac 3 strip_tac>>
        rpt(first_x_assum old_drule>>strip_tac)>>
        fs[]>>
        imp_res_tac stack_alloc_lab_pres>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum(qspec_then`next_lab p_2 2` assume_tac)>>fs[]>>
        pairarg_tac>>fs[]>>
        metis_tac[stack_names_lab_pres,stack_remove_lab_pres])
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,DECIDE``0n <> 1 /\ 0n <> 2 /\ 1n <> 2``,INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,DECIDE``0n <> 1 /\ 0n <> 2 /\ 1n <> 2``,INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,
             DECIDE``0n <> 1 /\ 0n <> 2 /\ 0n <> 3 /\ 0n <> 4 /\ 1n <> 2 /\ 1n <> 3 /\ 2n <> 3``, INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,
             DECIDE``0n <> 1 /\ 0n <> 2 /\ 0n <> 3 /\ 1n <> 2 /\ 1n <> 3``, INJ_DEF] )
      \\ simp[Abbr`code3`,domain_fromAList,Abbr`code2`]
      \\ conj_tac >-
        simp[compile_def,MAP_prog_to_section_Section_num]>>
      qmatch_goalsub_abbrev_tac`EVERY _ cc`>>
      `labels_ok cc` by
        (fs[Abbr`cc`]>>
        match_mp_tac stack_to_lab_compile_lab_pres>>
        fs[]>>
        `!n. stack_num_stubs ≤ n ⇒ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location` by
          (EVAL_TAC>>fs[])>>
        fs[UNCURRY,EVERY_MEM,MEM_MAP,PULL_EXISTS])>>
      metis_tac[labels_ok_imp])
    \\ conj_tac
    >- (
      simp[stack_to_labTheory.compile_def,
           stack_namesTheory.compile_def,Abbr`code2`,
           stack_removeTheory.compile_def,
           stack_removeTheory.init_stubs_def,
           stack_namesTheory.prog_comp_def,
           prog_to_section_def] \\
      pairarg_tac \\ fs[Once loc_to_pc_def] )
    \\ rfs[])
  \\ `discharge_these stack_conf.jump offset ggc max_heap sp InitGlobals_location coracle1 code1 s2`
  by (
    simp[discharge_these_def] \\ fs[good_code_def]
    \\ simp[Abbr`s2`]
    \\ conj_tac
    >- (
      imp_res_tac stack_rawcallProofTheory.stack_rawcall_reg_bound \\
      imp_res_tac stack_alloc_reg_bound \\
      rfs[EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS,Abbr`code1`] \\
      first_x_assum(qspec_then`data_conf`mp_tac) \\ simp[] \\
      ntac 4 strip_tac \\
      conj_tac >- metis_tac[] \\
      fs[stack_allocTheory.compile_def,stack_allocTheory.stubs_def]
      >- EVAL_TAC
      \\ fs[stack_allocProofTheory.prog_comp_lambda,MEM_MAP,EXISTS_PROD,
            stack_rawcallTheory.compile_def]
      \\ res_tac \\ fs[] )
    \\ simp[stack_namesProofTheory.make_init_def,Abbr`code2`,Abbr`s3`,make_init_def]
    \\ simp[domain_fromAList]
    \\ conj_tac >-(
      ntac 4 strip_tac>>
      first_x_assum(qspec_then`n` assume_tac)>>
      Cases_on`coracle n`>>Cases_on`r`>>fs[]>>
      fs[Abbr`coracle1`]>>
      old_drule (GEN_ALL stack_alloc_reg_bound)>>
      disch_then old_drule>>
      disch_then(qspec_then `ARB` assume_tac)>>
      fs[stack_allocTheory.compile_def]>>
      fs[Once EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD]>>
      conj_tac>-
        metis_tac[]>>
      fs[stack_allocProofTheory.prog_comp_lambda,MEM_MAP,UNCURRY]>>
      Cases_on`y`>>fs[]>>
      rpt(first_x_assum old_drule)>>
      fs[])
    \\ conj_tac >- EVAL_TAC
    \\ fs[]
    \\ metis_tac[LINV_DEF,IN_UNIV,BIJ_DEF] ) \\
  `propagate_these s2 bitmaps data_sp` by (
    fs[propagate_these_def,Abbr`s2`,Abbr`s3`,
        stack_namesProofTheory.make_init_def,
        make_init_def,BIJ_FLOOKUP_MAP_KEYS,
        flookup_fupdate_list]
    \\ fs[memory_assumption_def]) \\
  `t.ffi = s2.ffi` by
    (unabbrev_all_tac>>EVAL_TAC)
  \\ (stack_allocProofTheory.make_init_semantics
      |> Q.GENL[`start`,`c`,`s`,`oracle`,`code`]
      |> Q.ISPECL_THEN[`InitGlobals_location`,`data_conf`,`s1`,
               `coracle`,`stack_rawcall$compile code`]mp_tac)
  \\ `¬(stack_num_stubs ≤ gc_stub_location)` by EVAL_TAC
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ impl_tac
  >- (
    fs[good_code_def] \\
    conj_tac >- (
      simp [stack_rawcallTheory.compile_def,ALOOKUP_MAP,PULL_EXISTS]
      \\ ntac 3 strip_tac \\ imp_res_tac ALOOKUP_MEM
      \\ fs[EVERY_MEM,FORALL_PROD,stack_rawcallProofTheory.call_arg_comp]
      \\ metis_tac[]) \\
    conj_tac >- (
      `!k. stack_num_stubs ≤ k ⇒ k ≠ gc_stub_location` by
        (EVAL_TAC>>fs[])>>
      fs[EVERY_MEM,UNCURRY]>>
      metis_tac[FST,SND])
    \\ simp[Abbr`s1`,make_init_any_use_stack,make_init_any_use_store,
            make_init_any_use_alloc,make_init_any_code,make_init_any_bitmaps,
            make_init_any_stack_limit,make_init_any_compile_oracle]
    \\ simp[make_init_any_def,stack_rawcallProofTheory.MAP_FST_compile]
    \\ fs[make_init_opt_def,case_eq_thms,init_prop_def,init_reduce_def]
    \\ rw[] \\ fs [good_dimindex_def,dimword_def])
  \\ disch_then(assume_tac o GSYM)
  \\ old_drule stack_removeProofTheory.make_init_semantics
  \\ simp [] \\ strip_tac \\ simp []
  \\ fs [] \\ rveq \\ fs []
  \\ rewrite_tac [markerTheory.Abbrev_def] \\ rw []
  \\ fs[make_init_any_def]
  \\ first_assum (mp_then (Pos last) mp_tac stack_rawcallProofTheory.compile_semantics)
  \\ disch_then (qspec_then `code` mp_tac)
  \\ impl_tac THEN1 fs [stack_allocProofTheory.make_init_def,good_code_def]
  \\ qmatch_goalsub_abbrev_tac `semantics _ m1`
  \\ rename [`(make_init data_conf (fromAList code) coracle s0)`]
  \\ `m1 = make_init data_conf (fromAList (stack_rawcall$compile code)) coracle s0` by
    simp [Abbr`m1`,stack_allocProofTheory.make_init_def]
  \\ rveq \\ fs []
  \\ metis_tac []
QED

Theorem full_make_init_semantics[allow_rebind] =
  full_make_init_semantics |> REWRITE_RULE [markerTheory.Abbrev_def]

Theorem EVERY_sec_ends_with_label_MAP_prog_to_section[simp]:
   ∀prog. EVERY sec_ends_with_label (MAP prog_to_section prog)
Proof
  Induct \\ simp[] \\ Cases \\ simp[prog_to_section_def]
  \\ pairarg_tac \\ fs[sec_ends_with_label_def]
QED

val stack_asm_ok_def = stackPropsTheory.stack_asm_ok_def

Triviality flatten_line_ok_pre:
  ∀t p n m ls a b c.
  byte_offset_ok c 0w /\
  stack_asm_ok c p ∧
  flatten t p n m = (ls,a,b) ⇒
  EVERY (line_ok_pre c) (append ls)
Proof
  ho_match_mp_tac flatten_ind>>Cases_on`p`>>rw[]>>
  pop_assum mp_tac>>simp[Once flatten_def]>>rw[]>>fs[]
  >-
    (EVAL_TAC>>fs[stack_asm_ok_def])
  >-
    (every_case_tac>>fs[stack_asm_ok_def]>>
    rpt(pairarg_tac>>fs[])>>
    Cases_on`s`>>fs[]>>rw[]>>TRY(EVAL_TAC>>fs[]>>NO_TAC))
  >-
    (rpt(pairarg_tac>>fs[CaseEq"bool"])>>fs[stack_asm_ok_def]>>
    rw[] \\ EVAL_TAC)
  >-
    (*TODO: Actually the jump part of Ifs should be moved out into the
    line_ok_pre check as well as well *)
    (rpt(pairarg_tac>>fs[])>>
    every_case_tac>>fs[stack_asm_ok_def]>>rw[]>>EVAL_TAC)
  >-
    (*TODO: see above*)
    (rpt(pairarg_tac>>fs[])>>rw[]>>fs[stack_asm_ok_def]>>
    EVAL_TAC)
  >>
    pop_assum mp_tac>>EVAL_TAC>>
    pop_assum mp_tac>>EVAL_TAC>>
    fs[]>>
    Cases_on ‘a’>>EVAL_TAC>>rw[]
QED

Theorem compile_all_enc_ok_pre:
    byte_offset_ok c 0w ∧
    EVERY (λ(n,p).stack_asm_ok c p) prog ⇒
    all_enc_ok_pre c (MAP prog_to_section prog)
Proof
  fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD]>>rw[]>>
  fs[prog_to_section_def]>>pairarg_tac>>rw[] >>
  TRY (EVAL_TAC \\ NO_TAC) >>
  metis_tac[flatten_line_ok_pre]
QED

(* stack_name renames registers to obey non-clashing names
  It should be sufficient that the incoming nregs < reg_count - avoid_regs,
  and that the mapping target for these avoids bad regs
*)

Theorem stack_to_lab_compile_all_enc_ok:
  EVERY (λ(n,p). stack_asm_name c p) prog ∧
  EVERY (λ(n,p). stack_asm_remove c p) prog ∧
  names_ok c1.reg_names (c:'a asm_config).reg_count c.avoid_regs ∧
  fixed_names c1.reg_names c ∧
  addr_offset_ok c 0w ∧ good_dimindex (:α) ∧
  byte_offset_ok c 0w ∧
  (∀n. n ≤ max_stack_alloc ⇒
  c.valid_imm (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) ∧
  c.valid_imm (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) ∧
  c.valid_imm (INL Add) 1w ∧ c.valid_imm (INL Sub) 1w ∧
  c.valid_imm (INL Add) 4w ∧ c.valid_imm (INL Add) 8w ∧
  (∀s. addr_offset_ok c (store_offset s)) ∧ reg_name 10 c ∧
  reg_name (sp + 2) c ∧ reg_name (sp + 1) c ∧ reg_name sp c  ∧
  conf_ok (:'a) c2 ∧ sp ≠ 0 ⇒
  all_enc_ok_pre c (compile c1 c2 c3 sp c.addr_offset prog)
Proof
  rw[stack_to_labTheory.compile_def]>>
  match_mp_tac compile_all_enc_ok_pre>>fs[]>>
  match_mp_tac stack_names_stack_asm_ok>>fs[]>>
  match_mp_tac stack_remove_stack_asm_name>>fs[stackPropsTheory.reg_name_def]>>
  match_mp_tac stack_alloc_stack_asm_convs>>fs[stackPropsTheory.reg_name_def]>>
  fs [stack_rawcallProofTheory.stack_alloc_stack_asm_convs]
QED

Theorem IMP_init_store_ok:
   max_heap = 2 * max_heap_limit (:'a) c1 -1 /\
  (fmis,xxx) = full_make_init stack_conf c1 max_heap sp offset (bitmaps:'a word list) code s save_regs data_sp coracle
  ==>
    init_store_ok c1
      (fmis.store \\ Handler)
       fmis.memory
       fmis.mdomain
      fmis.code_buffer
      fmis.data_buffer
Proof
  strip_tac \\ rveq \\
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def]
  \\ CASE_TAC \\ fs [] THEN1
   (fs [data_to_word_gcProofTheory.init_store_ok_def,FUPDATE_LIST,
        stack_removeTheory.store_list_def,
        FLOOKUP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]
    \\ rw [] \\ qexists_tac `0` \\ fs [word_list_exists_def]
    \\ conj_tac THEN1 (CASE_TAC \\ fs [])
    \\ fs [set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,LENGTH_NIL]
    \\ fs [word_list_def,set_sepTheory.emp_def,set_sepTheory.fun2set_def]
    \\ EVAL_TAC \\ fs [n2w_mod])
  \\ fs [stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs [] \\ NTAC 2 (pop_assum kall_tac) \\ rw []
  \\ fs [data_to_word_gcProofTheory.init_store_ok_def,
         stack_removeProofTheory.init_prop_def]
  \\ rewrite_tac [DECIDE ``2 * n = n + n:num``,
       stack_removeProofTheory.word_list_exists_ADD]
  \\ qexists_tac`len`
  \\ fs [FLOOKUP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]
  \\ Cases_on `c1.gc_kind` \\ fs [is_gen_gc_def]
QED

Theorem IMP_init_state_ok:
  4 < kkk /\
  (bitmaps:'a word list) = 4w::t ∧
  good_dimindex (:α) /\
  (∀n.
    (λ((bm0,cfg),progs).
     EVERY
       (post_alloc_conventions kkk ∘ SND ∘ SND) progs ∧
     EVERY (flat_exp_conventions ∘ SND ∘ SND) progs ∧
     EVERY ((λy. raise_stub_location ≠ y) ∘ FST) progs ∧
     EVERY ((λy. store_consts_stub_location ≠ y) ∘ FST) progs ∧
     (n = 0 ⇒ bm0 = LENGTH bitmaps)) (word_oracle n)) ∧
  stack_oracle =
  (λn.
   (λ((bm0,cfg),progs).
      (λ(progs,fs,bm). (cfg,progs,append (FST bm)))
        (compile_word_to_stack
           ac kkk progs
           (Nil, bm0))) (word_oracle n)) ∧
    (full_make_init scc dc max_heap stk stoff bitmaps p6 lab_st save_regs data_sp stack_oracle = (fmis,SOME xxx))
    ==>
    init_state_ok ac kkk fmis word_oracle
Proof
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def] \\ strip_tac
  \\ every_case_tac \\ fs []
  \\ fs [word_to_stackProofTheory.init_state_ok_def,data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun]
  \\ conj_tac THEN1 fs [good_dimindex_def]
  \\ qpat_x_assum`_ = fmis` sym_sub_tac \\ rveq\\ fs[]
  \\ qpat_assum `_` mp_tac
  \\ rewrite_tac [stack_removeProofTheory.make_init_opt_def]
  \\ qpat_abbrev_tac `read_ptrs = read_pointers _`
  \\ disch_then kall_tac
  \\ `init_prop (is_gen_gc dc.gc_kind) max_heap data_sp
        (get_stack_heap_limit max_heap read_ptrs) x /\
      x.bitmaps = 4w::t` by
        (fs [stack_removeProofTheory.make_init_opt_def,
             stack_removeProofTheory.make_init_opt_def]
         \\ every_case_tac \\ fs [stack_removeProofTheory.init_reduce_def] \\ rw [])
  \\ fs [stack_removeProofTheory.init_prop_def]
  \\ `x.stack <> []` by (rpt strip_tac \\ fs [])
  \\ `?t1 t2. x.stack = SNOC t1 t2` by metis_tac [SNOC_CASES]
  \\ fs [] \\ rpt var_eq_tac \\ fs[ADD1,SNOC_APPEND]
  \\ qpat_x_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF] >>
  fs[data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun] >>
  qhdtm_x_assum `make_init_opt` mp_tac>>
  simp[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[stack_removeProofTheory.init_reduce_def]>>rw[]>>fs[]
QED

Theorem full_make_init_has_fp_ops[simp]:
  full_make_init stack_conf
      (dconf with <| has_fp_ops := b1; has_fp_tern := b2 |>)
      mheap sp offset bitmaps code s save_regs dsp cor =
    full_make_init stack_conf dconf
      mheap sp offset bitmaps code s save_regs dsp cor
Proof
  rewrite_tac [full_make_init_def] \\ fs []
  \\ fs [stack_allocProofTheory.make_init_def]
QED

Definition complex_get_code_labels_def:
  (complex_get_code_labels (Seq p1 p2) = complex_get_code_labels p1 UNION complex_get_code_labels p2) /\
  (complex_get_code_labels (If _ _ _ p1 p2) = complex_get_code_labels p1 UNION complex_get_code_labels p2) /\
  (complex_get_code_labels (Call ret dest handler) =
     (case dest of INL x => {(x,0)} | _ => {}) ∪
     (case ret of
      | NONE => {}
      | SOME (r,_,l1,l2) => (l1,l2) INSERT complex_get_code_labels r UNION
          (case handler of
           | NONE => {}
           | SOME (r,l1,l2) => (l1,l2) INSERT complex_get_code_labels r))) /\
  (complex_get_code_labels (While c n r p) = complex_get_code_labels p) /\
  (complex_get_code_labels (LocValue i l1 l2) = {(l1,l2)}) /\
  (complex_get_code_labels (RawCall l) = {(l,1)}) /\
  (complex_get_code_labels (JumpLower n m l) = {(l,0)}) /\
  (complex_get_code_labels _ = {})
End
val _ = export_rewrites["complex_get_code_labels_def"];

Theorem complex_flatten_labels:
    ∀t p n m.
  let pp = set(append (FST (flatten t p n m))) in
  BIGUNION (IMAGE line_get_labels pp)
  ⊆
  (n,0) INSERT
  (n,if t /\ ?p1 p2. p = Seq p1 p2 then 1 else 0) INSERT
  IMAGE (λn2. (n,n2)) (BIGUNION (IMAGE line_get_code_labels pp)) ∪
  complex_get_code_labels p
Proof
  recInduct flatten_ind >> rw[]
  THEN1
   (once_rewrite_tac [flatten_def]>>
    fs[line_get_labels_def,get_code_labels_def]>>
    rpt(pairarg_tac>>fs[]) >>
    rw[] >> fs[line_get_labels_def,get_code_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
  once_rewrite_tac [flatten_def]>>
  Cases_on `p`>>
  fs[line_get_labels_def,get_code_labels_def]>>
  rpt(pairarg_tac>>fs[])
  >-
    (TOP_CASE_TAC
    >-
      (* hidden jump target in dest *)
      (Cases_on`s`>>fs[compile_jump_def,line_get_labels_def]>>
      fs[])>>
    PairCases_on`x`>>fs[]>>
    pairarg_tac>>fs[]>>
    TOP_CASE_TAC>>
    fs[]>>TRY(PairCases_on`x`>>fs[]>> pairarg_tac)>>
    fs[line_get_labels_def] >>
    Cases_on`s`>>
    fs[compile_jump_def,line_get_labels_def]>>
    rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    rw[] >> fs[line_get_labels_def,get_code_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (* locally introduced labels in If *)
    (rw[]>>
    fs[line_get_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    fs[line_get_labels_def]>>
    match_mp_tac SUBSET_TRANS>>
    asm_exists_tac>>
    rw[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
QED

Theorem flatten_labels:
   ∀t m n p l x y.
     flatten t m n p = (l,x,y) ∧
     EVERY (sec_label_ok n) (append l)
     ⇒
     BIGUNION (IMAGE line_get_labels (set (append l))) ⊆
     sec_get_code_labels (Section n (append l)) ∪
     get_code_labels m
Proof
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = debug p`
  \\ Cases_on`p` \\ fs[] \\ rveq
  \\ fs[labPropsTheory.line_get_labels_def,
        labPropsTheory.sec_get_code_labels_def]
  >- (
    fs[CaseEq"option",CaseEq"prod"]
    \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ EVAL_TAC \\ fs[] \\ rw[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ fs[labPropsTheory.line_get_labels_def,
            labPropsTheory.line_get_code_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac[] )
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ fs[CaseEq"bool"] \\ rveq
    \\ fsrw_tac[DNF_ss][labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ metis_tac[] )
QED

Theorem get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma:
   ∀p. EVERY sec_labels_ok (MAP prog_to_section p) ⇒
    get_labels (MAP prog_to_section p) ⊆
    get_code_labels (MAP prog_to_section p) ∪
    BIGUNION (IMAGE get_code_labels (set (MAP SND p)))
Proof
  Induct \\ simp[FORALL_PROD] >- (EVAL_TAC \\ simp[])
  \\ rw[stack_to_labTheory.prog_to_section_def]
  \\ pairarg_tac \\ fs[labPropsTheory.get_labels_cons, labPropsTheory.get_code_labels_cons]
  \\ simp[labPropsTheory.sec_get_labels_def, labPropsTheory.sec_get_code_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[labPropsTheory.line_get_labels_def]
  \\ qmatch_asmsub_abbrev_tac`flatten q n z t`
  \\ qspecl_then[`q`,`n`,`z`,`t`]mp_tac flatten_labels
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS, labPropsTheory.sec_get_code_labels_def]
  \\ rw[] \\ first_x_assum old_drule \\ rw[]
  \\ metis_tac[]
QED

Triviality prog_to_section_preserves_MAP_FST:
  ∀p.
    IMAGE (λn. n,0) (set (MAP FST p)) ⊆
    get_code_labels (MAP prog_to_section p)
Proof
  Induct>>
    fs[labPropsTheory.get_code_labels_cons,FORALL_PROD,stack_to_labTheory.prog_to_section_def]>>
    rw[]>> rpt(pairarg_tac>>fs[])>>
    simp[labPropsTheory.get_code_labels_cons, labPropsTheory.sec_get_code_labels_def]>>
    fs[SUBSET_DEF]
QED

Theorem prog_to_section_labels:
    prog_to_section (n,p) = pp ⇒
  sec_get_labels pp
  ⊆
  sec_get_code_labels pp ∪ complex_get_code_labels p
Proof
  rw[prog_to_section_def]>>pairarg_tac>>fs[]>>
  qspecl_then [`T`,`p`,`n`,`next_lab p 2`] assume_tac complex_flatten_labels>>
  rfs[]>>
  fs[sec_get_labels_def,sec_get_code_labels_def,line_get_labels_def]>>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>> asm_rewrite_tac [] >>
  rewrite_tac [INSERT_SUBSET,UNION_SUBSET] >>
  rpt conj_tac \\ TRY (fs [SUBSET_DEF] \\ NO_TAC) >>
  rw [] \\ fs [Q.SPECL[`T`,`Seq p1 p2`]flatten_def] >>
  rpt (pairarg_tac \\ fs []) >>
  rveq \\ fs [] \\ fs [] >>
  CCONTR_TAC \\ fs [] >>
  first_x_assum (qspec_then `{1}` mp_tac) \\
  fs [] \\ qexists_tac `Label n 1 0` \\ fs []
QED

Theorem flatten_preserves_handler_labels:
   ∀t m n p l x y.
   flatten t m n p = (l,x,y)
   ⇒
   stack_get_handler_labels n m ⊆
     sec_get_code_labels (Section n (append l))
Proof
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = FOO p`
  \\ simp[labPropsTheory.sec_get_code_labels_def]
  \\ Cases_on`p` \\ fs[] \\ rveq \\ fs[stack_get_handler_labels_def]
  >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ TRY(metis_tac[]))
  (* >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fsrw_tac[DNF_ss][]
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ metis_tac[]) *)
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[SUBSET_DEF, PULL_EXISTS, CaseEq"bool"] \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def,stack_get_handler_labels_def]
    \\ metis_tac[] )
QED

Theorem MAP_prog_to_section_preserves_handler_labels:
   ∀p.
    BIGUNION (set (MAP (λ(n,pp). stack_get_handler_labels n pp) p)) ⊆
    get_code_labels (MAP prog_to_section p)
Proof
  Induct \\ simp[FORALL_PROD]
  \\ simp[stack_to_labTheory.prog_to_section_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ simp[labPropsTheory.get_code_labels_cons, labPropsTheory.sec_get_code_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] \\ rw[]
  \\ old_drule flatten_preserves_handler_labels
  \\ rw[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
  \\ first_x_assum old_drule
  \\ rw[labPropsTheory.sec_get_code_labels_def]
  \\ metis_tac[]
QED

Theorem one_prog_section:
  IMAGE (λn. (n,1)) (set (MAP FST p)) ⊆
  get_code_labels (MAP prog_to_section p)
Proof
  fs [SUBSET_DEF,get_code_labels_def,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ fs [prog_to_section_def,EXISTS_PROD]
  \\ rw []
  \\ rename [`MEM (x1,y1) _`]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ pairarg_tac \\ fs [] \\ reverse (rw [])
  THEN1 fs [sec_get_code_labels_def]
  \\ Cases_on `y1` \\ fs [is_Seq_def]
  \\ qpat_x_assum `_ = _` mp_tac
  \\ once_rewrite_tac [flatten_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw[] \\ fs [] \\ fs [sec_get_code_labels_def]
QED

Theorem get_labels_MAP_prog_to_section_SUBSET_code_labels:
 ∀p. EVERY sec_labels_ok (MAP prog_to_section p) ∧
    stack_good_code_labels p elabs
   ⇒
    get_labels (MAP prog_to_section p) ⊆
    get_code_labels (MAP prog_to_section p) ∪
    IMAGE (λn. n,0) elabs ∪
    IMAGE (λn. n,1) elabs
Proof
  rw[stack_good_code_labels_def]>>
  old_drule get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma >>
  strip_tac >> match_mp_tac SUBSET_TRANS>>
  asm_exists_tac >> asm_rewrite_tac [] >> simp [] >>
  conj_tac THEN1 fs [SUBSET_DEF] >>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>> reverse (rw[])
  THEN1 (assume_tac one_prog_section \\ fs [SUBSET_DEF])
  THEN1 fs [SUBSET_DEF]
  \\ metis_tac[MAP_prog_to_section_preserves_handler_labels,
      prog_to_section_preserves_MAP_FST,SUBSET_UNION,SUBSET_TRANS]
QED

(* TODO: move these when the actual needed theorem is clearer...
  - e.g.: do we need a LIST_REL on the labels before/after each code
    table entry? or just a weaker BIGUNION?
    (I think the latter may be sufficient)
 *)
(* stack_names *)
Triviality get_code_labels_comp:
  !f p. complex_get_code_labels (stack_names$comp f p) = complex_get_code_labels p
Proof
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [get_code_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]
QED

Theorem stack_names_get_code_labels:
    LIST_REL (λcp p. complex_get_code_labels cp = complex_get_code_labels p)
  (MAP SND (stack_names$compile f prog)) (MAP SND prog)
Proof
  rw[LIST_REL_EL_EQN,stack_namesTheory.compile_def]>>
  fs[MAP_MAP_o,o_DEF,LAMBDA_PROD,stack_namesTheory.prog_comp_def]>>
  fs[EL_MAP]>>pairarg_tac>>fs[]>>
  metis_tac[get_code_labels_comp]
QED

(* stack_remove *)
Triviality get_code_labels_comp:
  !a b c p. get_code_labels (comp a b c p) SUBSET (stack_err_lab,0) INSERT get_code_labels p
Proof
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [get_code_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs [] \\
  TRY(rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
  metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[get_code_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,get_code_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
QED

Triviality init_stubs_labels:
  EVERY (λp. get_code_labels p SUBSET (set [(1n,0n);(start,0n)])) (MAP SND (init_stubs ggc mh k start))
Proof
  rpt(EVAL_TAC>>rw[]>>fs[])
QED

(* ---- stack_names  ----*)
Triviality stack_names_get_code_labels_comp:
  !f p. get_code_labels (stack_names$comp f p) = get_code_labels p
Proof
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [get_code_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]
QED

Triviality stack_names_stack_get_handler_labels_comp:
  !f p n.
  stack_get_handler_labels n (stack_names$comp f p) =
  stack_get_handler_labels n p
Proof
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [stack_get_handler_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]
QED

Triviality UNCURRY_PAIR_ETA:
  UNCURRY f = λ(p1,p2). f p1 p2
Proof
  fs[FUN_EQ_THM]
QED

(* TODO: Exported for now -- maybe using in backendProof *)
Theorem stack_names_stack_good_code_labels:
  ∀prog f. stack_good_code_labels prog elabs ⇒
  stack_good_code_labels (stack_names$compile f prog) elabs
Proof
  EVAL_TAC>>rw[]>>
  fs[GSYM LIST_TO_SET_MAP]>>
  fs[MAP_MAP_o,o_DEF,stack_namesTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
  fs[stack_names_stack_get_handler_labels_comp,stack_names_get_code_labels_comp]>>
  fs[UNCURRY_PAIR_ETA]
QED;

(* ---- stack_remove ---- *)
Triviality stack_remove_get_code_labels_comp:
  !a b c p.
  get_code_labels (comp a b c p) SUBSET (stack_err_lab,0) INSERT get_code_labels p
Proof
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [get_code_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs [] \\
  TRY(rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
  metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[get_code_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,get_code_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
QED

Triviality stack_remove_stack_get_handler_labels_comp:
  !a b c p m.
  stack_get_handler_labels m (comp a b c p) =
  stack_get_handler_labels m p
Proof
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs []
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[stack_get_handler_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
QED

Triviality stack_remove_init_code_labels:
  x ∈ get_code_labels (init_code ggc mh sp) ⇒ x = (1n,0n)
Proof
  rpt(EVAL_TAC>>rw[]>>fs[])
QED

Theorem stack_remove_stack_good_code_labels:
  ∀prog.
  MEM loc (MAP FST prog) ∧
  stack_good_code_labels prog elabs ⇒
  stack_good_code_labels (stack_remove$compile jump off ggc mh sp loc prog) elabs
Proof
  rw[]>>
  simp[stack_removeTheory.compile_def]>>
  fs[stack_good_code_labels_def]>>rw[]
  >- (
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]>>
    simp[SUBSET_DEF,stack_removeTheory.init_stubs_def,PULL_EXISTS]>>
    fs[get_code_labels_def,stack_removeTheory.halt_inst_def]>>
    rw[]>>fs[]
    >-
      metis_tac[stack_remove_init_code_labels]
    >>
      fs[MEM_MAP,EXISTS_PROD]>>metis_tac[])
  >>
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_removeTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
    simp[stack_remove_stack_get_handler_labels_comp]>>
    fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
    old_drule (stack_remove_get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      fs[stack_removeTheory.init_stubs_def,stack_removeTheory.stack_err_lab_def,EXISTS_PROD]
    >>
      metis_tac[]
QED;

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
Theorem stack_remove_stack_good_code_labels_incr:
  ∀prog.
  stack_err_lab ∈ elabs ∧
  stack_good_code_labels prog elabs ⇒
  stack_good_code_labels (MAP (prog_comp jump offset sp) prog) elabs
Proof
  rw[]>>
  fs[stack_good_code_labels_def]>>rw[]>>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_removeTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
  simp[stack_remove_stack_get_handler_labels_comp]>>
  fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
  drule (stack_remove_get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
  rw[]>>
  metis_tac[]
QED;

(* --- stack_alloc ---- *)
Triviality stack_alloc_get_code_labels_comp:
  !n m p pp mm.
  get_code_labels (FST (comp n m p)) ⊆ (gc_stub_location,0) INSERT get_code_labels p
Proof
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]>>metis_tac[]
QED

Triviality stack_alloc_stack_get_handler_labels_comp:
  !n m p pp mm.
  stack_get_handler_labels i (FST (comp n m p)) = stack_get_handler_labels i p
Proof
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[stack_get_handler_labels_def])
  \\ fs[stack_get_handler_labels_def]
QED

Triviality stack_alloc_init_code_labels:
  get_code_labels (word_gc_code c) = {}
Proof
  simp[stack_allocTheory.word_gc_code_def]>>
  EVAL_TAC>>
  EVERY_CASE_TAC>>fs[]>>
  rpt(EVAL_TAC>>rw[]>>fs[])
QED

Theorem stack_alloc_stack_good_code_labels:
  ∀prog c.
  stack_good_code_labels prog elabs ⇒
  stack_good_code_labels (stack_alloc$compile c prog) elabs
Proof
  simp[stack_allocTheory.compile_def]>>
  fs[stack_good_code_labels_def]>>rw[]
  >- (
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]>>
    simp[SUBSET_DEF,stack_allocTheory.stubs_def,PULL_EXISTS]>>
    simp[stack_alloc_init_code_labels])
  >>
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_allocTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
    simp[stack_alloc_stack_get_handler_labels_comp]>>
    fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
    old_drule (stack_alloc_get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      fs[stack_allocTheory.stubs_def]
    >>
      metis_tac[]
QED

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
Theorem stack_alloc_stack_good_code_labels_incr:
  ∀prog.
  gc_stub_location ∈ elabs ∧
  stack_good_code_labels prog elabs ⇒
  stack_good_code_labels (MAP prog_comp prog) elabs
Proof
  fs[stack_good_code_labels_def]>>rw[]>>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_allocTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
  simp[stack_alloc_stack_get_handler_labels_comp]>>
  fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
  drule (stack_alloc_get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
  rw[]>>
  metis_tac[]
QED

Theorem IN_get_code_labels_comp_top_lemma:
  !i q p_1 p_2.
    ((p_1,p_2) ∈ get_code_labels (stack_rawcall$comp i q) ==>
     ?k. (p_1,k) ∈ get_code_labels q /\
         (p_2 <> k ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)) /\
    ((p_1,p_2) ∈ get_code_labels (comp_top i q) ==>
     ?k. (p_1,k) ∈ get_code_labels q /\
         (p_2 <> k ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i))
Proof
  recInduct stack_rawcallTheory.comp_ind
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_rawcallTheory.comp_top_def] \\ fs []
  \\ simp [Once stack_rawcallTheory.comp_def] \\ fs []
  THEN1 (every_case_tac \\ fs [] \\ metis_tac [])
  THENL [all_tac,metis_tac [],metis_tac []]
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               (Seq (comp i p1) (comp i p2))`
  \\ fs [] THEN1 metis_tac []
  \\ drule stack_rawcallProofTheory.comp_seq_neq_IMP
  \\ strip_tac \\ rveq
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [stack_rawcallTheory.comp_seq_def]
  \\ fs [CaseEq"option",pair_case_eq]
  \\ Cases_on `dest_case (StackFree k) (Call NONE (INL dest) NONE)` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ Cases_on `lookup x1 i` \\ fs []
  \\ fs [stack_rawcallTheory.dest_case_def] \\ rveq
  \\ disch_then kall_tac
  \\ rw[] \\ fs [domain_lookup]
  \\ rpt (pop_assum mp_tac)
  \\ simp [Once stack_rawcallTheory.comp_def]
QED

Theorem IN_domain_collect_info:
  !prog f p_1.
    p_1 ∈ domain (collect_info prog f) ==>
    MEM p_1 (MAP FST prog) \/ p_1 IN domain f
Proof
  Induct \\ fs [stack_rawcallTheory.collect_info_def,FORALL_PROD]
  \\ rw [] \\ every_case_tac \\ fs []
  \\ first_x_assum drule \\ rw [] \\ fs []
QED

Theorem IN_get_code_labels_comp_top:
  (p_1,p_2) ∈ get_code_labels (comp_top (collect_info prog LN) q) ==>
  ?k. (p_1,k) ∈ get_code_labels q /\
      (p_2 <> k ==> p_2 = 1 /\ k = 0 /\ MEM p_1 (MAP FST prog))
Proof
  strip_tac
  \\ imp_res_tac IN_get_code_labels_comp_top_lemma
  \\ asm_exists_tac \\ fs []
  \\ rw [] \\ fs [] \\ rveq \\ fs []
  \\ drule IN_domain_collect_info \\ fs []
QED

Theorem stack_rawcall_stack_good_code_labels:
  stack_good_code_labels prog elabs ==>
  stack_good_code_labels (stack_rawcall$compile prog) elabs
Proof
  fs [stack_good_code_labels_def,stack_rawcallTheory.compile_def]
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ simp []
  \\ fs [stack_rawcallProofTheory.stack_get_handler_labels_comp]
  \\ fs [SUBSET_DEF,PULL_EXISTS,EXISTS_PROD,FORALL_PROD,MEM_MAP]
  \\ rw [] \\ drule IN_get_code_labels_comp_top \\ strip_tac
  \\ Cases_on `p_2 = k` THEN1 metis_tac []
  \\ fs [] \\ rveq \\ fs []
  \\ fs [MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

(* stack_to_lab *)
Theorem stack_to_lab_stack_good_code_labels:
  compile stack_conf data_conf max_heap sp offset prog = prog' ∧
  MEM InitGlobals_location (MAP FST prog) ∧
  stack_good_code_labels prog elabs ∧
  EVERY sec_labels_ok  prog' ⇒
  (* TODO: pretty sure this is only ever used with elabs = {} *)
  get_labels prog' ⊆ get_code_labels prog' ∪ IMAGE (λn. n,0) elabs ∪ IMAGE (λn. n,1) elabs
Proof
  rw[stack_to_labTheory.compile_def]>>
  match_mp_tac get_labels_MAP_prog_to_section_SUBSET_code_labels >>
  simp[]>>
  match_mp_tac stack_names_stack_good_code_labels>>
  match_mp_tac stack_remove_stack_good_code_labels>>
  rw[]
  >- (
    simp[stack_allocTheory.compile_def,MAP_MAP_o,UNCURRY,o_DEF,LAMBDA_PROD]>>
    fs[MEM_MAP,EXISTS_PROD,stack_rawcallTheory.compile_def]>>
    metis_tac[])
  >>
  match_mp_tac stack_alloc_stack_good_code_labels>>

  match_mp_tac stack_rawcall_stack_good_code_labels>>
  fs[]
QED;

Theorem stack_to_lab_stack_good_code_labels_incr:
  stack_err_lab ∈ elabs ∧
  gc_stub_location ∈ elabs ∧
  compile_no_stubs f jump offset sp prog = prog' ∧
  stack_good_code_labels prog elabs ∧
  EVERY sec_labels_ok  prog' ⇒
  get_labels prog' ⊆ get_code_labels prog' ∪ IMAGE (λn. n,0) elabs ∪ IMAGE (λn. n,1) elabs
Proof
  rw[compile_no_stubs_def]>>
  match_mp_tac get_labels_MAP_prog_to_section_SUBSET_code_labels >>
  simp[]>>
  match_mp_tac stack_names_stack_good_code_labels>>
  match_mp_tac stack_remove_stack_good_code_labels_incr>>
  simp[]>>
  match_mp_tac stack_alloc_stack_good_code_labels_incr>>
  simp[]
QED;

(* nonzero restricted code labels *)
Theorem nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels:
 ∀p. EVERY sec_labels_ok (MAP prog_to_section p) ∧
    stack_good_handler_labels p
    ⇒
    restrict_nonzero (get_labels (MAP prog_to_section p)) ⊆
    get_code_labels (MAP prog_to_section p)
Proof
  rw[]>>
  drule get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma >>
  strip_tac>>
  fs[stack_good_handler_labels_def]>>
  drule backendPropsTheory.restrict_nonzero_SUBSET_left>>
  strip_tac>>
  drule backendPropsTheory.restrict_nonzero_right_union>>
  qmatch_goalsub_abbrev_tac`a ⊆ b ∪ c`>>
  qsuff_tac` c ⊆ b`
  >- (simp[SUBSET_DEF]>> metis_tac[]) >>
  unabbrev_all_tac>>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  metis_tac[MAP_prog_to_section_preserves_handler_labels,one_prog_section,
      SUBSET_UNION,SUBSET_TRANS]
QED;

Theorem stack_names_stack_good_handler_labels:
  ∀prog f. stack_good_handler_labels prog ⇒
  stack_good_handler_labels (stack_names$compile f prog)
Proof
  simp[stack_namesTheory.compile_def,stack_good_handler_labels_def,MAP_MAP_o,o_DEF]>>
  simp[LAMBDA_PROD,stack_namesTheory.prog_comp_def]>>
  rw[]>>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,LAMBDA_PROD,stack_names_get_code_labels_comp]>>
  fs[stack_names_stack_get_handler_labels_comp]
QED;

Theorem restrict_nonzero_union:
  restrict_nonzero (A ∪ B) = restrict_nonzero A ∪ restrict_nonzero B
Proof
  rw[backendPropsTheory.restrict_nonzero_def,EXTENSION]>>
  metis_tac[]
QED;

Theorem restrict_nonzero_IN:
  x ∈ restrict_nonzero s ⇔ x ∈ s ∧ SND x ≠ 0
Proof
  EVAL_TAC>>simp[]
QED;

Theorem stack_good_handler_labels_append:
  stack_good_handler_labels xs ∧
  stack_good_handler_labels ys ⇒
  stack_good_handler_labels (xs ++ ys)
Proof
  simp[stack_good_handler_labels_def,restrict_nonzero_union]>>
  rw[]>>
  fs [SUBSET_DEF] >>
  metis_tac []
QED;

Theorem stack_remove_stack_good_handler_labels_incr:
  ∀prog.
  stack_good_handler_labels prog ⇒
  stack_good_handler_labels (MAP (prog_comp jump offset sp) prog)
Proof
  simp[stack_good_handler_labels_def]>>
  rw[]>>
  simp[MAP_MAP_o,o_DEF,stack_removeTheory.prog_comp_def,LAMBDA_PROD]>>
  simp[stack_remove_stack_get_handler_labels_comp]>>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
  qmatch_asmsub_abbrev_tac`A ⊆ B`>>
  qmatch_goalsub_abbrev_tac`C ⊆ D`>>
  qsuff_tac`C ⊆ A`
  >-
    (unabbrev_all_tac>>metis_tac[SUBSET_UNION,SUBSET_TRANS])
  >>
  unabbrev_all_tac>>
  simp[backendPropsTheory.restrict_nonzero_BIGUNION]>>
  simp[BIGUNION_IMAGE_set_SUBSET,MEM_MAP,SUBSET_DEF]>>
  simp[PULL_FORALL,PULL_EXISTS]>>rw[]>>
  qexists_tac`y`>>simp[]>>
  fs[restrict_nonzero_IN]>>
  pairarg_tac>>fs[]>>
  drule(stack_remove_get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
  Cases_on`x'`>>simp[]>>
  rw[]>>fs[]
QED;

Theorem stack_remove_stack_good_handler_labels:
  ∀prog.
  stack_good_handler_labels prog ⇒
  stack_good_handler_labels (stack_remove$compile jump off ggc mh sp loc prog)
Proof
  rw[]>>
  simp[stack_removeTheory.compile_def]>>
  match_mp_tac stack_good_handler_labels_append>>rw[]
  >-
    (simp[stack_good_handler_labels_def]>>
    simp[stack_removeTheory.init_stubs_def,get_code_labels_def,stack_removeTheory.halt_inst_def,restrict_nonzero_union]>>
    qmatch_goalsub_abbrev_tac` A ⊆ _`>>
    qsuff_tac`A = {}`
    >-
      simp[backendPropsTheory.restrict_nonzero_def,SUBSET_DEF]
    >>
    simp[Abbr`A`,EXTENSION,backendPropsTheory.restrict_nonzero_def]>>
    rw[]>>
    CCONTR_TAC>>fs[]>>
    drule stack_remove_init_code_labels>>
    metis_tac[SND])
  >>
    metis_tac[stack_remove_stack_good_handler_labels_incr]
QED;

Theorem stack_alloc_stack_good_handler_labels_incr:
  ∀prog.
  stack_good_handler_labels prog ⇒
  stack_good_handler_labels (MAP prog_comp prog)
Proof
  fs[stack_good_handler_labels_def]>>rw[]>>
  fs[backendPropsTheory.restrict_nonzero_BIGUNION]>>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_allocTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
  simp[stack_alloc_stack_get_handler_labels_comp]>>
  fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
  first_x_assum match_mp_tac>>
  qexists_tac`y`>>simp[]>>
  drule (MATCH_MP backendPropsTheory.restrict_nonzero_mono (stack_alloc_get_code_labels_comp |> SPEC_ALL) |> SIMP_RULE std_ss [SUBSET_DEF])>>
  simp[backendPropsTheory.restrict_nonzero_def]>>
  Cases_on`x`>>simp[]>>
  metis_tac[]
QED;

Theorem stack_alloc_stack_good_handler_labels:
  ∀prog c.
  stack_good_handler_labels prog ⇒
  stack_good_handler_labels (stack_alloc$compile c prog)
Proof
  rw[stack_allocTheory.compile_def]>>
  match_mp_tac stack_good_handler_labels_append>>rw[]
  >-
    (simp[stack_good_handler_labels_def,GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]>>
    simp[SUBSET_DEF,stack_allocTheory.stubs_def,PULL_EXISTS]>>
    simp[stack_alloc_init_code_labels]>>
    simp[backendPropsTheory.restrict_nonzero_def])
  >>
    metis_tac[stack_alloc_stack_good_handler_labels_incr]
QED

Theorem stack_rawcall_stack_good_handler_labels:
  stack_good_handler_labels prog ==>
  stack_good_handler_labels (stack_rawcall$compile prog)
Proof
  rw[stack_rawcallTheory.compile_def]
  \\ fs[stack_good_handler_labels_def,GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ fs [stack_rawcallProofTheory.stack_get_handler_labels_comp]
  \\ fs [SUBSET_DEF,MEM_MAP,EXISTS_PROD]
  \\ fs [restrict_nonzero_IN,MEM_MAP,PULL_EXISTS]
  \\ fs [FORALL_PROD] \\ rw []
  \\ drule IN_get_code_labels_comp_top \\ strip_tac
  \\ Cases_on `p_2 ≠ k` \\ fs [] \\ rveq \\ fs []
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ metis_tac []
QED

Theorem stack_to_lab_stack_good_handler_labels:
  compile stack_conf data_conf max_heap sp offset prog = prog' ∧
  stack_good_handler_labels prog ∧
  EVERY sec_labels_ok  prog' ⇒
  restrict_nonzero (get_labels prog') ⊆ get_code_labels prog'
Proof
  rw[stack_to_labTheory.compile_def]>>
  match_mp_tac nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels >>
  simp[]>>
  match_mp_tac stack_names_stack_good_handler_labels>>
  match_mp_tac stack_remove_stack_good_handler_labels>>
  match_mp_tac stack_alloc_stack_good_handler_labels>>
  match_mp_tac stack_rawcall_stack_good_handler_labels>>
  fs[]
QED

Theorem stack_to_lab_stack_good_handler_labels_incr:
  compile_no_stubs f jump offset sp prog = prog' ∧
  stack_good_handler_labels prog ∧
  EVERY sec_labels_ok prog' ⇒
  restrict_nonzero (get_labels prog') ⊆ get_code_labels prog'
Proof
  rw[compile_no_stubs_def]>>
  match_mp_tac nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels >>
  simp[]>>
  match_mp_tac stack_names_stack_good_handler_labels>>
  match_mp_tac stack_remove_stack_good_handler_labels_incr>>
  match_mp_tac stack_alloc_stack_good_handler_labels_incr>>
  simp[]
QED

(*** no_shmemop ***)

Theorem stack_rawcall_comp_no_shmemop:
  ∀i p. no_shmemop p ⇒ no_shmemop (comp i p)
Proof
  recInduct stack_rawcallTheory.comp_ind>>rw[]
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_rawcallTheory.comp_def]
  \\ fs [stack_rawcallTheory.comp_seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [no_shmemop_def])
  >>fs[no_shmemop_def]
QED

Theorem stack_rawcall_comp_top_no_shmemop:
  ∀p. no_shmemop p ⇒ no_shmemop (comp_top i p)
Proof
  Induct>>
  rw[stack_rawcallTheory.comp_top_def,no_shmemop_def]>>
  irule stack_rawcall_comp_no_shmemop>>fs[no_shmemop_def]
QED

Theorem stack_rawcall_compile_no_shmemop:
  ∀prog. EVERY (\(a,p). no_shmemop p) prog ⇒
      EVERY (\(a,p). no_shmemop p) (compile prog)
Proof
  Induct>>rw[]>>
  simp[stack_rawcallTheory.compile_def]>>
  rpt (pairarg_tac>>fs[])>>
  drule stack_rawcall_comp_top_no_shmemop>>
  qmatch_asmsub_abbrev_tac ‘comp_top i _’>>
  disch_then $ qspec_then ‘i’ assume_tac>>gvs[]>>
  fs[EVERY_MEM]>>rpt strip_tac>>
  fs[MEM_MAP]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>rename1 ‘MEM (a',b') prog’>>
  rveq>>fs[]>>
  irule stack_rawcall_comp_top_no_shmemop>>
  first_x_assum $ qspec_then ‘(a',b')’ assume_tac>>gvs[]
QED

Theorem stack_alloc_comp_no_shmemop:
  ∀n m p. no_shmemop p ⇒ no_shmemop (FST (comp n m p))
Proof
  recInduct comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [no_shmemop_def])
  >>fs[no_shmemop_def]
QED

Theorem stack_alloc_prog_comp_no_shmemop:
  ∀prog.
  EVERY (\(a,p). no_shmemop p) prog ⇒
  EVERY (\(a,p). no_shmemop p) (MAP prog_comp prog)
Proof
  Induct>>fs[prog_comp_def]>>rpt strip_tac>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[prog_comp_def]>>gvs[]>>
  irule stack_alloc_comp_no_shmemop>>fs[]
QED

Theorem stack_alloc_compile_no_shmemop:
  EVERY (λ(a,p). no_shmemop p) prog ⇒
  EVERY (λ(a,p). no_shmemop p) (stack_alloc_compile data prog)
Proof
  rw[stack_allocTheory.compile_def]>-
   (EVAL_TAC>>every_case_tac>>fs[no_shmemop_def])>>
  irule stack_alloc_prog_comp_no_shmemop>>fs[]
QED

Theorem upshift_no_shmemop[simp]:
  ∀k n. no_shmemop (upshift k n)
Proof
  recInduct stack_removeTheory.upshift_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.upshift_def] \\ rw []
  \\ fs [no_shmemop_def]
QED

Theorem downshift_no_shmemop[simp]:
  ∀k n. no_shmemop (downshift k n)
Proof
  recInduct stack_removeTheory.downshift_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.downshift_def] \\ rw []
  \\ fs [no_shmemop_def]
QED

Theorem stack_free_no_shmemop[simp]:
  ∀k n. no_shmemop (stack_free k n)
Proof
  recInduct stack_removeTheory.stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.stack_free_def] \\ rw []
  \\ fs [no_shmemop_def,stack_removeTheory.single_stack_free_def]
QED

Theorem stack_alloc_no_shmemop[simp]:
  ∀jump k n. no_shmemop (stack_alloc jump k n)
Proof
  recInduct stack_removeTheory.stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.stack_alloc_def] \\ rw []>>
  fs [no_shmemop_def,stack_removeTheory.single_stack_alloc_def]>>
  IF_CASES_TAC >> fs [no_shmemop_def,stack_removeTheory.halt_inst_def]
QED

Theorem stack_remove_comp_no_shmemop:
  ∀jump off k p. no_shmemop p ⇒ no_shmemop (comp jump off k p)
Proof
  recInduct stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_removeTheory.comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [no_shmemop_def])>>
  fs[no_shmemop_def,stackLangTheory.list_Seq_def]
  >- fs[no_shmemop_def,stackLangTheory.list_Seq_def,
        stack_removeTheory.copy_loop_def,
        stack_removeTheory.copy_each_def]
  >- fs[stack_removeTheory.stack_store_def,no_shmemop_def]
  >- fs[stack_removeTheory.stack_load_def,no_shmemop_def]
QED

Theorem stack_remove_prog_comp_no_shmemop:
  ∀p. no_shmemop p ⇒ no_shmemop (SND (prog_comp jump off k (n,p)))
Proof
  Induct>>fs[stack_removeTheory.prog_comp_def]>>rpt strip_tac>>
  irule stack_remove_comp_no_shmemop>>fs[]
QED

Theorem stack_remove_compile_no_shmemop:
  EVERY (λ(a,p). no_shmemop p) prog ⇒
  EVERY (λ(a,p). no_shmemop p) (stack_remove_compile jump offset gckind mh sp loc prog)
Proof
  rw[stack_removeTheory.compile_def]>-
   (EVAL_TAC>>every_case_tac>>fs[no_shmemop_def])>>
  fs[EVERY_MEM]>>rpt strip_tac>>
  pairarg_tac>>fs[MEM_MAP]>>
  rpt (pairarg_tac>>fs[])>>
  last_x_assum $ qspec_then ‘y’ assume_tac>>gvs[]>>
  rpt (pairarg_tac>>fs[])>>
  ‘p = SND (prog_comp jump offset sp y)’ by gvs[]>>
  gvs[]>>
  irule stack_remove_prog_comp_no_shmemop>>fs[]
QED

Theorem stack_names_comp_no_shmemop:
  ∀f p. no_shmemop p ⇒ no_shmemop (stack_names$comp f p)
Proof
  recInduct stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [no_shmemop_def])
  >>fs[no_shmemop_def]
QED

Theorem stack_names_prog_comp_no_shmemop:
  ∀prog.
  EVERY (\(a,p). no_shmemop p) prog ⇒
  EVERY (\(a,p). no_shmemop p) (MAP (prog_comp f) prog)
Proof
  Induct>>fs[stack_namesTheory.prog_comp_def]>>rpt strip_tac>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[stack_namesTheory.prog_comp_def]>>gvs[]>>
  irule stack_names_comp_no_shmemop>>fs[]
QED

Theorem stack_names_compile_no_shmemop:
  EVERY (λ(a,p). no_shmemop p) prog ⇒
  EVERY (λ(a,p). no_shmemop p) (stack_names_compile names prog)
Proof
  rw[stack_namesTheory.compile_def]>>
  irule stack_names_prog_comp_no_shmemop>>fs[]
QED

Theorem flatten_no_share_mem_inst:
  ∀t p n m.
      no_shmemop p ⇒
      EVERY (λln. ∀op re a inst len. ln ≠ Asm (ShareMem op re a) inst len)
            (append (FST (flatten t p n m)))
Proof
  recInduct flatten_ind>>rw[]>>
  Cases_on ‘p’>>simp[Once flatten_def]>>fs[no_shmemop_def]>>
  every_case_tac>>fs[]>>
  rpt (pairarg_tac>>fs[])>>
  TRY (Cases_on ‘s’>>fs[compile_jump_def,no_shmemop_def])>>
  gvs[no_shmemop_def]>>
  rpt (IF_CASES_TAC>>fs[])
QED

Theorem asm_fetch_aux_no_share_mem_inst_CONS:
  ∀xs.
  EVERY (λln. ∀op re a inst len. ln ≠ Asm (ShareMem op re a) inst len) xs ∧
  no_share_mem_inst ls ⇒
  no_share_mem_inst (Section k xs::ls)
Proof
  Induct>>rw[no_share_mem_inst_def, asm_fetch_aux_def]>>
  IF_CASES_TAC>>fs[]>-fs[no_share_mem_inst_def]>>
  IF_CASES_TAC>>fs[no_share_mem_inst_def]
QED

Theorem prog_to_section_no_share_mem_inst:
  ∀prog. EVERY (λ(a,p). no_shmemop p) prog ⇒
         no_share_mem_inst (MAP prog_to_section prog)
Proof
  Induct>>rw[]>-fs[no_share_mem_inst_def,asm_fetch_aux_def]>>
  pairarg_tac>>fs[]>>
  rewrite_tac[prog_to_section_def]>>
  Cases_on ‘flatten T p a (next_lab p 2)’>>rename1 ‘(lines,r)’>>
  PairCases_on ‘r’>>fs[]>>
  ‘EVERY (λln. ∀op re a inst len. ln ≠ Asm (ShareMem op re a) inst len)
   (append lines)’
    by (‘lines = FST (flatten T p a (next_lab p 2))’ by gvs[]>>gvs[]>>
        irule flatten_no_share_mem_inst>>fs[])>>
  irule asm_fetch_aux_no_share_mem_inst_CONS>>
  fs[]
QED

Theorem compile_no_share_mem_inst:
  ∀prog prog'.
  EVERY (\(a,p). no_shmemop p) prog ∧
  compile stack_conf data_conf max_heap sp offset prog = prog' ==>
  labProps$no_share_mem_inst prog'
Proof
  rw[compile_def]>>
  irule prog_to_section_no_share_mem_inst>>
  irule stack_names_compile_no_shmemop>>
  irule stack_remove_compile_no_shmemop>>
  irule stack_alloc_compile_no_shmemop>>
  irule stack_rawcall_compile_no_shmemop>>fs[]
QED

Theorem stack_remove_prog_comp_no_shmemop_MAP:
  EVERY (\(a,p). no_shmemop p) prog ⇒
  EVERY (\(a,p). no_shmemop p) (MAP (prog_comp jump offset sp) prog)
Proof
  rw[EVERY_MEM]>>
  pairarg_tac>>fs[MEM_MAP]>>
  first_x_assum $ qspec_then ‘y’ assume_tac>>gvs[]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  ‘p = SND (prog_comp jump offset sp (a'',p''))’ by gvs[]>>
  gvs[]>>irule stack_remove_prog_comp_no_shmemop>>fs[]
QED

Theorem compile_no_stubs_no_share_mem_inst:
  EVERY (\(a,p). no_shmemop p) prog ∧
  compile_no_stubs f jump offset sp prog = prog' ==>
  labProps$no_share_mem_inst prog'
Proof
  rw[compile_no_stubs_def]>>
  irule prog_to_section_no_share_mem_inst>>
  irule stack_names_compile_no_shmemop>>
  irule stack_remove_prog_comp_no_shmemop_MAP>>
  irule stack_alloc_prog_comp_no_shmemop>>fs[]
QED

(*** no_install ***)

Theorem stack_rawcall_comp_no_install:
  ∀i p. no_install p ⇒ no_install (comp i p)
Proof
  recInduct stack_rawcallTheory.comp_ind>>rw[]
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_rawcallTheory.comp_def]
  \\ fs [stack_rawcallTheory.comp_seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [stackPropsTheory.no_install_def])
  >>fs[stackPropsTheory.no_install_def]
QED

Theorem stack_rawcall_comp_top_no_install:
  ∀p. no_install p ⇒ no_install (comp_top i p)
Proof
  Induct>>
  rw[stack_rawcallTheory.comp_top_def,stackPropsTheory.no_install_def]>>
  irule stack_rawcall_comp_no_install>>
  fs[stackPropsTheory.no_install_def]
QED

Theorem stack_rawcall_compile_no_install:
  ∀prog. EVERY (\(a,p). no_install p) prog ⇒
      EVERY (\(a,p). no_install p) (compile prog)
Proof
  Induct>>rw[]>>
  simp[stack_rawcallTheory.compile_def]>>
  rpt (pairarg_tac>>fs[])>>
  drule stack_rawcall_comp_top_no_install>>
  qmatch_asmsub_abbrev_tac ‘comp_top i _’>>
  disch_then $ qspec_then ‘i’ assume_tac>>gvs[]>>
  fs[EVERY_MEM]>>rpt strip_tac>>
  fs[MEM_MAP]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>rename1 ‘MEM (a',b') prog’>>
  rveq>>fs[]>>
  irule stack_rawcall_comp_top_no_install>>
  first_x_assum $ qspec_then ‘(a',b')’ assume_tac>>gvs[]
QED

Theorem stack_alloc_comp_no_install:
  ∀n m p. no_install p ⇒ no_install (FST (comp n m p))
Proof
  recInduct comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [stackPropsTheory.no_install_def])
  >>fs[stackPropsTheory.no_install_def]
QED

Theorem stack_alloc_prog_comp_no_install:
  ∀prog.
  EVERY (\(a,p). no_install p) prog ⇒
  EVERY (\(a,p). no_install p) (MAP prog_comp prog)
Proof
  Induct>>fs[prog_comp_def]>>rpt strip_tac>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[prog_comp_def]>>gvs[]>>
  irule stack_alloc_comp_no_install>>fs[]
QED

Theorem stack_alloc_compile_no_install:
  EVERY (λ(a,p). no_install p) prog ⇒
  EVERY (λ(a,p). no_install p) (stack_alloc_compile data prog)
Proof
  rw[stack_allocTheory.compile_def]>-
   (EVAL_TAC>>every_case_tac>>fs[stackPropsTheory.no_install_def])>>
  irule stack_alloc_prog_comp_no_install>>fs[]
QED

Theorem upshift_no_install[simp]:
  ∀k n. no_install (upshift k n)
Proof
  recInduct stack_removeTheory.upshift_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.upshift_def] \\ rw []
  \\ fs [stackPropsTheory.no_install_def]
QED

Theorem downshift_no_install[simp]:
  ∀k n. no_install (downshift k n)
Proof
  recInduct stack_removeTheory.downshift_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.downshift_def] \\ rw []
  \\ fs [stackPropsTheory.no_install_def]
QED

Theorem stack_free_no_install[simp]:
  ∀k n. no_install (stack_free k n)
Proof
  recInduct stack_removeTheory.stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.stack_free_def] \\ rw []
  \\ fs [stackPropsTheory.no_install_def,
         stack_removeTheory.single_stack_free_def]
QED

Theorem stack_alloc_no_install[simp]:
  ∀jump k n. no_install (stack_alloc jump k n)
Proof
  recInduct stack_removeTheory.stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_removeTheory.stack_alloc_def] \\ rw []>>
  fs [stackPropsTheory.no_install_def,
      stack_removeTheory.single_stack_alloc_def]>>
  IF_CASES_TAC >>
  fs [stackPropsTheory.no_install_def,stack_removeTheory.halt_inst_def]
QED

Theorem stack_remove_comp_no_install:
  ∀jump off k p. no_install p ⇒ no_install (comp jump off k p)
Proof
  recInduct stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_removeTheory.comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [stackPropsTheory.no_install_def])>>
  fs[stackPropsTheory.no_install_def,
     stackLangTheory.list_Seq_def]
  >- fs[stackPropsTheory.no_install_def,
        stackLangTheory.list_Seq_def,
        stack_removeTheory.copy_loop_def,
        stack_removeTheory.copy_each_def]
  >- fs[stack_removeTheory.stack_store_def,stackPropsTheory.no_install_def]
  >- fs[stack_removeTheory.stack_load_def,stackPropsTheory.no_install_def]
QED

Theorem stack_remove_prog_comp_no_install:
  ∀p. no_install p ⇒ no_install (SND (prog_comp jump off k (n,p)))
Proof
  Induct>>fs[stack_removeTheory.prog_comp_def]>>rpt strip_tac>>
  irule stack_remove_comp_no_install>>fs[]
QED

Theorem stack_remove_compile_no_install:
  EVERY (λ(a,p). no_install p) prog ⇒
  EVERY (λ(a,p). no_install p) (stack_remove_compile jump offset gckind mh sp loc prog)
Proof
  rw[stack_removeTheory.compile_def]>-
   (EVAL_TAC>>every_case_tac>>fs[stackPropsTheory.no_install_def])>>
  fs[EVERY_MEM]>>rpt strip_tac>>
  pairarg_tac>>fs[MEM_MAP]>>
  rpt (pairarg_tac>>fs[])>>
  last_x_assum $ qspec_then ‘y’ assume_tac>>gvs[]>>
  rpt (pairarg_tac>>fs[])>>
  ‘p = SND (prog_comp jump offset sp y)’ by gvs[]>>
  gvs[]>>
  irule stack_remove_prog_comp_no_install>>fs[]
QED

Theorem stack_names_comp_no_install:
  ∀f p. no_install p ⇒ no_install (stack_names$comp f p)
Proof
  recInduct stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [stackPropsTheory.no_install_def])
  >>fs[stackPropsTheory.no_install_def]
QED

Theorem stack_names_prog_comp_no_install:
  ∀prog.
  EVERY (\(a,p). no_install p) prog ⇒
  EVERY (\(a,p). no_install p) (MAP (prog_comp f) prog)
Proof
  Induct>>fs[stack_namesTheory.prog_comp_def]>>rpt strip_tac>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[stack_namesTheory.prog_comp_def]>>gvs[]>>
  irule stack_names_comp_no_install>>fs[]
QED

Theorem stack_names_compile_no_install:
  EVERY (λ(a,p). no_install p) prog ⇒
  EVERY (λ(a,p). no_install p) (stack_names_compile names prog)
Proof
  rw[stack_namesTheory.compile_def]>>
  irule stack_names_prog_comp_no_install>>fs[]
QED

Theorem flatten_no_install:
  ∀t p n m.
      no_install p ⇒
      EVERY (λln. ∀w bytes l. ln ≠ LabAsm Install w bytes l)
            (append (FST (flatten t p n m)))
Proof
  recInduct flatten_ind>>rw[]>>
  Cases_on ‘p’>>simp[Once flatten_def]>>
  fs[stackPropsTheory.no_install_def]>>
  every_case_tac>>fs[]>>
  rpt (pairarg_tac>>fs[])>>
  TRY (Cases_on ‘s’>>fs[compile_jump_def,no_install_def])>>
  gvs[stackPropsTheory.no_install_def]>>
  rpt (IF_CASES_TAC>>fs[])
QED

Theorem asm_fetch_aux_no_install_CONS:
  ∀xs.
  EVERY (λln. ∀w bytes l. ln ≠ LabAsm Install w bytes l) xs ∧
  no_install ls ⇒
  no_install (Section k xs::ls)
Proof
  Induct>>rw[labPropsTheory.no_install_def, asm_fetch_aux_def]>>
  IF_CASES_TAC>>fs[]>-fs[labPropsTheory.no_install_def]>>
  IF_CASES_TAC>>fs[labPropsTheory.no_install_def]
QED

Theorem prog_to_section_no_install:
  ∀prog. EVERY (λ(a,p). no_install p) prog ⇒
         no_install (MAP prog_to_section prog)
Proof
  Induct>>rw[]>-fs[labPropsTheory.no_install_def,asm_fetch_aux_def]>>
  pairarg_tac>>fs[]>>
  rewrite_tac[prog_to_section_def]>>
  Cases_on ‘flatten T p a (next_lab p 2)’>>rename1 ‘(lines,r)’>>
  PairCases_on ‘r’>>fs[]>>
  ‘EVERY (λln. ∀w bytes l. ln ≠ LabAsm Install w bytes l)
   (append lines)’
    by (‘lines = FST (flatten T p a (next_lab p 2))’ by gvs[]>>gvs[]>>
        irule flatten_no_install>>fs[])>>
  irule asm_fetch_aux_no_install_CONS>>
  fs[]
QED

Theorem stack_to_lab_compile_no_install:
  ∀prog prog'.
  EVERY (\(a,p). no_install p) prog ∧
  compile stack_conf data_conf max_heap sp offset prog = prog' ==>
  labProps$no_install prog'
Proof
  rw[compile_def]>>
  irule prog_to_section_no_install>>
  irule stack_names_compile_no_install>>
  irule stack_remove_compile_no_install>>
  irule stack_alloc_compile_no_install>>
  irule stack_rawcall_compile_no_install>>fs[]
QED

val _ = export_theory();
