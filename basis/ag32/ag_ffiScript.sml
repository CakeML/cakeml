open preamble printFFITheory PrinterProofTheory

val _ = new_theory"ag_ffi";

val ag_ffi_oracle_def = Define `
  ag_ffi_oracle =
    \name st conf bytes.
     if name = "print" then
       case ffi_print conf bytes st of
       | SOME(FFIreturn bytes st) => Oracle_return st bytes
       | SOME FFIdiverge => Oracle_final FFI_diverged
       | _ => Oracle_final FFI_failed
     else Oracle_final FFI_failed`;

val ag_ffi_def = Define `
  ag_ffi =
    <| oracle := ag_ffi_oracle
     ; ffi_state := ""
     ; io_events := [] |>`;

val ag_proj1_def = Define `
  ag_proj1 = (λst.
    FEMPTY |++ (mk_proj1 print_ffi_part st))`;

val ag_proj2_def = Define `
  ag_proj2 = [mk_proj2 print_ffi_part]`;

val ag_proj1_print = Q.store_thm("ag_proj1_print",
  `ag_proj1 ffi ' "print" = Str ffi`, EVAL_TAC);

val PRINTER_precond = Q.prove(
  `(PRINTER ls) {FFI_part (Str ls) (mk_ffi_next print_ffi_part)
           (MAP FST (SND(SND print_ffi_part))) events}`,
  rw[PRINTER_def,printFFITheory.print_ffi_part_def,
     cfHeapsBaseTheory.IOx_def,
     cfHeapsBaseTheory.IO_def,
     set_sepTheory.SEP_EXISTS_THM,
     set_sepTheory.SEP_CLAUSES,
     set_sepTheory.one_def]);

fun mk_main_call s =
  ``(Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val ag_prog_spec_def = Define`
  ag_prog_spec fv post ⇔
    ∃out.
    app (ag_proj1, ag_proj2) fv [Conv NONE []]
      (PRINTER "")
      (POSTv uv. &UNIT_TYPE () uv * PRINTER out) ∧
    post out`;

val RTC_call_FFI_rel_ag_ffi_IMP = Q.store_thm("RTC_call_FFI_rel_ag_ffi_IMP",
  `∀s1 s2.
    call_FFI_rel^* s1 s2 ⇒
      s1.oracle = ag_ffi_oracle ⇒
      (∃outs. s1.io_events = MAP (λout. IO_event "print" (MAP (n2w o ORD) out) []) outs ∧
              s1.ffi_state = CONCAT outs) ⇒
      (∃outs. s2.io_events = MAP (λout. IO_event "print" (MAP (n2w o ORD) out) []) outs ∧
              s2.ffi_state = CONCAT outs)`,
  HO_MATCH_MP_TAC RTC_INDUCT
  \\ rw[]
  \\ fs[evaluatePropsTheory.call_FFI_rel_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ Cases_on `n = ""` \\ fs [] THEN1 (rveq \\ fs [PULL_EXISTS] \\ metis_tac[])
  \\ fs[CaseEq"oracle_result", CaseEq"bool"]
  \\ rw[] \\ fs[PULL_EXISTS]
  \\ fs[ag_ffi_oracle_def, CaseEq"bool", CaseEq"option", CaseEq"ffi_result"]
  \\ fs[ffi_print_def, NULL_EQ]
  \\ rw[] \\ fs[]
  \\ first_x_assum(qspec_then`outs ++ [MAP (CHR o w2n) conf]`mp_tac)
  \\ simp[MAP_MAP_o, n2w_ORD_CHR_w2n]);

val ag_prog_spec_semantics_prog = Q.store_thm("ag_prog_spec_semantics_prog",
  `∀fname fv.
     ML_code env1 (init_state ag_ffi) prog NONE env2 st2 ==>
     lookup_var fname env2 = SOME fv ==>
     ag_prog_spec fv Q ==>
     (?h1 h2. SPLIT (st2heap (ag_proj1, ag_proj2) st2) (h1,h2) /\ (PRINTER "") h1)
   ==>
   ∃outs.
     semantics_prog (init_state ag_ffi) env1
       (SNOC ^main_call prog)
       (Terminate Success
         (MAP (λout. IO_event "print" (MAP (n2w o ORD) out) []) outs)) /\
     Q (FLAT outs)`,
  rw[ag_prog_spec_def]
  \\ drule (GEN_ALL cfMainTheory.call_main_thm2)
  \\ rpt(disch_then drule)
  \\ disch_then (qspecl_then [`h2`, `h1`] mp_tac)
  \\ impl_keep_tac
  >- (
    rw[PRINTER_def]
    \\ rw[cfMainTheory.FFI_part_hprop_def,
          cfHeapsBaseTheory.IOx_def,
          cfHeapsBaseTheory.IO_def,
          print_ffi_part_def,
          set_sepTheory.SEP_EXISTS_THM,
          set_sepTheory.SEP_CLAUSES,
          set_sepTheory.one_def]
      \\ rw[] )
  \\ rw[]
  \\ drule RTC_call_FFI_rel_ag_ffi_IMP
  \\ impl_tac >- (EVAL_TAC \\ rw[])
  \\ rw[] \\ fs[]
  \\ asm_exists_tac \\ rw[]
  \\ fs[PRINTER_def,
        cfHeapsBaseTheory.IO_def,
        cfHeapsBaseTheory.IOx_def,
        print_ffi_part_def,
        set_sepTheory.SEP_EXISTS_THM,
        set_sepTheory.SEP_CLAUSES]
  \\ qmatch_assum_abbrev_tac`one ffip _`
  \\ fs[set_sepTheory.one_def]
  \\ `ffip ∈ (st2heap (ag_proj1,ag_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
  \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap, Abbr`ffip`,
        cfStoreTheory.ffi2heap_def]
  \\ pop_assum mp_tac \\ rw[]
  \\ fs[ag_proj1_print, FLOOKUP_DEF] \\ rw[]);

val sets_thm = save_thm("sets_thm",PRINTER_precond);

val ag_ffi_length_thms = save_thm("ag_ffi_length_thms", LIST_CONJ [ffi_print_length]);

val ag_ffi_part_defs = save_thm("ag_ffi_part_defs", LIST_CONJ [print_ffi_part_def]);

val SPLIT_exists = Q.store_thm ("SPLIT_exists",
  `A s /\ s ⊆ C
    ==> (?h1 h2. SPLIT C (h1, h2) /\ A h1)`,
  rw[]
  \\ qexists_tac `s` \\ qexists_tac `C DIFF s`
  \\ cfHeapsBaseLib.SPLIT_TAC);

(*

val oracle_parts = Q.store_thm("oracle_parts",
  `!st. st.ffi.oracle = ag_ffi_oracle /\
       MEM (ns, u) ag_proj2 /\ MEM m ns /\ u m conf bytes (ag_proj1 x ' m) = SOME (FFIreturn new_bytes w)
    ==> (?y. st.ffi.oracle m x conf bytes = Oracle_return y new_bytes /\ ag_proj1 x
 |++ MAP (\n. (n,w)) ns = ag_proj1 y)`,
  simp[basis_proj2_def,basis_proj1_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[cfHeapsBaseTheory.mk_proj1_def,
        cfHeapsBaseTheory.mk_proj2_def,
        basis_ffi_oracle_def,basis_ffi_part_defs]
  \\ rw[] \\ fs[FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM]
  \\ TRY (
     CASE_TAC \\ fs[cfHeapsBaseTheory.mk_ffi_next_def]
     \\ CASE_TAC \\ fs[fmap_eq_flookup,FLOOKUP_UPDATE]
     \\ rw[] )
  \\ TRY (
      fs[ffi_exit_def] \\ NO_TAC)
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]);

(* TODO: move to fsFFI? *)
val fs_ffi_no_ffi_div = Q.store_thm("fs_ffi_no_ffi_div",`
  (ffi_open_in conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_open_out conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_read conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_close conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_write conf bytes fs = SOME FFIdiverge ==> F)
`,
  rw[ffi_open_in_def,ffi_open_out_def,ffi_read_def,ffi_close_def,ffi_write_def,
     OPTION_GUARD_COND,OPTION_CHOICE_EQUALS_OPTION,ELIM_UNCURRY]
  \\ rpt(PURE_TOP_CASE_TAC \\ rw[])
  \\ rw[OPTION_CHOICE_EQUALS_OPTION,ELIM_UNCURRY]);

(* TODO: move to clFFI? *)
val cl_ffi_no_ffi_div = Q.store_thm("cl_ffi_no_ffi_div",`
  (ffi_get_arg_count conf bytes cls = SOME FFIdiverge ==> F) /\
  (ffi_get_arg_length conf bytes cls = SOME FFIdiverge ==> F) /\
  (ffi_get_arg conf bytes cls = SOME FFIdiverge ==> F)
`,
  rw[clFFITheory.ffi_get_arg_count_def,clFFITheory.ffi_get_arg_length_def,
     clFFITheory.ffi_get_arg_def]);

val oracle_parts_div = Q.store_thm("oracle_parts_div",
  `!st. st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\ MEM m ns /\ u m conf bytes (basis_proj1 x ' m) = SOME FFIdiverge
    ==> st.ffi.oracle m x conf bytes = Oracle_final FFI_diverged`,
  simp[basis_proj2_def,basis_proj1_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[cfHeapsBaseTheory.mk_proj1_def,
        cfHeapsBaseTheory.mk_proj2_def,
        basis_ffi_oracle_def,basis_ffi_part_defs]
  \\ rw[] \\ fs[FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM]
  \\ TRY (
     CASE_TAC \\ fs[cfHeapsBaseTheory.mk_ffi_next_def]
     \\ CASE_TAC \\ fs[fmap_eq_flookup,FLOOKUP_UPDATE]
     \\ rw[] )
  \\ fs[cl_ffi_no_ffi_div,fs_ffi_no_ffi_div]
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]);

val parts_ok_ag = Q.store_thm("parts_ok_ag",
  `parts_ok (auto_state_1 (basis_ffi cls fs)).ffi (basis_proj1, basis_proj2)` ,
  qmatch_goalsub_abbrev_tac`st.ffi`
  \\ `st.ffi.oracle = basis_ffi_oracle`
  by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
  \\ rw[cfStoreTheory.parts_ok_def]
  \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
  \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
  \\ TRY ( imp_res_tac oracle_parts_div \\ rfs[] \\ NO_TAC)
  \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
  \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
  \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
  \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
  \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
  \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
  \\ TRY(PURE_FULL_CASE_TAC \\ fs[])
  \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
  \\ srw_tac[DNF_ss][] \\ fs[ffi_exit_def]
);

*)

val _ = export_theory();
