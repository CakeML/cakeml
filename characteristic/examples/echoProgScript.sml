open  preamble ml_progLib ioProgLib ml_translatorLib
      cfTacticsLib

val _ = new_theory "echoProg";

val _ = translation_extends"ioProg";

(* This is the expected workflow for getting the semantics and the output of
  a program using basis_projs, basis_oracle and basis_ffi, as well as 
  preparing it for compilation. Note that the main call should be of type
  unit->unit   *)

val echo = process_topdecs
  `fun echo u = 
      let 
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
        val ok = print cls
      in CharIO.write #"\n" end`

val res = ml_prog_update(ml_progLib.add_prog echo pick_name)

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!ls b bv. cl <> [] /\ EVERY validArg cl /\
   LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (s) ++ [CHR 0]) (cl)))) < 257 ==>
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * (STDOUT (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) * COMMANDLINE cl))`,
    xcf "echo" st
    \\ xlet `POSTv zv. & UNIT_TYPE () zv * STDOUT output * COMMANDLINE cl` 
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv argv. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) argv * STDOUT output
      * COMMANDLINE cl`
    >-(xapp \\ instantiate \\ qexists_tac `STDOUT output` \\ xsimpl)
    \\ xlet `POSTv clv. STDOUT output * COMMANDLINE cl * & STRING_TYPE (implode (CONCAT_WITH " " (TL cl))) clv`
    >-(xapp \\ xsimpl \\ instantiate
      \\ rw[mlstringTheory.concatWith_CONCAT_WITH, mlstringTheory.implode_explode, Once mlstringTheory.implode_def]
      \\ Cases_on `cl` \\ fs[mlstringTheory.implode_def])
    \\ xlet `POSTv xv. &UNIT_TYPE () xv * STDOUT (output ++ (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl`
    >-(xapp \\ qexists_tac `COMMANDLINE cl` \\ xsimpl \\ qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
      \\ rw[mlstringTheory.explode_implode] \\ xsimpl)
    \\ xapp \\ map_every qexists_tac [`COMMANDLINE cl`, `output ++ (CONCAT_WITH " " (TL cl))`, `(CHR 10)`] \\ xsimpl
);

val st = get_ml_prog_state();
val spec = echo_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "echo";
val (call_thm_echo, echo_prog_tm) = call_thm st name spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;



(*------------------------------------------------------------------------------------------------*)

(*
val STDOUT_COMMANDLINE_precond =  Q.store_thm("STDOUT_COMMANDLINE_precond",
  `(STDOUT out * COMMANDLINE cls)
    {FFI_part (Str out) stdout_fun ["putChar"] events1;
     FFI_part (List (MAP Str cls)) commandLine_fun ["getArgs"] events2;
     Mem 1 (W8array [w])}`,
  rw[STDOUT_def,COMMANDLINE_def,cfHeapsBaseTheory.IO_def,
     set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ simp[Once set_sepTheory.STAR_COMM]
  \\ simp[set_sepTheory.one_STAR]
  \\ rw[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``write_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ simp [set_sepTheory.one_def]
  \\ qexists_tac`w`
  \\ rw[EXTENSION,EQ_IMP_THM]);

val STDOUT_COMMANDLINE_precond_subset = Q.store_thm("STDOUT_COMMANDLINE_precond_subset",
`!st out cls w events1 events2.
{FFI_part (Str out) stdout_fun ["putChar"] events1;
     FFI_part (List (MAP Str cls)) commandLine_fun ["getArgs"] events2;
     Mem 1 (W8array [w])} ⊆ (st2heap (basis_proj1,basis_proj2) st)
  ==>
  ∃h2 h1.
  SPLIT (st2heap (basis_proj1,basis_proj2) st) (h1,h2) ∧
  (STDOUT out * COMMANDLINE cls) h1`,
rpt strip_tac
\\ qmatch_assum_abbrev_tac`s1 ⊆ s2`
\\ qexists_tac`s2 DIFF s1`
\\ qexists_tac`s1`
\\ conj_tac >- SPLIT_TAC
\\ simp[Abbr`s1`]
\\ metis_tac[STDOUT_COMMANDLINE_precond]);

val st = call_thm_echo |> SPEC_ALL |> concl |> dest_imp |> #1 |> rator |> rand |> rand

val echo_precond = store_thm("echo_precond",
  STDOUT_COMMANDLINE_precond_subset
  |> SPECL[st,``""``,repeat rand st,``0w:word8``]
  |> Q.SPECL[`[]`,`[]`]
  |> concl |> dest_imp |> #1,
  CONV_TAC(RAND_CONV(RAND_CONV EVAL))
  \\ rw[cfStoreTheory.st2heap_def,cfStoreTheory.FFI_part_NOT_IN_store2heap,
        cfStoreTheory.Mem_NOT_IN_ffi2heap]
  \\ simp[cfStoreTheory.ffi2heap_def]



val call_thm_echo2 =
  let
    val st = call_thm_echo |> SPEC_ALL |> concl |> dest_imp |> #1 |> rator |> rand |> rand
    val th = STDOUT_COMMANDLINE_precond_subset |> Q.GEN`st` |> SPEC st
    val th2 = th |> CONV_RULE(LAND_CONV (RAND_CONV (RAND_CONV EVAL)))
    val th1 =
       call_thm_echo
       |> PURE_REWRITE_RULE[AND_IMP_INTRO]
       |> CONV_RULE(QUANT_CONV(HO_REWR_CONV LEFT_FORALL_IMP_THM))
       |> CONV_RULE(HO_REWR_CONV LEFT_FORALL_IMP_THM)
       |> CONV_RULE(
       CONSEQ_HO_REWRITE_CONV ([STDOUT_COMMANDLINE_precond_subset],[STDOUT_COMMANDLINE_precond_subset],[STDOUT_COMMANDLINE_precond_subset])
       CONSEQ_CONV_STRENGTHEN_direction)
    val tm1 = th1 |> concl |> dest_imp |> #1
    val tm2 = STDOUT_COMMANDLINE_precond_subset |> concl |> dest_imp |> #2
    val res = match_term tm2 tm1

  |> C MATCH_MP STDOUT_COMMANDLINE_precond_subset

  Q.SPEC`{}`
  |> PURE_REWRITE_RULE[cfHeapsBaseTheory.SPLIT_emp2]
  |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM2)

val th = 
  call_thm_echo2
  |> CONV_RULE(LAND_CONV(RAND_CONV (RAND_CONV EVAL)))
  |> 
DB.find"st2heap_def"
|>
  call_thm_echo2 |> concl |> dest_imp |> #1
EVAL tm


val basis_proj_parts = (rhs(concl(EVAL ``(FLAT (MAP FST basis_proj2))``)))
val parts_ok_basis_proj = Q.store_thm("parts_ok_basis_proj",
  `st.final_event = NONE ∧ st.oracle = basis_ffi_oracle ∧
   EVERY (ffi_has_index_in ^basis_proj_parts) st.io_events ⇒
   parts_ok st (basis_proj1,basis_proj2)`,
  rw[cfStoreTheory.parts_ok_def]
  >- EVAL_TAC
  >- (EVAL_TAC \\ rw[])
  >- (
    pop_assum mp_tac \\ EVAL_TAC
    \\ rw[] \\ rw[]
    \\ pairarg_tac
    \\ rw[FLOOKUP_UPDATE] )
  >- (
    qpat_x_assum`MEM _ basis_proj2`mp_tac
    \\ EVAL_TAC \\ rw[]
    \\ pop_assum mp_tac \\ EVAL_TAC
    \\ rw[]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ rw[]
    \\ every_case_tac \\ fs[] \\ rw[]
    \\ rw[LENGTH_EQ_NUM_compute]
    \\ Cases_on`bytes` \\ fs[]  )
  >- (
    qpat_x_assum`MEM _ basis_proj2`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ rw[] \\ pop_assum mp_tac \\ fs[]
    \\ TRY (
      rename1`commandLine_fun`
      \\ rw[commandLine_fun_def]
      \\ pairarg_tac \\ fs[] \\ rw[]
      \\ rw[basis_ffi_oracle_def]
      \\ pairarg_tac
      \\ fs[basis_proj1_def,FAPPLY_FUPDATE_THM,FUPDATE_LIST_THM]
      \\ qpat_x_assum`decode _ = _`mp_tac \\ CONV_TAC(LAND_CONV EVAL)
      \\ simp[OPT_MMAP_MAP_o] \\ rw[]
      \\ simp[fmap_eq_flookup,FLOOKUP_UPDATE]
      \\ rw[]
      \\ EVAL_TAC \\ NO_TAC)
    \\ EVAL_TAC
    \\ rw[] \\ pairarg_tac \\ every_case_tac \\ fs[] \\ rw[] \\ fs[]
    \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[]
    \\ fs[FAPPLY_FUPDATE_THM]
    \\ rw[FLOOKUP_UPDATE]))

val STDOUT_COMMANDLINE_precond =  Q.store_thm("STDOUT_COMMANDLINE_precond",
`st.ffi.ffi_state = (inp,"",cls) ∧
 st.ffi.final_event = NONE ∧ st.ffi.oracle = basis_ffi_oracle ∧
 (* EVERY (ffi_has_index_in ^basis_proj_parts) st.ffi.io_events ∧ *)
 st.ffi.io_events = []
 1 < LENGTH st.refs ∧ EL 1 st.refs = W8array [w]
  ==>
  ∃h2 h1.
  SPLIT (st2heap (basis_proj1,basis_proj2) st) (h1,h2) ∧
  (STDOUT "" * COMMANDLINE cls) h1`,
  rw[STDOUT_def,COMMANDLINE_def,cfHeapsBaseTheory.IO_def,
     set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ simp[Once set_sepTheory.STAR_COMM]
  \\ simp[set_sepTheory.one_STAR]
  \\ rw[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap]
  \\ `Mem 1 (W8array [w]) ∈ store2heap st.refs`
  by (
    Cases_on`st.refs` \\ fs[]
    \\ EVAL_TAC \\ rw[] \\ Cases_on`t` \\ fs[]
    \\ EVAL_TAC \\ NO_TAC)

  \\ qmatch_goalsub_abbrev_tac`SPLIT (store2heap st.refs ∪ ffih) _`
  \\ qexists_tac`store2heap st.refs DELETE Mem 1 (W8array [w])`
  \\ qexists_tac`Mem 1 (W8array [w]) INSERT ffih`
  \\ conj_tac
  >- (
    rw[set_sepTheory.SPLIT_def,EXTENSION,IN_DISJOINT,EQ_IMP_THM] \\ rw[]
    >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ fs[Abbr`ffih`] \\ rw[]
    \\ fs[cfStoreTheory.ffi2heap_def,cfStoreTheory.store2heap_def]
    \\ every_case_tac
    \\ fs[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux,cfStoreTheory.FFI_split_NOT_IN_store2heap_aux]
    \\ rfs[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux,cfStoreTheory.FFI_split_NOT_IN_store2heap_aux]
    \\ imp_res_tac parts_ok_basis_proj)
  \\ simp[Abbr`ffih`]
  \\ rw[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``write_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ simp [set_sepTheory.one_def]

  \\ simp[RIGHT_EXISTS_AND_THM]
  \\ rpt (conj_tac >- EVAL_TAC)
  \\ simp[INSERT_EQ_SING]

  INSERT_DELETE

  \\ simp[Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  DB.find_in"INSERT"(DB.find"sing")

  \\ TRY(qexists_tac`0w`) \\ fs[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux]
  \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ TRY (EVAL_TAC \\ qexists_tac`0w` \\ rw[] \\ NO_TAC)
     \\ fs [EXTENSION] \\ rpt strip_tac \\ EQ_TAC \\ rw [] \\ rw []
     \\ TRY (EVAL_TAC \\ NO_TAC)
     \\ fs [io_proj2_def] \\ rw [] \\ fs []
DB.find"w8array_def"


*)

(*-------------------------------------------------------------------------------------------------*)

(* TODO: Move these to somewhere relevant *) 
val extract_output_not_putChar = Q.prove(
    `!xs name bytes. name <> "putChar" ==>
      extract_output (xs ++ [IO_event name bytes]) = extract_output xs`,
      rw[extract_output_APPEND, extract_output_def] \\ Cases_on `extract_output xs` \\ rw[]
);

val extract_output_FILTER = Q.store_thm("extract_output_FILTER",
  `!st. extract_output st.ffi.io_events = extract_output (FILTER (ffi_has_index_in ["putChar"]) st.ffi.io_events)`,
  Cases_on `st` \\ Cases_on `f` \\ Induct_on `l'` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND]
  \\ fs[] \\ rw[extract_output_def] \\ full_case_tac 
  \\ Cases_on `extract_output (FILTER (ffi_has_index_in ["putChar"]) l')` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND] \\ fs[]
  \\ Cases_on `h` \\ Cases_on `s = "putChar"` \\ fs[cfStoreTheory.ffi_has_index_in_def, extract_output_def]
);


val _ = export_theory();
