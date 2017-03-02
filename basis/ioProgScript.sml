open preamble
     ml_translatorTheory ml_translatorLib semanticPrimitivesTheory evaluatePropsTheory
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib basisFunctionsLib
     mlfileioProgTheory cfMainTheory

val _ = new_theory "ioProg"

val _ = translation_extends "mlfileioProg";

val write_list = normalise_topdecs
  `fun write_list xs =
     case xs of
         [] => ()
       | x::xs => (CharIO.write x; write_list xs)`;

val _ = ml_prog_update (ml_progLib.add_prog write_list pick_name);

val basis_st = get_ml_prog_state;

val write_list_spec = Q.store_thm ("write_list_spec",
  `!xs cv output.
     LIST_TYPE CHAR xs cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "write_list" (basis_st()))
       [cv]
       (STDOUT output)
       (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ xs))`,
  Induct
  THEN1
   (xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ fs [LIST_TYPE_def,PULL_EXISTS] \\ rw []
  \\ xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
  \\ xmatch
  \\ xlet `POSTv uv. STDOUT (output ++ [h])`
  THEN1
   (xapp  \\ instantiate
    \\ qexists_tac `emp` \\ qexists_tac `output` \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `emp`
  \\ qexists_tac `output ++ [h]`
  \\ xsimpl \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ xsimpl);

val read_all = normalise_topdecs
  `fun read_all cs =
    let
      val u = ()
      val c = CharIO.read u
    in
      if CharIO.read_failed u then
        (*once it moves to mllist, List.*)rev cs
      else
        read_all (c::cs)
      end`;

val _ = ml_prog_update (ml_progLib.add_prog read_all pick_name);

val char_reverse_v_thm = save_thm("char_reverse_v_thm",
  std_preludeTheory.reverse_v_thm
  |> GEN_ALL |> ISPEC ``CHAR``);

val read_all_spec = Q.store_thm ("read_all_spec",
  `!xs cv input read_failed.
     LIST_TYPE CHAR xs cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "read_all" (basis_st()))
       [cv]
       (STDIN input read_failed)
       (POSTv uv. STDIN "" T * &(LIST_TYPE CHAR (REVERSE xs ++ input) uv))`,
  Induct_on `input`
  THEN1
   (xcf "read_all" (basis_st()) \\ fs [LIST_TYPE_def]
    \\ xlet `POSTv uv. STDIN "" read_failed * &(UNIT_TYPE () uv)`
    THEN1 (xcon \\ fs [] \\ xsimpl)
    \\ xlet `POSTv xv. STDIN "" T` (* TODO: change xv to _ and it breaks the xapp below. what is this bug!? *)
    THEN1
     (xapp \\ fs [PULL_EXISTS] \\ xsimpl
      \\ qexists_tac `emp`
      \\ qexists_tac`read_failed`
      \\ qexists_tac `""` \\ xsimpl)
    \\ xlet `POSTv bv. STDIN "" T * cond (BOOL T bv)`
    >- ( xapp \\ fs[] )
    \\ xif \\ instantiate
    \\ xapp
    \\ xsimpl
    \\ instantiate)
  \\ xcf "read_all" (basis_st()) \\ fs [LIST_TYPE_def]
  \\ xlet `POSTv v. STDIN (STRING h input) read_failed * &(UNIT_TYPE () v)`
  >- (xcon \\ xsimpl )
  \\ xlet `POSTv v. STDIN input F * &(CHAR h v)`
  >- (
    xapp
    \\ fs[PULL_EXISTS]
    \\ qexists_tac`emp`
    \\ qexists_tac`read_failed`
    \\ qexists_tac`h::input`
    \\ xsimpl )
  \\ xlet `POSTv v. STDIN input F * &(BOOL F v)`
  >- ( xapp \\ fs[] )
  \\ xif \\ instantiate
  \\ xlet `POSTv x. STDIN input F * &(LIST_TYPE CHAR (h::xs) x)`
  THEN1 (xcon \\ xsimpl \\ fs [LIST_TYPE_def])
  \\ xapp
  \\ instantiate \\ xsimpl
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ qexists_tac`emp`
  \\ qexists_tac`F`
  \\ xsimpl);



(*TODO: update this to include Char.fromByte and move to a more appropriate location*)
val print = process_topdecs
  `fun print s =
    let
      val l = String.explode s
    in write_list l end`

val res = ml_prog_update(ml_progLib.add_prog print pick_name)

val print_spec = Q.store_thm("print_spec",
  `!s sv. STRING_TYPE s sv ==>
   app (p:'ffi ffi_proj) ^(fetch_v "print" (basis_st())) [sv]
   (STDOUT output)
   (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ (explode s)))`,
    xcf "print" (basis_st())
    \\ xlet `POSTv lv. & LIST_TYPE CHAR (explode s) lv * STDOUT output`
    >-(xapp \\ xsimpl \\ instantiate)
    \\ xapp \\ rw[]
);

val res = register_type``:'a app_list``;

val print_app_list = process_topdecs
  `fun print_app_list ls =
   (case ls of
      Nil => ()
    | List ls => List.app print ls
    | Append(l1,l2)=> (print_app_list l1; print_app_list l2))`;
val res = ml_prog_update(ml_progLib.add_prog print_app_list pick_name);

val st = get_ml_prog_state();

val MISC_APP_LIST_TYPE_def = theorem"MISC_APP_LIST_TYPE_def";

val print_app_list_spec = Q.store_thm("print_app_list_spec",
  `∀ls lv out. MISC_APP_LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "print_app_list" st) [lv]
     (STDOUT out) (POSTv v. &UNIT_TYPE () v * STDOUT (out ++ FLAT (MAP explode (append ls))))`,
  reverse Induct \\ rw[MISC_APP_LIST_TYPE_def]
  >- (
    xcf "print_app_list" st
    \\ xmatch \\ xcon \\ xsimpl )
  >- (
    xcf "print_app_list" st
    \\ xmatch
    \\ ntac 2 (first_x_assum drule)
    \\ ntac 2 strip_tac
    \\ xlet`POSTv v. &UNIT_TYPE () v * STDOUT (out ++ FLAT (MAP explode (append ls)))`
    >- ( first_x_assum xapp_spec )
    \\ first_x_assum xapp_spec )
  \\ xcf "print_app_list" st
  \\ xmatch
  \\ xapp_spec (INST_TYPE[alpha|->mlstringSyntax.mlstring_ty]mllistProgTheory.app_spec)
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`λn. STDOUT (out ++ FLAT (MAP explode (TAKE n l)))`
  \\ qexists_tac`l`
  \\ xsimpl
  \\ instantiate
  \\ rw[]
  \\ xapp
  \\ xsimpl
  \\ instantiate
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`out ++ FLAT(MAP explode (TAKE n l))`
  \\ xsimpl
  \\ qmatch_abbrev_tac`STDOUT s1 ==>> STDOUT s2 * _`
  \\ `s1 = s2` suffices_by xsimpl
  \\ unabbrev_all_tac
  \\ `TAKE (n + 1) l = SNOC (EL n l) (TAKE n l)`
  by metis_tac[SNOC_EL_TAKE,ADD1]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[]);

(*-------------------------------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (inp,out,cls,fs) bytes.
     if name = "putChar" then
       case ffi_putChar bytes out of
       | SOME (bytes,out) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "getChar" then
       case ffi_getChar bytes inp of
       | SOME (bytes,inp) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "getArgs" then
       case ffi_getArgs bytes cls of
       | SOME (bytes,cls) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open" then
       case ffi_open bytes fs of
       | SOME (bytes,fs) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "fgetc" then
       case ffi_fgetc bytes fs of
       | SOME (bytes,fs) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "close" then
       case ffi_close bytes fs of
       | SOME (bytes,fs) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     if name = "isEof" then
       case ffi_isEof bytes fs of
       | SOME (bytes,fs) => Oracle_return (inp,out,cls,fs) bytes
       | _ => Oracle_fail else
     Oracle_fail`

(*Output is always empty to start *)
val basis_ffi_def = Define `
  basis_ffi (inp: string) (cls: string list) files =
    <| oracle := basis_ffi_oracle
     ; ffi_state := (inp, [], cls, (<| files := files; infds := [] |> : RO_fs))
     ; final_event := NONE
     ; io_events := [] |>`;

val basis_proj1_def = Define `
  basis_proj1 = (\(inp, out, cls, fs).
    FEMPTY |++
      ((mk_proj1 stdin_ffi_part inp) ++
       (mk_proj1 stdout_ffi_part out) ++
       (mk_proj1 commandLine_ffi_part cls) ++
       (mk_proj1 rofs_ffi_part fs)))`;

val basis_proj2_def = Define `
  basis_proj2 =
    [mk_proj2 stdin_ffi_part;
     mk_proj2 stdout_ffi_part;
     mk_proj2 commandLine_ffi_part;
     mk_proj2 rofs_ffi_part]`;

val basis_proj1_putChar = Q.store_thm("basis_proj1_putChar",
  `basis_proj1 ffi ' "putChar" = Str(FST(SND ffi))`,
  PairCases_on`ffi` \\ EVAL_TAC);

val extract_output_def = Define `
  (extract_output [] = SOME []) /\
  (extract_output ((IO_event name bytes)::xs) =
     case extract_output xs of
     | NONE => NONE
     | SOME rest =>
         if name <> "putChar" then SOME rest else
         if LENGTH bytes <> 1 then NONE else
           SOME ((SND (HD bytes)) :: rest))`

val extract_output_APPEND = Q.store_thm("extract_output_APPEND",
  `!xs ys.
      extract_output (xs ++ ys) =
      case extract_output ys of
      | NONE => NONE
      | SOME rest => case extract_output xs of
                     | NONE => NONE
                     | SOME front => SOME (front ++ rest)`,
  Induct \\ fs [APPEND,extract_output_def] \\ rw []
  THEN1 (every_case_tac \\ fs [])
  \\ Cases_on `h` \\ fs [extract_output_def]
  \\ rpt (CASE_TAC \\ fs []));

(*-------------------------------------------------------------------------------------------------*)

(*The following thms are used to automate the proof of the SPLIT of the heap in ioProgLib*)
val append_hprop = Q.store_thm ("append_hprop",
  `A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 ∪ s2)`,
  rw[set_sepTheory.STAR_def] \\ SPLIT_TAC
);

val SPLIT_exists = Q.store_thm ("SPLIT_exists",
  `(A * B) s /\ s ⊆ C
    ==> (?h1 h2. SPLIT C (h1, h2) /\ (A * B) h1)`,
  rw[]
  \\ qexists_tac `s` \\ qexists_tac `C DIFF s`
  \\ SPLIT_TAC
);

val append_emp = Q.store_thm("append_emp",
  `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT x) ==> app p fv xs (P * emp) (POSTv uv. (A uv) * (STDOUT x * emp))`,
  rw[set_sepTheory.SEP_CLAUSES]
);

val emp_precond = Q.store_thm("emp_precond",
  `emp {}`, EVAL_TAC);

(*-------------------------------------------------------------------------------------------------*)
(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)

val RTC_call_FFI_rel_IMP_basis_events = Q.store_thm ("RTC_call_FFI_rel_IMP_basis_events",
  `!st st'. call_FFI_rel^* st st' ==>
  st.oracle = basis_ffi_oracle /\
  extract_output st.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 st.ffi_state ' "putChar")))) ==>
  extract_output st'.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 st'.ffi_state ' "putChar"))))`,
  HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ fs [extract_output_APPEND,extract_output_def,basis_proj1_putChar] \\ rfs []
  \\ first_x_assum match_mp_tac
  \\ qpat_x_assum`_ = Oracle_return _ _`mp_tac
  \\ simp[basis_ffi_oracle_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[stdoutFFITheory.ffi_putChar_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ simp[n2w_ORD_CHR_w2n |> SIMP_RULE(srw_ss())[o_THM,FUN_EQ_THM]]
);


(*extract_output_basis_ffi shows that the first condition for the previous theorem holds for the
  init_state ffi  *)

val extract_output_basis_ffi = Q.store_thm ("extract_output_basis_ffi",
  `extract_output (init_state (basis_ffi inp cls fs)).ffi.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 (init_state (basis_ffi inp cls fs)).ffi.ffi_state ' "putChar"))))`,
  rw[ml_progTheory.init_state_def, extract_output_def, basis_ffi_def, basis_proj1_putChar, cfHeapsBaseTheory.destStr_def, FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
);


(*call_main_thm_basis uses call_main_thm2 to get Semantics_prog, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on
  st.io_events  *)

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;


val call_main_thm_basis = Q.store_thm("call_main_thm_basis",
`!fname fv.
 ML_code env1 (init_state (basis_ffi inp cls fs)) prog NONE env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (basis_proj1, basis_proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * (STDOUT x * Q)) ==>
  no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs)).defined_mods /\
  no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs)).defined_types ==>
  (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ P h1)
  ==>
    ∃(st3:(string # string # string list # RO_fs) semanticPrimitives$state).
    semantics_prog (init_state (basis_ffi inp cls fs)) env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    extract_output st3.ffi.io_events = SOME (MAP (n2w o ORD) x)`,
    rw[]
    \\ drule (GEN_ALL call_main_thm2)
    \\ rpt(disch_then drule)
    \\ simp[] \\ strip_tac
    \\ `FFI_part_hprop (STDOUT x * Q)`
    by metis_tac[FFI_part_hprop_def, mlcharioProgTheory.STDOUT_FFI_part_hprop, FFI_part_hprop_STAR]
    \\ first_x_assum (qspecl_then [`h2`, `h1`] mp_tac) \\ rw[] \\ fs[]
    \\ qexists_tac `st3` \\ rw[]
    \\ `(THE (destStr (basis_proj1 st3.ffi.ffi_state ' "putChar"))) = x` suffices_by
      (imp_res_tac RTC_call_FFI_rel_IMP_basis_events
      \\ fs[extract_output_basis_ffi, ml_progTheory.init_state_def, basis_ffi_def])
    \\ fs[basis_proj1_putChar]
    \\ fs[mlcharioProgTheory.STDOUT_def, cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
          set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM, stdoutFFITheory.stdout_ffi_part_def]
    \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
    \\ qmatch_assum_abbrev_tac`ffip ∈ h3`
    \\ `ffip ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
    \\ fs [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,Abbr`ffip`]
    \\ fs [cfStoreTheory.ffi2heap_def]
    \\ Cases_on `parts_ok st3.ffi (basis_proj1, basis_proj2)`
    \\ fs[FLOOKUP_DEF, MAP_MAP_o, n2w_ORD_CHR_w2n, basis_proj1_putChar]
);


(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
val oracle_parts = Q.store_thm("oracle_parts",
  `!st. st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\ MEM m ns /\ u m bytes (basis_proj1 x ' m) = SOME (new_bytes, w)
    ==> (?y. st.ffi.oracle m x bytes = Oracle_return y new_bytes /\ basis_proj1 x |++ MAP (\n. (n,w)) ns = basis_proj1 y)`,
  rw[basis_ffi_oracle_def, basis_proj2_def, basis_proj1_def] \\ pairarg_tac \\ fs[] \\ Cases_on `m = "putChar"` \\ Cases_on `m = "getChar"` \\ Cases_on `m = "getArgs"`
  \\ rw[ffi_putChar_def, ffi_getChar_def, ffi_getArgs_def]
  >-(Cases_on `bytes` \\ fs[stdout_fun_def, stdin_fun_def, commandLine_fun_def, ffi_putChar_def, ffi_getChar_def, ffi_getArgs_def]
    \\ Cases_on `t` \\ pairarg_tac \\ fs[FUPDATE_LIST, FLOOKUP_UPDATE, FAPPLY_FUPDATE_THM] \\ rw[]
    \\ rw[FUPDATE_EQ, FUPDATE_COMMUTES] \\ metis_tac[FUPDATE_EQ, FUPDATE_COMMUTES] \\ NO_TAC)
  >-(Cases_on `bytes` \\ fs[stdout_fun_def, stdin_fun_def, commandLine_fun_def, ffi_putChar_def, ffi_getChar_def, ffi_getArgs_def]
    \\ Cases_on `t` \\ pairarg_tac \\ fs[FUPDATE_LIST, FLOOKUP_UPDATE, FAPPLY_FUPDATE_THM] \\ rw[]
    \\ rw[FUPDATE_EQ, FUPDATE_COMMUTES] \\ metis_tac[FUPDATE_EQ, FUPDATE_COMMUTES] \\ NO_TAC)
  \\ TRY ( Cases_on `bytes` \\ fs[stdout_fun_def, stdin_fun_def, commandLine_fun_def, ffi_putChar_def, ffi_getChar_def, ffi_getArgs_def]
    \\ fs[FUPDATE_LIST, FLOOKUP_UPDATE, OPT_MMAP_MAP_o, decode_def, cfHeapsBaseTheory.decode_list_def, cfHeapsBaseTheory.destStr_def, encode_def, cfHeapsBaseTheory.encode_list_def]
    \\ pairarg_tac \\ fs[] \\ rw[] \\ fs[] \\ NO_TAC)
  \\ fs[commandLine_fun_def, decode_def, cfHeapsBaseTheory.decode_list_def, cfHeapsBaseTheory.destStr_def, FUPDATE_LIST, FLOOKUP_UPDATE, OPT_MMAP_MAP_o, ffi_getArgs_def, o_DEF]
  \\ full_simp_tac std_ss [EVERY_NOT_EXISTS]
);

(*This is an example of how to show parts_ok for a given state -- could be automate and put in ioProgLib.sml *)
val parts_ok_basis_st = Q.store_thm("parts_ok_basis_st",
  `parts_ok (auto_state_1 (basis_ffi inp cls)).ffi (basis_proj1, basis_proj2)` ,
  rw[cfStoreTheory.parts_ok_def] \\ TRY (
  EVAL_TAC
  \\ fs[basis_proj2_def, basis_proj1_def, FLOOKUP_UPDATE, FAPPLY_FUPDATE_THM,FUPDATE_LIST]
  \\ rw[]
  \\ imp_res_tac stdout_fun_length
  \\ imp_res_tac stdin_fun_length
  \\ imp_res_tac commandLine_fun_length
  \\ NO_TAC)
  \\ `(auto_state_1 (basis_ffi inp cls)).ffi.oracle = basis_ffi_oracle` suffices_by
    metis_tac[oracle_parts]
  \\ EVAL_TAC
);

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

val UNION_DIFF_3 = Q.store_thm("UNION_DIFF_3",
  `!a b c. (DISJOINT a b /\ DISJOINT a c /\ DISJOINT b c) \/
    (DISJOINT b a /\ DISJOINT c a /\ DISJOINT c b) ==>
    (a ∪ b ∪ c DIFF b DIFF c) = a`,
    SPLIT_TAC
);


val star_delete_heap_imp = Q.store_thm("star_delete_heap_imp",
  `((A * B * C):hprop) h /\ A s1 /\ B s2 /\ C s3
    /\ (!a b. C a /\ C b ==> a = b)
    /\ (!a b. B a /\ B b ==> a = b)
    /\ (!a b. A a /\ A b ==> a = b)
    ==>
    (A * B) (h DIFF s3) /\ (A * C) (h DIFF s2) /\
    (B * C) (h DIFF s1) /\ A (h DIFF s2 DIFF s3) /\
    B (h DIFF s1 DIFF s3) /\ C (h DIFF s1 DIFF s2)`,
    rw[set_sepTheory.STAR_def]
    \\ `v = s3` by fs[] \\ rw[]
    \\ `v' = s2` by fs[] \\ rw[]
    \\ `u' = s1` by fs[] \\ rw[]
    \\ TRY (instantiate \\ SPLIT_TAC \\ NO_TAC)
    \\ fs[SPLIT_def]  \\ rw[] \\ fs[]
    \\ imp_res_tac UNION_DIFF_3 \\ rw[] \\ fs[DISJOINT_SYM] \\ rfs[]
    \\ metis_tac[UNION_COMM, UNION_ASSOC]
);


val _ = export_theory ()
