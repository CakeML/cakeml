open preamble
     ml_translatorTheory ml_translatorLib semanticPrimitivesTheory evaluatePropsTheory
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib basisFunctionsLib
     mlcharioProgTheory

val _ = new_theory "ioProg"

val _ = translation_extends "mlcharioProg";

val write_list = parse_topdecs
  `fun write_list xs =
     case xs of
         [] => ()
       | x::xs => (CharIO.write x; write_list xs)`;

val _ = ml_prog_update (ml_progLib.add_prog write_list pick_name);

val basis_st = get_ml_prog_state;

val write_list_spec = Q.store_thm ("write_list_spec",
  `!xs cv output.
     LIST_TYPE WORD (xs:word8 list) cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "write_list" (basis_st()))
       [cv]
       (STDOUT output)
       (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ (MAP (CHR o w2n) xs)))`,
  Induct
  THEN1
   (xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ fs [LIST_TYPE_def,PULL_EXISTS] \\ rw []
  \\ xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
  \\ xmatch
  \\ xlet `POSTv uv. STDOUT (output ++ [(CHR o w2n) h])`
  THEN1
   (xapp  \\ instantiate
    \\ qexists_tac `emp` \\ qexists_tac `output` \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `emp`
  \\ qexists_tac `output ++ [(CHR o w2n) h]`
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
      val nl = List.map_1 (Char.ord) l
      val bl = List.map_1 (Word8.fromInt) nl
    in write_list bl end`

val res = ml_prog_update(ml_progLib.add_prog print pick_name)

val CHR_w2n_n2w_ORD = Q.store_thm("CHR_w2n_n2w_ORD",
  `(CHR o w2n o (n2w:num->word8) o ORD) = I`,
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
);

val n2w_ORD_CHR_w2n = Q.store_thm("n2w_ORD_CHR_w2n",
  `((n2w:num->word8) o ORD o CHR o w2n) = I`,
  rw[w2n_lt_256, o_DEF, ORD_BOUND, ORD_CHR, FUN_EQ_THM]
);


(*TODO fix the use of map_1 instead of map *)
val map_1_v_thm = fetch "mllistProg" "map_1_v_thm";
val string_map_v_thm = save_thm("string_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:char``, beta|->``:num``])
val byte_map_v_thm = save_thm("byte_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:num``, beta|->``:word8``])


val print_spec = Q.store_thm("print_spec",
  `!s sv. STRING_TYPE s sv ==>
   app (p:'ffi ffi_proj) ^(fetch_v "print" (basis_st())) [sv]
   (STDOUT output)
   (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ (explode s)))`,  
    xcf "print" (basis_st())
    \\ xlet `POSTv lv. & LIST_TYPE CHAR (explode s) lv * STDOUT output`
    >-(xapp \\ xsimpl \\ instantiate)
    \\ xlet `POSTv nlv. & LIST_TYPE NUM (MAP ORD (explode s)) nlv * STDOUT output`
    >-(xapp_spec string_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `ORD` \\ qexists_tac `NUM`  \\ rw[mlcharProgTheory.char_ord_v_thm])
    \\ xlet `POSTv blv. & LIST_TYPE (WORD:word8 -> v -> bool) (MAP n2w (MAP ORD (explode s))) blv * STDOUT output`    
    >-(xapp_spec byte_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `n2w` \\ qexists_tac `WORD` \\ rw[mlword8ProgTheory.word8_fromint_v_thm])
    \\ xapp 
    \\ instantiate \\ qexists_tac `emp` \\ qexists_tac `output` \\ xsimpl 
    \\ fs[MAP_MAP_o, CHR_w2n_n2w_ORD] \\ xsimpl 
);

(* --- the following are defs and lemmas used by compiler/bootstrap/io/ioProgLib --- *)

val io_ffi_oracle_def = Define `
  (io_ffi_oracle:(string # string) oracle) =
    \name (inp,out) bytes.
       if name = "putChar" then
         case bytes of
         | [b] => Oracle_return (inp,out ++ [CHR (w2n b)]) [b]
         | _ => Oracle_fail
       else if name = "getChar" then
         case bytes of
         | [b;f] =>
           if inp = "" then
             Oracle_return (inp,out) [b; 1w]
           else
             Oracle_return (TL inp,out) [n2w(ORD(HD inp)); 0w]
         | _ => Oracle_fail
       else Oracle_fail`

val io_ffi_def = Define `
  io_ffi (inp:string) =
    <| oracle := io_ffi_oracle
     ; ffi_state := (inp,[])
     ; final_event := NONE
     ; io_events := [] |>`;

val io_proj1_def = Define `
  io_proj1 = (\(inp,out).
    FEMPTY |++ [("putChar",Str out);("getChar",Str inp)])`;

val io_proj2_def = Define `
  io_proj2 = [(["putChar"],stdout_fun);(["getChar"],stdin_fun)]`;

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

val evaluate_prog_RTC_call_FFI_rel = Q.store_thm("evaluate_prog_RTC_call_FFI_rel",
  `evaluate_prog F env st prog (st',tds,res) ==>
    RTC call_FFI_rel st.ffi st'.ffi`,
  rw[bigClockTheory.prog_clocked_unclocked_equiv]
  \\ (funBigStepEquivTheory.functional_evaluate_tops
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO
      |> Q.GENL[`tops`,`s`,`env`]
      |> qspecl_then[`env`,`st with clock := c`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ drule evaluatePropsTheory.evaluate_tops_call_FFI_rel_imp
  \\ imp_res_tac determTheory.prog_determ
  \\ fs[] \\ rw[]);

val RTC_call_FFI_rel_IMP_io_events = Q.store_thm("RTC_call_FFI_rel_IMP_io_events",
  `!st st'.
      call_FFI_rel^* st st' ==>
      st.oracle = io_ffi_oracle /\
      extract_output st.io_events = SOME (MAP (n2w o ORD) (SND (st.ffi_state))) ==>
      extract_output st'.io_events = SOME (MAP (n2w o ORD) (SND (st'.ffi_state)))`,
  HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ reverse (Cases_on `n = "putChar"`) \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [extract_output_APPEND,extract_output_def] \\ rfs []
  THEN1
   (fs [io_ffi_oracle_def]
    \\ fs [] \\ Cases_on `st.ffi_state` \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ every_case_tac \\ fs []
  THEN1
   (fs [io_ffi_oracle_def]
    \\ fs [] \\ Cases_on `st.ffi_state` \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `bytes` \\ fs [] \\ Cases_on `l` \\ fs []
  \\ Cases_on `t` \\ fs [] \\ Cases_on `t'` \\ fs []
  \\ fs [io_ffi_oracle_def]
  \\ Cases_on `st.ffi_state` \\ fs [] \\ rw []
  \\ fs[MAP_APPEND]
  \\ simp[n2w_ORD_CHR_w2n |> SIMP_RULE(srw_ss())[o_THM,FUN_EQ_THM]]
);

val MAP_CHR_w2n_11 = Q.store_thm("MAP_CHR_w2n_11",
  `!ws1 ws2:word8 list.
      MAP (CHR ∘ w2n) ws1 = MAP (CHR ∘ w2n) ws2 <=> ws1 = ws2`,
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `ws2` \\ fs [] \\ metis_tac [CHR_11,w2n_lt_256,w2n_11]);

val evaluate_prog_rel_IMP_evaluate_prog_fun = Q.store_thm(
   "evaluate_prog_rel_IMP_evaluate_prog_fun",
  `bigStep$evaluate_whole_prog F env st prog (st',new_tds,Rval r) ==>
    ?k. evaluate$evaluate_prog (st with clock := k) env prog =
          (st',new_tds,Rval r)`,
  rw[bigClockTheory.prog_clocked_unclocked_equiv,bigStepTheory.evaluate_whole_prog_def]
  \\ qexists_tac`c + st.clock`
  \\ (funBigStepEquivTheory.functional_evaluate_prog
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO |> GEN_ALL
      |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","env","prog"]))
      |> qspecl_then[`st with clock := c + st.clock`,`env`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ fs[bigStepTheory.evaluate_whole_prog_def]
  \\ drule bigClockTheory.prog_add_to_counter \\ simp[]
  \\ disch_then(qspec_then`st.clock`strip_assume_tac)
  \\ drule determTheory.prog_determ
  \\ every_case_tac \\ fs[]
  \\ TRY (disch_then drule \\ rw[])
  \\ fs[semanticPrimitivesTheory.state_component_equality]);

val parts_ok_io_ffi = Q.store_thm("parts_ok_io_ffi",
  `parts_ok (io_ffi input) (io_proj1,io_proj2)`,
  fs [cfStoreTheory.parts_ok_def]
  \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
  THEN1
   (fs [io_proj2_def,io_proj1_def,io_ffi_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ EVAL_TAC \\ qexists_tac `Str input` \\ fs [] \\ rw [])
  THEN1
   (fs [io_proj2_def] \\ rveq \\ fs [stdout_fun_def,stdin_fun_def, ffi_putChar_def, ffi_getChar_def]
    \\ rfs [io_proj1_def] \\ pairarg_tac \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ fs [io_ffi_def,io_ffi_oracle_def,io_proj2_def] \\ rveq \\ fs []
  THEN1
    (pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [stdout_fun_def,stdin_fun_def,io_proj1_def, ffi_putChar_def, ffi_getChar_def]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rveq \\ fs [GSYM fmap_EQ,FUN_EQ_THM]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rw [] \\ fs [] \\ rfs[] \\ metis_tac[])
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [stdout_fun_def,stdin_fun_def,io_proj1_def, ffi_putChar_def, ffi_getChar_def]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rveq \\ fs [GSYM fmap_EQ,FUN_EQ_THM]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rw [] \\ fs [] \\ rfs[] \\ pairarg_tac \\ Cases_on `inp'` \\ Cases_on `inp` \\ rw[] \\ fs[]
);

val _ = export_theory ()
