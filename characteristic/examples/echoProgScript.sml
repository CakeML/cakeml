open preamble
     semanticPrimitivesTheory miscTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     mlcommandLineProgTheory basisFunctionsLib

val _ = new_theory "echo";

val _ = translation_extends"mlcommandLineProg";

(*TODO: update this to include Char.fromByte and move to a more appropriate location*)
val print = process_topdecs
  `fun print s =
    let 
      val l = String.explode s
      val nl = List.map_1 (Char.ord) l
      val bl = List.map_1 (Word8.fromInt) nl
    in write_list bl end`

val res = ml_prog_update(ml_progLib.add_prog print pick_name)

val echo = process_topdecs
  `fun echo u = 
      let 
        val cl = commandLine.arguments ()
        val cls = String.concatwith " " cl
      in print cls end`

val res = ml_prog_update(ml_progLib.add_prog echo pick_name)

val st = get_ml_prog_state()


(*TODO fix the use of map_1 instead of map *)
val map_1_v_thm = fetch "mllistProg" "map_1_v_thm";
val string_map_v_thm = save_thm("string_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:char``, beta|->``:num``])
val byte_map_v_thm = save_thm("byte_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:num``, beta|->``:word8``])


val print_spec = Q.store_thm("print",
  `!s sv. STRING_TYPE s sv ==>
   app (p:'ffi ffi_proj) ^(fetch_v "print" st) [sv]
   (STDOUT output)
   (POSTv uv. STDOUT (output ++ MAP (n2w o ORD) (explode s)))`,  
    xcf "print" st
    \\ xlet `POSTv lv. & LIST_TYPE CHAR (explode s) lv * STDOUT output`
    >-(xapp \\ xsimpl \\ instantiate)
    \\ xlet `POSTv nlv. & LIST_TYPE NUM (MAP ORD (explode s)) nlv * STDOUT output`
    >-(xapp_spec string_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `ORD` \\ qexists_tac `NUM`  \\ rw[mlcharProgTheory.char_ord_v_thm])
    \\ xlet `POSTv blv. & LIST_TYPE (WORD:word8 -> v -> bool) (MAP n2w (MAP ORD (explode s))) blv * STDOUT output`    
    >-(xapp_spec byte_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `n2w` \\ qexists_tac `WORD` \\ rw[mlword8ProgTheory.word8_fromint_v_thm])
    \\ xapp \\ fs[MAP_MAP_o]
);

val echo_spec = Q.store_thm("echo",
  `!ls. UNIT_TYPE u uv /\ cl <> [] /\ EVERY validArg cl /\
   LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))) < 257 ==>
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [uv]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. STDOUT (output ++ MAP (n2w o ORD) (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl)`,  
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
    \\ xapp \\ qexists_tac `COMMANDLINE cl` \\ xsimpl \\ qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
    \\ rw[mlstringTheory.explode_implode] \\ xsimpl 
);

val _ = export_theory();
