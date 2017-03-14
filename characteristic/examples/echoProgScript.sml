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
  `!ls b bv. cl <> [] /\ EVERY validArg cl /\ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ==>
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * STDERR err * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * (STDOUT (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) 
                               * STDERR err * COMMANDLINE cl))`,
    xcf "echo" st
    \\ xlet `POSTv zv. & UNIT_TYPE () zv * STDOUT output * STDERR err * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv argv. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) argv * STDOUT output
      * STDERR err * COMMANDLINE cl`
    >-(xapp \\ instantiate \\ xsimpl
       \\ simp[MAP_TL,NULL_EQ,LENGTH_FLAT,MAP_MAP_o,o_DEF] (* TODO: this is duplicated in grepProg *)
       \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
       \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
       \\ simp[MAP_K_REPLICATE,SUM_REPLICATE,GSYM LENGTH_FLAT])
    \\ xlet `POSTv clv. STDOUT output * STDERR err * COMMANDLINE cl * & STRING_TYPE (implode (CONCAT_WITH " " (TL cl))) clv`
    >-(xapp \\ xsimpl \\ instantiate
      \\ rw[mlstringTheory.concatWith_CONCAT_WITH, mlstringTheory.implode_explode, Once mlstringTheory.implode_def]
      \\ Cases_on `cl` \\ fs[mlstringTheory.implode_def])
    \\ xlet `POSTv xv. &UNIT_TYPE () xv * STDOUT (output ++ (CONCAT_WITH " " (TL cl))) 
                                        * STDERR err * COMMANDLINE cl`
    >-(xapp \\ qexists_tac `STDERR err * COMMANDLINE cl` \\ xsimpl \\ 
       qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
      \\ rw[mlstringTheory.explode_implode] \\ xsimpl)
    \\ xapp \\ map_every qexists_tac [`STDERR err * COMMANDLINE cl`, `output ++ (CONCAT_WITH " " (TL cl))`, `(CHR 10)`] \\ xsimpl
);

val st = get_ml_prog_state();
val spec = echo_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "echo";
val (call_thm_echo, echo_prog_tm) = call_thm st name spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;

val echo_semantics = save_thm("echo_semantics",
  call_thm_echo
  |> ONCE_REWRITE_RULE[GSYM echo_prog_def]
  |> DISCH_ALL
  |> REWRITE_RULE[APPEND]);

val _ = export_theory();
