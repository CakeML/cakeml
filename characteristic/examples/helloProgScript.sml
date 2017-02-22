open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     ioProgTheory basisFunctionsLib

val _ = new_theory "helloProg"

val _ = translation_extends"ioProg";

val hello = process_topdecs
  `fun hello u = print "Hello World!\n"`

val res = ml_prog_update(ml_progLib.add_prog hello pick_name)

val st = get_ml_prog_state ()

val hello_spec = Q.store_thm ("hello_spec",
  `!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [cv]
        (STDOUT [])
        (POSTv uv. STDOUT ("Hello World!\n"))`,
  xcf "hello" st 
  \\ xapp 
  \\ xsimpl \\ qexists_tac `emp` \\ qexists_tac `[]` \\ xsimpl 
); 

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val ML_code_thm = get_ml_prog_state() |> remove_snocs |> get_thm
val prog =  ML_code_thm |> SPEC_ALL |> concl |> rator |> rator |> rator |> rand 
val hello_dlet = mk_main_call (stringSyntax.fromMLstring "hello");
val hello_prog_tm = listSyntax.mk_snoc(hello_dlet,prog);
val hello_prog_def = Define`
  hello_prog = ^hello_prog_tm`;

val _ = export_theory ()
