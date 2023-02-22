(*
  Contains the code for the entire CakeML basis library in basis_def.
*)
open preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib std_preludeTheory
     CommandLineProofTheory TextIOProofTheory RuntimeProofTheory PrettyPrinterProgTheory

val _ = new_theory "basisProg"

val _ = translation_extends"TextIOProg";

val print_e = ``Var(Long"TextIO"(Short"print"))``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val state = get_ml_prog_state () |> ml_progLib.get_state
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [state, env, print_e, state, mk_var ("x", v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  in v_thm end
val () = ml_prog_update (add_Dlet eval_thm "print");

val _ = ml_prog_update open_local_block;

val _ = (use_full_type_names := false);
val r = translate mlstringTheory.sum_sizes_def;
val r = translate mlstringTheory.make_app_list_ann_def;
val r = translate mlstringTheory.shrink_def;
val _ = (next_ml_names := ["str_app_list_opt"]);
val r = translate mlstringTheory.str_app_list_opt_def;
val _ = (use_full_type_names := true);

val _ = (append_prog o process_topdecs) `
  fun print_app_list_aux ls =
    (case ls of
       Nil => ()
     | List ls => TextIO.print_list ls
     | Append l1 l2 => (print_app_list_aux l1; print_app_list_aux l2))`;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  fun print_app_list ls = print_app_list_aux (str_app_list_opt ls)`;

val _ = ml_prog_update close_local_blocks;

Theorem print_app_list_aux_spec[local]:
   ∀ls lv out. APP_LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) print_app_list_aux_v [lv]
     (STDIO fs) (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat (append ls))))
Proof
  reverse(Cases_on`STD_streams fs`) >- (rw[STDIO_def] \\ xpull) \\
  pop_assum mp_tac \\ simp[PULL_FORALL] \\ qid_spec_tac`fs` \\
  reverse (Induct_on`ls`) \\ rw[APP_LIST_TYPE_def]
  >- (
    xcf_with_def () (fetch "-" "print_app_list_aux_v_def")
    \\ xmatch \\ xcon
    \\ DEP_REWRITE_TAC[GEN_ALL add_stdo_nil]
    \\ xsimpl \\ metis_tac[STD_streams_stdout])
  >- (
    xcf_with_def () (fetch "-" "print_app_list_aux_v_def")
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\ xsimpl
    \\ simp[Abbr`fs'`,STD_streams_add_stdout]
    \\ DEP_REWRITE_TAC[GEN_ALL add_stdo_o]
    \\ simp[mlstringTheory.concat_thm,mlstringTheory.strcat_thm]
    \\ xsimpl
    \\ metis_tac[STD_streams_stdout])
  \\ xcf_with_def () (fetch "-" "print_app_list_aux_v_def")
  \\ xmatch
  \\ xapp
  \\ simp[]
QED

Theorem print_app_list_spec:
   ∀ls lv out. APP_LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) print_app_list_v [lv]
     (STDIO fs) (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat (append ls))))
Proof
  rw []
  \\ xcf_with_def () (fetch "-" "print_app_list_v_def")
  \\ xlet_auto >- xsimpl
  \\ once_rewrite_tac [GSYM mlstringTheory.str_app_list_opt_thm]
  \\ xapp_spec print_app_list_aux_spec \\ fs []
QED

val _ = (append_prog o process_topdecs)
  `fun print_int i = TextIO.print (Int.toString i)`;

Theorem print_int_spec:
   INT i iv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "print_int" (get_ml_prog_state())) [iv]
     (STDIO fs) (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (toString i)))
Proof
  xcf"print_int"(get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl
QED

val _ = (append_prog o process_topdecs)
  `fun print_pp pp = print_app_list (PrettyPrinter.toAppList pp)`;

Theorem print_pp_spec:
   ∀pp lv out. PP_DATA_TYPE pp lv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "print_pp" (get_ml_prog_state())) [lv]
     (STDIO fs) (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat (append (pp_contents pp)))))
Proof
  xcf "print_pp" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
QED

val basis_st = get_ml_prog_state ();

val basis_prog = basis_st |> remove_snocs |> ml_progLib.get_prog;

val basis_def = Define `basis = ^basis_prog`;

Theorem basis_Decls_thm =
  ml_progLib.get_Decls_thm basis_st
  |> REWRITE_RULE [GSYM basis_def];

val _ = export_theory ()
