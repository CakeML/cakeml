(*
  Contains the code for the entire CakeML basis library in basis_def.
*)
open preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib
     CommandLineProofTheory TextIOProofTheory RuntimeProofTheory PrettyPrinterProgTheory

val _ = new_theory "basisProg"

val _ = translation_extends"PrettyPrinterProg";

val print_e = ``Var(Long"TextIO"(Short"print"))``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val state = get_ml_prog_state () |> ml_progLib.get_state
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [state, env, print_e, state, mk_var ("x", v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  in v_thm end
val () = ml_prog_update (add_Dlet eval_thm "print" []);

val print_app_list = process_topdecs
  `fun print_app_list ls =
   (case ls of
      Nil => ()
    | List ls => TextIO.print_list ls
    | Append l1 l2 => (print_app_list l1; print_app_list l2))`;
val () = append_prog print_app_list;

Theorem print_app_list_spec:
   ∀ls lv out. APP_LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "print_app_list" (get_ml_prog_state())) [lv]
     (STDIO fs) (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat (append ls))))
Proof
  reverse(Cases_on`STD_streams fs`) >- (rw[STDIO_def] \\ xpull) \\
  pop_assum mp_tac \\ simp[PULL_FORALL] \\ qid_spec_tac`fs` \\
  reverse (Induct_on`ls`) \\ rw[APP_LIST_TYPE_def]
  >- (
    xcf "print_app_list" (get_ml_prog_state())
    \\ xmatch \\ xcon
    \\ DEP_REWRITE_TAC[GEN_ALL add_stdo_nil]
    \\ xsimpl \\ metis_tac[STD_streams_stdout])
  >- (
    xcf "print_app_list" (get_ml_prog_state())
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
  \\ xcf "print_app_list" (get_ml_prog_state())
  \\ xmatch
  \\ xapp
  \\ simp[]
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

val basis_st = get_ml_prog_state ();

val basis_prog_state = save_thm("basis_prog_state",
  ml_progLib.pack_ml_prog_state basis_st);

val basis_prog = basis_st |> remove_snocs |> ml_progLib.get_prog;

val basis_def = Define `basis = ^basis_prog`;

val _ = export_theory ()
