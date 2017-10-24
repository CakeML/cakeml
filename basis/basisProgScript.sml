open preamble ml_translatorLib ml_progLib mltextioProgTheory mltextioSpecTheory

val _ = new_theory "basisProg"

val _ = translation_extends"mltextioProg";

val basis_st = get_ml_prog_state ();

val basis_prog_state = save_thm("basis_prog_state",
  ml_progLib.pack_ml_prog_state basis_st);

val basis_prog = basis_st |> remove_snocs
  |> get_thm |> concl |> rator |> rator |> rator |> rand

val basis_def = Define `basis = ^basis_prog`;

val _ = export_theory ()
