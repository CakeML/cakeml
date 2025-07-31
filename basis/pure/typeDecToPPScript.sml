(*
   Maps a Dtype or Dtabbrev declaration (the ast syntax) to
   the default pretty-printer function definition for it
   (also as ast syntax).

   Used by the compiler (in add-pp mode) to set up default
   pretty-printers for user types and by the basis translation
   to set up default pretty-printers for some basis types.
*)
Theory typeDecToPP
Ancestors
  ast string[qualified] mlint
Libs
  stringSyntax[qualified]


Definition pppre_def:
  pppre nm = "pp_" ++ nm
End

Definition pp_prefix_def:
  pp_prefix (Short nm) = Short (pppre nm) /\
  pp_prefix (Long nm id) = Long nm (pp_prefix id)
End

(* FIXME: is this elsewhere? *)
Definition mk_list_exp_def:
  mk_list_exp [] = Con (SOME (Short "[]")) [] /\
  mk_list_exp (x :: xs) = Con (SOME (Short "::")) [x; mk_list_exp xs]
End

Definition con_x_i_pat_def:
  con_x_i_pat cname n =
    Pcon cname (GENLIST (\i. Pvar ("x" ++ mlstring$explode (mlint$toString (& i)))) n)
End

Definition x_i_list_f_apps_def:
  x_i_list_f_apps fs = mk_list_exp
    (MAPi (\i f. App Opapp [f; Var (Short ("x" ++ mlstring$explode (mlint$toString (& i))))]) fs)
End

Definition mod_pp_def:
  mod_pp nm = Long "PrettyPrinter" nm
End

Definition rpt_app_def:
  rpt_app f [] = f /\
  rpt_app f (x :: xs) = rpt_app (App Opapp [f; x]) xs
End

Definition id_to_str_def:
  id_to_str (Short s) = s /\
  id_to_str (Long mnm id) = (mnm ++ "." ++ id_to_str id)
End

Definition pp_of_ast_t_def:
  pp_of_ast_t fixes (Atvar nm) = (Var (pp_prefix (Short nm))) /\
  pp_of_ast_t fixes (Atfun _ _) = (Fun "x" (Var (Short "pp_fun"))) /\
  pp_of_ast_t fixes (Atapp xs nm) = (case nsLookup fixes nm of
      NONE => rpt_app (Var (pp_prefix nm)) (MAP (pp_of_ast_t fixes) xs)
    | SOME NONE => (Fun "x" (App Opapp
            [Var (mod_pp (Short "unprintable")); Lit (StrLit (id_to_str nm))]))
    | SOME (SOME nm2) => rpt_app (Var (pp_prefix nm2)) (MAP (pp_of_ast_t fixes) xs)
  ) /\
  pp_of_ast_t fixes (Attup ts) = (Fun "x" (App Opapp
    [Var (mod_pp (Short "tuple")); Mat (Var (Short "x"))
        [(con_x_i_pat NONE (LENGTH ts), x_i_list_f_apps (MAP (pp_of_ast_t fixes) ts))]]))
End

Definition mk_pps_for_type_def:
  mk_pps_for_type fixes (tvars, nm, conss) =
    let (v, exp) = FOLDR (\nm (v, exp). (pppre nm, Fun v exp))
        ("x", Mat (Var (Short "x"))
            (MAP (\(conN, ts). (con_x_i_pat (SOME (Short conN)) (LENGTH ts),
                rpt_app (Var (mod_pp (Short "app_block"))) [Lit (StrLit conN);
                    (x_i_list_f_apps (MAP (pp_of_ast_t fixes) ts))])) conss)) tvars
    in
    (pppre nm, v, exp)
End

Definition mk_pp_type_def:
  mk_pp_type fixes (funs : type_def) = Dletrec unknown_loc (MAP (mk_pps_for_type fixes) funs)
End

Definition mk_pp_tabbrev_def:
  mk_pp_tabbrev fixes tvars nm ast_t = Dlet unknown_loc (Pvar (pppre nm))
    (FOLDR (\nm exp. Fun (pppre nm) exp) (pp_of_ast_t fixes ast_t) tvars)
End

Definition pps_for_dec_def:
  pps_for_dec fixes (Dtype locs type_def) = [mk_pp_type fixes type_def] /\
  pps_for_dec fixes (Dtabbrev locs tvars nm ast_t) = [mk_pp_tabbrev fixes tvars nm ast_t] /\
  pps_for_dec _ dec = []
End

