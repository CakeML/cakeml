(*
   The first pass of adding print functions to source AST.
   Runs prior to type inference, and defines a pretty-print
   function per datatype definition.
*)

open HolKernel Parse boolLib bossLib;
open astTheory;
local open stringTheory stringSyntax in end;

val _ = new_theory "addTypePP";
val _ = set_grammar_ancestry ["ast", "string"];

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

Definition con_xi_pat_def:
  con_xi_pat cname n =
    Pcon cname (GENLIST (\i. Pvar ("x" ++ num_to_hex_string i)) n)
End

Definition xi_list_f_apps_def:
  xi_list_f_apps fs = mk_list_exp
    (MAPi (\i f. App Opapp [f; Var (Short ("x" ++ num_to_hex_string i))]) fs)
End

Definition pp_of_ast_t_def:
  pp_of_ast_t (Atvar nm) = (Var (pp_prefix (Short nm))) /\
  pp_of_ast_t (Atfun _ _) = (Fun "x" (Var (Short "pp_fun"))) /\
  pp_of_ast_t (Atapp xs nm) = (App Opapp (Var (pp_prefix nm) :: MAP pp_of_ast_t xs)) /\
  pp_of_ast_t (Attup ts) = (Fun "x" (App Opapp
    [Var (Short "pp_paren_tuple"); Mat (Var (Short "x"))
        [(con_xi_pat NONE (LENGTH ts), xi_list_f_apps (MAP pp_of_ast_t ts))]]))
Termination
  WF_REL_TAC `measure ast_t_size`
End

Definition mk_pps_for_type_def:
  mk_pps_for_type (tvars, nm, conss) =
    (pppre nm, "x", Mat (Var (Short "x"))
        (MAP (\(conN, ts). (con_xi_pat (SOME (Short conN)) (LENGTH ts),
            App Opapp [Var (Short "pp_app_block"); Lit (StrLit conN);
                (xi_list_f_apps (MAP pp_of_ast_t ts))])) conss))
End

Definition mk_pp_type_def:
  mk_pp_type (funs : type_def) = Dletrec unknown_loc (MAP mk_pps_for_type funs)
End

Definition mk_pp_tabbrev_def:
  mk_pp_tabbrev tvars nm ast_t = Dlet unknown_loc (Pvar ("pp_" ++ nm))
    (FOLDL (\exp nm. Fun ("pp_" ++ nm) exp) (pp_of_ast_t ast_t) tvars)
End

Definition pps_for_dec_def:
  pps_for_dec (Dtype locs type_def) = [mk_pp_type type_def] /\
  pps_for_dec (Dtabbrev locs tvars nm ast_t) = [mk_pp_tabbrev tvars nm ast_t] /\
  pps_for_dec dec = []
End

Definition add_pp_decs_def:
  add_pp_decs [] = [] /\
  (add_pp_decs (Dmod modN decs :: decs2) =
    Dmod modN (add_pp_decs decs) :: add_pp_decs decs2) /\
  (add_pp_decs (Dlocal ldecs decs :: decs2) =
    Dlocal (add_pp_decs ldecs) (add_pp_decs decs) :: add_pp_decs decs2) /\
  (add_pp_decs (d :: decs) = d :: pps_for_dec d ++ add_pp_decs decs)
Termination
  WF_REL_TAC `measure (list_size dec_size)`
End

Definition pp_begin_marker_def:
  pp_begin_marker = "pp_fun"
End

Definition add_pp_begin_def:
  (add_pp_begin (Dlet _ pat _) = EXISTS (\nm. nm = pp_begin_marker) (pat_bindings pat [])) /\
  (add_pp_begin (Dletrec _ recs) = EXISTS (\(nm, _, _). nm = pp_begin_marker) recs) /\
  (add_pp_begin _ = F)
End

Definition toplevel_add_decs_def:
  toplevel_add_decs prev [] = [] /\
  toplevel_add_decs prev (d :: ds) = d :: (if add_pp_begin d
    then REVERSE prev ++ add_pp_decs ds
    else toplevel_add_decs (pps_for_dec d ++ prev) ds)
End

val _ = export_theory ();

