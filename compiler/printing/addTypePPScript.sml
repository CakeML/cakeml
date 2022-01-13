(*
   The first pass of adding print functions to source AST.
   Runs prior to type inference, and defines a pretty-print
   function per datatype definition.
*)

open HolKernel Parse boolLib bossLib;
open astTheory;
open typeDecToPPTheory;
local open stringTheory stringSyntax in end;

val _ = new_theory "addTypePP";
val _ = set_grammar_ancestry ["typeDecToPP", "ast", "string"];

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

Definition toplevel_add_pp_decs_def:
  toplevel_add_pp_decs _ [] = [] /\
  toplevel_add_pp_decs T (d :: ds) = add_pp_decs [d] ++ toplevel_add_pp_decs T ds /\
  toplevel_add_pp_decs F (d :: ds) = d :: toplevel_add_pp_decs (add_pp_begin d) ds
End

val _ = export_theory ();

