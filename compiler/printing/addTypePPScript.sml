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
  add_pp_decs fixes [] = [] /\
  (add_pp_decs fixes (Dmod modN decs :: decs2) =
    Dmod modN (add_pp_decs fixes decs) :: add_pp_decs fixes decs2) /\
  (add_pp_decs fixes (Dlocal ldecs decs :: decs2) =
    Dlocal (add_pp_decs fixes ldecs) (add_pp_decs fixes decs) :: add_pp_decs fixes decs2) /\
  (add_pp_decs fixes (d :: decs) = d :: pps_for_dec fixes d ++ add_pp_decs fixes decs)
Termination
  WF_REL_TAC `measure (list_size dec_size o SND)`
End

val _ = export_theory ();

