(*
   The second pass of the add-printing process. Type checks
   the AST and adds code to print "val x = ..." for every
   variable "x" bound in a declaration. This requires type
   checking to know the type of "x".
*)

open HolKernel Parse boolLib bossLib;
open astTheory inferTheory;
local open sptreeTheory stringTheory stringSyntax typeDecToPPTheory namespaceTheory
    mlprettyprinterTheory in end;

val _ = new_theory "addPrintVals";
val _ = set_grammar_ancestry ["ast", "infer", "namespace", "typeDecToPP", "sptree"];

Definition nsContents_def:
  nsContents (Bind locs mods) = MAP (Short ## I) locs ++
    FLAT (MAP (\(mn, ns). MAP (Long mn ## I) (nsContents ns)) mods)
Termination
  WF_REL_TAC `measure (namespace_size (K 0) (K 0) (K 0))`
End

Datatype:
  type_names = <|
    id_map : ((modN, varN) id) num_map ;
    nm_map : (modN, varN, num option) namespace
  |>
End

(* the inferencer builds a mapping from type names to its internal
   type numbers. we need to maintain a reverse mapping back to names *)
Definition add_type_name_def:
  add_type_name (nm, opt_id) tn =
    let id_map1 = (case nsLookup tn.nm_map (Short nm) of
        SOME (SOME n) => sptree$delete n tn.id_map
      | _ => tn.id_map
    ) in
    let id_map2 = case opt_id of NONE => id_map1
        | SOME n => sptree$insert n (Short nm) id_map1 in
    tn with <| id_map := id_map2; nm_map := nsBind nm opt_id tn.nm_map |>
End

Definition add_mod_type_names_def:
  add_mod_type_names (mod_nm, m) tn =
    let ids_removed = (case nsLookupMod tn.nm_map [mod_nm] of
        NONE => []
      | SOME m' => mapPartial SND (nsContents m')
    ) in
    let id_map1 = FOLDR sptree$delete tn.id_map ids_removed in
    let id_map2 = FOLDR (\(nm, opt_id) id_map. case opt_id of NONE => id_map
        | SOME n => sptree$insert n (Long mod_nm nm) id_map) id_map1 (nsContents m) in
    tn with <| id_map := id_map2 ; nm_map := nsAppend (nsLift mod_nm m) tn.nm_map |>
End

Definition t_info_id_def:
  t_info_id (xs : string list, Tapp ts id) = SOME id /\
  t_info_id _ = NONE
End

Definition inf_t_to_ast_t_def:
  inf_t_to_ast_t tn (Infer_Tuvar n) = SOME (Atvar ("t_u_" ++ explode (mlint$toString (&n)))) /\
  inf_t_to_ast_t tn (Infer_Tvar_db n) = SOME (Atvar ("t_" ++ explode (mlint$toString (&n)))) /\
  inf_t_to_ast_t tn (Infer_Tapp ts ti) =
    OPTION_BIND (OPT_MMAP (inf_t_to_ast_t tn) ts) (\ts. 
    OPTION_BIND (sptree$lookup ti tn.id_map) (\nm.
      SOME (Atapp ts nm)))
Termination
  WF_REL_TAC `measure (infer_t_size o SND)`
End

Definition id_str_def:
  id_str (Short s) = s /\
  id_str (Long mnm id) = (mnm ++ "." ++ id_str id)
End

Definition print_of_val_def:
  print_of_val tn (nm, inf_t) = (case inf_t_to_ast_t tn inf_t of
      NONE => []
    | SOME ast_t =>
    [Dlet unknown_loc Pany (App Opapp [Var (Short "print_pp");
        rpt_app (Var (Long "PrettyPrinter" (Short "val_eq")))
            [Lit (StrLit (id_str nm)); pp_of_ast_t ast_t; Var nm]])]
  )
End

Definition val_prints_def:
  val_prints tn ienv = (case nsMap t_info_id ienv.inf_t of
    Bind locs mods =>
    let tn1 = FOLDR add_type_name tn locs in
    let tn2 = FOLDR add_mod_type_names tn1 mods in
    let prints = MAP (print_of_val tn2) (MAP (I ## SND) (nsContents ienv.inf_v)) in
    tn2
  )
End

val _ = export_theory ();

