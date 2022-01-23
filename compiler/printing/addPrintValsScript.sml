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
    id_map : (((modN, varN) id) list # string)  num_map ;
    nm_map : (modN, varN, num option) namespace
  |>
End

Definition empty_type_names_def:
  empty_type_names = <| id_map := sptree$LN ; nm_map := nsEmpty |>
End

Definition delete_nm_def:
  delete_nm id_map n nm = (case sptree$lookup n id_map of
      NONE => id_map
    | SOME (ids, short_nm) => sptree$insert n (FILTER (\nm2. nm2 <> nm) ids, short_nm) id_map)
End

Definition add_nm_def:
  add_nm id_map n nm = (case sptree$lookup n id_map of
      NONE => sptree$insert n ([nm], id_to_n nm) id_map
    | SOME (ids, short_nm) => sptree$insert n (nm :: ids, short_nm) id_map)
End

(* the inferencer builds a mapping from type names to its internal
   type numbers. we need to maintain a reverse mapping back to names *)
Definition add_type_name_def:
  add_type_name (nm, opt_id) tn =
    let id_map1 = (case nsLookup tn.nm_map (Short nm) of
        SOME (SOME n) => delete_nm tn.id_map n (Short nm)
      | _ => tn.id_map
    ) in
    let id_map2 = case opt_id of NONE => id_map1
        | SOME n => add_nm id_map1 n (Short nm) in
    tn with <| id_map := id_map2; nm_map := nsBind nm opt_id tn.nm_map |>
End

Definition add_mod_type_names_def:
  add_mod_type_names v_ns (mod_nm, m) tn =
    let removed_contents = (case nsLookupMod tn.nm_map [mod_nm] of
        NONE => []
      | SOME m' => nsContents m'
    ) in
    let id_map1 = FOLDR (\(nm, opt_id) id_map. case opt_id of NONE => id_map
        | SOME n => delete_nm id_map n nm) tn.id_map removed_contents in
    let added = nsContents m in
    let added_ok = FILTER (\(nm, _). IS_SOME
            (nsLookup v_ns (pp_prefix (Long mod_nm nm)))) added in
    let id_map2 = FOLDR (\(nm, opt_id) id_map. case opt_id of NONE => id_map
        | SOME n => add_nm id_map n (Long mod_nm nm)) id_map1 added_ok in
    tn with <| id_map := id_map2 ; nm_map := nsAppend (nsLift mod_nm m) tn.nm_map |>
End

Definition t_info_id_def:
  t_info_id (xs : string list, Tapp ts id) = SOME id /\
  t_info_id _ = NONE
End

Definition update_type_names_def:
  update_type_names ienv tn = (case nsMap t_info_id ienv.inf_t of
    Bind locs mods =>
    let tn1 = FOLDR add_type_name tn locs in
    let tn2 = FOLDR (add_mod_type_names ienv.inf_v) tn1 mods in
    tn2
  )
End

Definition inf_t_to_ast_t_def:
  inf_t_to_ast_t tn (Infer_Tuvar n) = SOME (Atvar ("'t_u_" ++ explode (mlint$toString (&n)))) /\
  inf_t_to_ast_t tn (Infer_Tvar_db n) = SOME (Atvar ("'t_" ++ explode (mlint$toString (&n)))) /\
  inf_t_to_ast_t tn (Infer_Tapp ts ti) =
    OPTION_BIND (OPT_MMAP (inf_t_to_ast_t tn) ts) (\ts.
    if ti = Tfn_num then
      (case ts of [t1; t2] => SOME (Atfun t1 t2) | _ => NONE)
    else if ti = Ttup_num then SOME (Attup ts)
    else
    OPTION_BIND (sptree$lookup ti tn.id_map) (\(nms, _).
      case nms of [] => NONE | (nm :: _) => SOME (Atapp ts nm)))
Termination
  WF_REL_TAC `measure (infer_t_size o SND)`
End

Definition inf_t_to_str_def:
  inf_t_to_str tn (Infer_Tuvar n) = ("'t_u_" ++ explode (mlint$toString (&n))) /\
  inf_t_to_str tn (Infer_Tvar_db n) = ("'t_" ++ explode (mlint$toString (&n))) /\
  inf_t_to_str tn (Infer_Tapp ts ti) =
    let tss = MAP (inf_t_to_str tn) ts in
    let tss1 = TAKE 1 tss in
    let tss2 = DROP 1 tss in
    if ti = Tfn_num /\ LENGTH ts = 2
    then FLAT (["("] ++ tss1 ++ [" -> "] ++ tss2 ++ [")"])
    else if ti = Ttup_num
    then FLAT (["("] ++ tss1 ++ MAP (\s. ", " ++ s) tss2 ++ [")"])
    else
    let tc_str = case sptree$lookup ti tn.id_map of
        NONE => "unexpected" | SOME (_, nm) => nm
    in
    if NULL ts then tc_str
    else FLAT (["("] ++ tss1 ++ MAP (\s. " " ++ s) tss2 ++ [" "; tc_str; ")"])
Termination
  WF_REL_TAC `measure (infer_t_size o SND)`
End

Definition id_str_def:
  id_str (Short s) = s /\
  id_str (Long mnm id) = (mnm ++ "." ++ id_str id)
End

Definition print_of_val_def:
  print_of_val tn (nm, inf_t) =
    let idl = Lit (StrLit (id_str nm)) in
    let tstr = Lit (StrLit (inf_t_to_str tn inf_t)) in
    Dlet unknown_loc Pany (App Opapp [Var (Short "print_pp");
        (case inf_t_to_ast_t tn inf_t of
          NONE => rpt_app (Var (Long "PrettyPrinter" (Short "val_hidden_type"))) [idl; tstr]
        | SOME ast_t => rpt_app (Var (Long "PrettyPrinter" (Short "val_eq")))
            [idl; pp_of_ast_t ast_t; Var nm; tstr])])
End

Definition val_prints_def:
  val_prints tn ienv =
    let tn2 = update_type_names ienv tn in
    let prints = MAP (print_of_val tn2)
        (MAP (I ## SND) (REVERSE (nsContents (ns_nub ienv.inf_v)))) in
    (prints, tn2)
End

val _ = export_theory ();

