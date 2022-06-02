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
val _ = set_grammar_ancestry ["ast", "infer", "namespace", "typeDecToPP",
    "sptree", "mlprettyprinter"];

Definition nsContents_def:
  nsContents (Bind locs mods) = MAP (Short ## I) locs ++
    FLAT (MAP (\(mn, ns). MAP (Long mn ## I) (nsContents ns)) mods)
Termination
  WF_REL_TAC `measure (namespace_size (K 0) (K 0) (K 0))`
End

(* The inferencer builds a mapping from type names to its internal
   type numbers, but the printer needs a reverse mapping to print
   inferred types. It maintains a mapping from type numbers to the
   list of names that have mapped to that type, whether or not they
   are current.

   There is also a mapping for "fixes" for type identifiers that
   were not defined with a matching pretty-printer, which is expected
   to only apply to some basis types.
*)
Datatype:
  type_names = <|
    id_map : (((modN, varN) id) list) num_map ;
    pp_fixes : (modN, varN, ((modN, varN) id) option) namespace
  |>
End

Definition empty_type_names_def:
  empty_type_names = <| id_map := sptree$LN; pp_fixes := nsEmpty |>
End

Definition add_type_name_def:
  add_type_name nm id id_map =
    let prev = case sptree$lookup id id_map of NONE => [] | SOME nms => nms in
    sptree$insert id (nm :: prev) id_map
End

Definition t_info_id_def:
  t_info_id (xs : string list, Tapp ts id) = SOME id /\
  t_info_id _ = NONE
End

Definition update_type_names_def:
  update_type_names ienv tn =
    let new = MAP (I ## t_info_id) (nsContents ienv.inf_t) in
    tn with <| id_map := FOLDR (\(nm, opt_id) id_map. case opt_id of NONE => id_map
        | SOME id => add_type_name nm id id_map) tn.id_map new |>
End

Definition strip_tapp_fun_def:
  strip_tapp_fun (Infer_Tapp [x; f] n) = (if n = Tfn_num
    then let (ys, t) = strip_tapp_fun f in
    (x :: ys, t)
    else ([], Infer_Tapp [x; f] n)) /\
  strip_tapp_fun t = ([], t)
End

Definition tn_current_def:
  tn_current ienv id nm = case nsLookup ienv.inf_v (pp_prefix nm) of
    NONE => F
  | SOME (_, t) =>
    let (params, _) = strip_tapp_fun t in
    (if NULL params then F else
     case LAST params of
        Infer_Tapp _ id2 => id2 = id
      | Infer_Tvar_db _ => T
      | _ => F
    )
End

Definition add_to_namespace_def:
  add_to_namespace (Short nm) x ns = nsBind nm x ns /\
  add_to_namespace (Long mnm id) x ns = (
    let m = case nsLookupMod ns [mnm] of NONE => nsEmpty | SOME m => m in
    nsAppend (nsLift mnm (add_to_namespace id x m)) ns)
End

Definition mk_namespace_def:
  mk_namespace xs = FOLDR (\(id, x). add_to_namespace id x) nsEmpty xs
End

Definition tn_setup_fixes_def:
  tn_setup_fixes ienv tn =
    let info = MAP (\(i, ns). MAP (\n. (n, tn_current ienv i n)) ns)
        (toSortedAList tn.id_map) in
    let fixes = FLAT (MAP (\ns.
        let not_ok = MAP FST (FILTER ($~ o SND) ns) in
        if NULL not_ok then []
        else
        let fst_ok = OPTION_MAP FST (FIND SND ns) in
        MAP (\nm. (nm, fst_ok)) not_ok)
     info) in
    tn with <| pp_fixes := mk_namespace fixes |>
End

Definition init_type_names_def:
  init_type_names ienv = tn_setup_fixes ienv
    (update_type_names ienv empty_type_names)
End

Definition get_tn_ok_def:
  get_tn_ok ienv tn id = OPTION_BIND (sptree$lookup id tn.id_map)
    (\ids. case (ids, FIND (tn_current ienv id) ids) of
        (_, SOME current_id) => SOME current_id
      | ([], NONE) => NONE
      | (id :: _, NONE) => (case nsLookup tn.pp_fixes id of
          NONE => NONE
        | SOME _ => (* it's ok to use this, pp_of_ast_t will cope *)
            SOME id
      ))
End

(* map the inferred type of a val to its AST counterpart, monomorphising
   any type variables to PrettyPrinter.default_type *)
Definition inf_t_to_ast_t_mono_def:
  inf_t_to_ast_t_mono ienv tn (Infer_Tuvar _) =
    SOME (Atapp [] (Long "PrettyPrinter" (Short "default_type"))) /\
  inf_t_to_ast_t_mono ienv tn (Infer_Tvar_db _) =
    SOME (Atapp [] (Long "PrettyPrinter" (Short "default_type"))) /\
  inf_t_to_ast_t_mono ienv tn (Infer_Tapp ts ti) =
    OPTION_BIND (OPT_MMAP (inf_t_to_ast_t_mono ienv tn) ts) (\ts.
    if ti = Tfn_num then
      (case ts of [t1; t2] => SOME (Atfun t1 t2) | _ => NONE)
    else if ti = Ttup_num then SOME (Attup ts)
    else
    OPTION_BIND (get_tn_ok ienv tn ti) (\nm. SOME (Atapp ts nm)))
Termination
  WF_REL_TAC `measure (infer_t_size o SND o SND)`
End

Definition type_con_name_def:
  type_con_name tn ti =
  (case sptree$lookup ti tn.id_map of
      NONE => strlit "<undeclared>"
    | SOME [] => strlit "<undeclared>"
    | SOME nms => implode (id_to_n (LAST nms))
  )
End

Definition inf_t_to_s_def:
  inf_t_to_s tn t = FST (inf_type_to_string_rec (type_con_name tn) t)
End

Definition print_of_val_opts_def:
  print_of_val_opts ienv tn (nm, inf_t) =
    let nm_str = id_to_str nm in
    let idl = Lit (StrLit nm_str) in
    let tstr = Lit (StrLit (explode (inf_t_to_s tn inf_t))) in
    let pp_hidden = Dlet unknown_loc Pany (App Opapp [Var (Short "print_pp");
        rpt_app (Var (Long "PrettyPrinter" (Short "val_hidden_type"))) [idl; tstr]]) in
    let pp_val = case inf_t_to_ast_t_mono ienv tn inf_t of
          NONE => []
        | SOME ast_t => [Dlet unknown_loc Pany (App Opapp [Var (Short "print_pp");
            rpt_app (Var (Long "PrettyPrinter" (Short "val_eq")))
                [idl; pp_of_ast_t tn.pp_fixes ast_t; Var nm; tstr]])] in
    (nm_str, pp_val ++ [pp_hidden])
End

Definition val_prints_def:
  val_prints tn prev_ienv decs_ienv =
    let tn2 = update_type_names decs_ienv tn in
    let full_ienv = extend_dec_ienv decs_ienv prev_ienv in
    let prints = MAP (print_of_val_opts full_ienv tn2)
        (MAP (I ## SND) (REVERSE (nsContents (ns_nub decs_ienv.inf_v)))) in
    (prints, tn2)
End

val _ = export_theory ();
