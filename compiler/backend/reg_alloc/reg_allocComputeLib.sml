structure reg_allocComputeLib =
struct

local

open HolKernel boolLib bossLib computeLib
open parmoveTheory reg_allocTheory state_transformerTheory
open reg_alloc
open sptreeSyntax numSyntax listSyntax
open basicComputeLib

in

val add_reg_alloc_compset = extend_compset
  [Tys [``:ra_state``, ``:tag``, ``:clash_tree``, ``:ira_state``],
   Defs
   [reg_allocTheory.st_ex_FOREACH_def,
    reg_allocTheory.st_ex_MAP_def,
    reg_allocTheory.st_ex_PARTITION_def,
    reg_allocTheory.st_ex_FILTER_def,
    reg_allocTheory.list_remap_def,
    reg_allocTheory.mk_bij_aux_def,
    reg_allocTheory.mk_bij_def,
    reg_allocTheory.is_phy_var_def,
    reg_allocTheory.sp_default_def,
    reg_allocTheory.extract_tag_def,
    sptreeTheory.fromAList_def,
    reg_allocTheory.dec_deg_def,
    reg_allocTheory.dec_degree_def,
    reg_allocTheory.add_simp_wl_def,
    reg_allocTheory.add_stack_def,
    reg_allocTheory.split_degree_def,
    reg_allocTheory.unspill_def,
    reg_allocTheory.do_simplify_def,
    reg_allocTheory.st_ex_list_MAX_deg_def,
    reg_allocTheory.do_spill_def,
    reg_allocTheory.do_step_def,
    reg_allocTheory.rpt_do_step_def,
    reg_allocTheory.remove_colours_def,
    reg_allocTheory.assign_Atemp_tag_def,
    reg_allocTheory.assign_Atemps_def,
    reg_allocTheory.tag_col_def,
    reg_allocTheory.unbound_colour_def,
    reg_allocTheory.assign_Stemp_tag_def,
    reg_allocTheory.assign_Stemps_def,
    reg_allocTheory.first_match_col_def,
    reg_allocTheory.biased_pref_def,
    reg_allocTheory.insert_edge_def,
    reg_allocTheory.list_insert_edge_def,
    reg_allocTheory.clique_insert_edge_def,
    reg_allocTheory.extend_clique_def,
    reg_allocTheory.mk_graph_def,
    reg_allocTheory.extend_graph_def,
    reg_allocTheory.mk_tags_def,
    reg_allocTheory.init_ra_state_def,
    reg_allocTheory.is_Atemp_def,
    reg_allocTheory.init_alloc1_heu_def,
    reg_allocTheory.do_alloc1_def,
    reg_allocTheory.extract_color_def,
    reg_allocTheory.do_reg_alloc_def,
    reg_allocTheory.reg_alloc_aux_def,
    reg_allocTheory.run_ira_state_def,
    reg_allocTheory.pri_move_insert_def,
    reg_allocTheory.undir_move_insert_def,
    reg_allocTheory.moves_to_sp_def,
    reg_allocTheory.resort_moves_def,
    reg_allocTheory.reg_alloc_def,
    reg_allocTheory.numset_list_delete_def,
    reg_allocTheory.check_clash_tree_def,
    reg_allocTheory.check_partial_col_def,
    reg_allocTheory.check_col_def,
    (*parmove*)
    parmoveTheory.pmov_def,
    parmoveTheory.parmove_def,
    parmoveTheory.fstep_def
    ]]

val ERR = mk_HOL_ERR"reg_allocComputeLib";


(* unit sptree to ML unit sptree_spt*)
fun dest_unit_sptree tm =
 case Lib.total boolSyntax.dest_strip_comb tm of
    SOME ("sptree$LN", []) => Ln
  | SOME ("sptree$LS", [t]) => Ls ()
  | SOME ("sptree$BN", [t1, t2]) => Bn (dest_unit_sptree t1, dest_unit_sptree t2)
  | SOME ("sptree$BS", [t1, v, t2]) => Bs (dest_unit_sptree t1, (), dest_unit_sptree t2)
  | _ => raise ERR "dest_unit_sptree" "";

(*Int ML sptree to HOL num sptree*)
fun mk_num_sptree t =
 case t of
    Ln => mk_ln ``:num``
  | Ls a => mk_ls (term_of_int a)
  | Bn (Ln, t2) =>
       let
          val tm = mk_num_sptree t2
       in
          mk_bn (mk_ln ``:num``, tm)
       end
  | Bn (t1, Ln) =>
       let
          val tm = mk_num_sptree t1
       in
          mk_bn (tm, mk_ln (sptree_ty_of tm))
       end
  | Bn (t1, t2) => mk_bn (mk_num_sptree t1, mk_num_sptree t2)
  | Bs (t1, a, t2) =>
       let
          val ln = mk_ln ``:num``
          val tm1 = if t1 = Ln then ln else mk_num_sptree t1
          val tm2 = if t2 = Ln then ln else mk_num_sptree t2
       in
          mk_bs (tm1, (term_of_int a), tm2)
       end;

(*List of clash in HOL to unit sptree*)
fun dest_clash_tree tm =
  case Lib.total boolSyntax.dest_strip_comb tm of
    SOME ("reg_alloc$Delta", [t1,t2]) => Delta (map int_of_term (fst(listSyntax.dest_list t1)),map int_of_term (fst(listSyntax.dest_list t2)))
  | SOME ("reg_alloc$Set", [t]) => Set (dest_unit_sptree t)
  | SOME ("reg_alloc$Seq", [t1, t2]) => Seq (dest_clash_tree t1, dest_clash_tree t2)
  | SOME ("reg_alloc$Branch", [opt, t1, t2]) =>
    if optionSyntax.is_none opt then
      Branch (NONE,dest_clash_tree t1,dest_clash_tree t2)
    else
      Branch (SOME((dest_unit_sptree o optionSyntax.dest_some) opt),dest_clash_tree t1,dest_clash_tree t2)
  | _ => raise ERR "dest_clash_tree" "";

fun tup2 l = case l of [a, b] => (a, b) | _ => raise General.Bind
fun tup3 l = case l of [a, b, c] => (a, (b, c)) | _ => raise General.Bind

fun dest_moves tm =
  let val (ls,_) = dest_list tm
      val split = map pairSyntax.strip_pair ls in
  map
  (fn p => tup3 (map int_of_term p)) split end

fun dest_forced tm =
  let val (ls,_) = dest_list tm
      val split = map pairSyntax.strip_pair ls in
  map
  (fn p => tup2 (map int_of_term p)) split end

fun alloc_aux alg k [] n = (print"\n";[])
|   alloc_aux alg k ([clash_tree,moves,force]::xs) n =
  let val _ = print (strcat (Int.toString n) " ")
      val clash_tree_poly = dest_clash_tree clash_tree
      val moves_poly = dest_moves moves
      val force_poly = dest_forced force
      val res = reg_alloc k moves_poly clash_tree_poly force_poly in
    case res of
      Success s => s:: alloc_aux alg k xs (n+1)
    | Failure e => raise ERR "reg_alloc" "failure"
  end
|   alloc_aux _ _ _ _ = raise General.Bind;

(*Main thing to call for external allocator
  Should be passed a term of the form (k,(clashsetlist,moves) list)
*)
fun alloc_all alg t =
  let val (k,ls) = pairSyntax.dest_pair t
      val _ = print ("Num regs: "^Int.toString (int_of_term k) ^" Alg: "^Int.toString alg^ "\n")
    val clash_mov_ls = map pairSyntax.strip_pair (fst(listSyntax.dest_list ls)) in
    alloc_aux alg (int_of_term k) clash_mov_ls 0
  end

fun get_oracle alg t =
  let val cols = alloc_all alg t
      val alloc = listSyntax.mk_list (map mk_num_sptree cols,``:num num_map``) in
  ``let alloc = ^(alloc) in
    \n. if n >= LENGTH alloc then NONE else SOME(EL n alloc)``
  end

(*
get_oracle 3 ``(5n,[(Seq (Delta [1;2;3][]) (Set LN),[],[(1n,2n)]);Set LN,[(1n,1n,2n)],[]])``
*)

end
end
