structure compute_reg_allocLib =
struct

local

open HolKernel boolLib bossLib computeLib
open parmoveTheory reg_allocTheory state_transformerTheory
open reg_alloc
open sptreeSyntax numSyntax listSyntax

in

fun add_reg_alloc_compset compset =
let
  val add_datatype = compute_basicLib.add_datatype compset
  val add_thms = Lib.C computeLib.add_thms compset
in
  add_datatype ``:ra_state``
  ; add_thms
    [reg_allocTheory.is_stack_var_def
    ,reg_allocTheory.undir_move_insert_def
    ,reg_allocTheory.reg_alloc_def
    ,reg_allocTheory.maybe_flip_def
    ,reg_allocTheory.briggs_coalesce_def
    ,reg_allocTheory.do_briggs_step_def
    ,reg_allocTheory.briggs_has_work_def
    ,reg_allocTheory.total_colour_def
    ,reg_allocTheory.aux_move_pref_def
    ,reg_allocTheory.move_pref_def
    ,reg_allocTheory.first_match_col_def
    ,reg_allocTheory.resort_moves_def
    ,reg_allocTheory.moves_to_sp_def
    ,reg_allocTheory.unspill_def
    ,reg_allocTheory.pri_move_insert_def
    ,reg_allocTheory.aux_pref_def
    ,reg_allocTheory.rpt_do_step2_def
    ,reg_allocTheory.do_step2_def
    ,reg_allocTheory.full_simplify_def
    ,reg_allocTheory.full_coalesce_def
    ,reg_allocTheory.full_coalesce_aux_def
    ,reg_allocTheory.deg_comparator_def
    ,reg_allocTheory.sec_ra_state_def
    ,reg_allocTheory.rpt_do_step_def
    ,reg_allocTheory.has_work_def
    ,reg_allocTheory.do_step_def
    ,reg_allocTheory.get_clock_def
    ,reg_allocTheory.dec_clock_def
    ,reg_allocTheory.coalesce_def
    ,reg_allocTheory.respill_def
    ,reg_allocTheory.pair_rename_def
    ,reg_allocTheory.do_coalesce_def
    ,reg_allocTheory.force_add_def
    ,reg_allocTheory.split_avail_def
    ,reg_allocTheory.is_coalesceable_move_def
    ,reg_allocTheory.is_valid_move_def
    ,reg_allocTheory.george_ok_def
    ,reg_allocTheory.briggs_ok_def
    ,reg_allocTheory.freeze_def
    ,reg_allocTheory.spill_def
    ,reg_allocTheory.max_non_coalesced_def
    ,reg_allocTheory.simplify_def
    ,reg_allocTheory.set_unavail_moves_def
    ,reg_allocTheory.revive_moves_def
    ,reg_allocTheory.dec_deg_def
    ,reg_allocTheory.dec_one_def
    ,reg_allocTheory.inc_one_def
    ,reg_allocTheory.get_edges_def
    ,reg_allocTheory.add_coalesce_def
    ,reg_allocTheory.freeze_node_def
    ,reg_allocTheory.add_unavail_moves_def
    ,reg_allocTheory.set_move_rel_def
    ,reg_allocTheory.get_unavail_moves_def
    ,reg_allocTheory.add_avail_moves_def
    ,reg_allocTheory.add_avail_moves_pri_def
    ,reg_allocTheory.set_avail_moves_def
    ,reg_allocTheory.set_avail_moves_pri_def
    ,reg_allocTheory.get_avail_moves_def
    ,reg_allocTheory.get_avail_moves_pri_def
    ,reg_allocTheory.set_coalesced_def
    ,reg_allocTheory.get_coalesced_def
    ,reg_allocTheory.set_deg_def
    ,reg_allocTheory.get_move_rel_def
    ,reg_allocTheory.get_colours_def
    ,reg_allocTheory.set_freeze_worklist_def
    ,reg_allocTheory.get_freeze_worklist_def
    ,reg_allocTheory.set_simp_worklist_def
    ,reg_allocTheory.get_simp_worklist_def
    ,reg_allocTheory.get_spill_worklist_def
    ,reg_allocTheory.set_spill_worklist_def
    ,reg_allocTheory.add_freeze_worklist_def
    ,reg_allocTheory.add_spill_worklist_def
    ,reg_allocTheory.add_simp_worklist_def
    ,reg_allocTheory.spill_colouring_def
    ,reg_allocTheory.get_deg_def
    ,reg_allocTheory.get_degs_def
    ,reg_allocTheory.push_stack_def
    ,reg_allocTheory.get_graph_def
    ,reg_allocTheory.get_stack_def
    ,reg_allocTheory.init_ra_state_def
    ,reg_allocTheory.split_priority_def
    ,reg_allocTheory.considered_var_def
    ,reg_allocTheory.in_moves_set_def
    ,reg_allocTheory.in_moves_def
    ,reg_allocTheory.count_degrees_def
    ,reg_allocTheory.option_filter_def
    ,reg_allocTheory.assign_colour2_def
    ,reg_allocTheory.remove_colours_def
    ,reg_allocTheory.unbound_colours_def
    ,reg_allocTheory.alloc_colouring_def
    ,reg_allocTheory.id_colour_def
    ,reg_allocTheory.alloc_colouring_aux_def
    ,reg_allocTheory.assign_colour_def
    ,reg_allocTheory.list_g_insert_def
    ,reg_allocTheory.clash_sets_to_sp_g_def
    ,reg_allocTheory.clique_g_insert_def
    ,reg_allocTheory.lookup_g_def
    ,reg_allocTheory.undir_g_insert_def
    ,reg_allocTheory.dir_g_insert_def
    ,reg_allocTheory.is_alloc_var_def
    ,reg_allocTheory.is_phy_var_def
    ]
  (*parmove*)
  ; add_thms
    [parmoveTheory.pmov_def
    ,parmoveTheory.parmove_def
    ,parmoveTheory.fstep_def
    ]
  end

val the_reg_alloc_compset =
  let
    val c = compute_basicLib.the_basic_compset
    val () = add_reg_alloc_compset c
  in
    c
  end

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

(*List of clash sets in HOL to unit sptree*)
fun dest_clash_set_list tm =
  let val (ls,_) = dest_list tm in
      map dest_unit_sptree ls
  end;

fun tup3 [x,y,z] =(x,(y,z))

fun dest_moves tm =
  let val (ls,_) = dest_list tm
      val split = map pairSyntax.strip_pair ls in
  map
  (fn p => tup3 (map int_of_term p)) split end

fun alloc_aux k [] = []
|   alloc_aux k ((clash_sets,moves)::xs) =
  let val clash_sets_poly = dest_clash_set_list clash_sets
      val moves_poly = dest_moves moves in
      irc_alloc clash_sets_poly k moves_poly :: alloc_aux k xs
  end;

(*Main thing to call for external allocator
  Should be passed a term of the form (k,(clashsetlist,moves) list)
*)
fun alloc_all t =
  let val (k,ls) = pairSyntax.dest_pair t 
    val clash_mov_ls = map pairSyntax.dest_pair (fst(listSyntax.dest_list ls)) in
    alloc_aux (int_of_term k) clash_mov_ls
  end

fun get_oracle t =
  let val cols = alloc_all t
      val alloc = listSyntax.mk_list (map mk_num_sptree cols,``:num num_map``) in
  ``let alloc = ^(alloc) in
    \n. if n >= LENGTH alloc then NONE else SOME(EL n alloc)``
  end

(* get_oracle ``(5n,[([LN;LN],[]);([LN;LN],[])])`` *)
end
end
