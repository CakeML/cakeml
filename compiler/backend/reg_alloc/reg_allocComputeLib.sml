(*
  A compset for evaluating the register allocators and parallel move
  compiler.
*)
structure reg_allocComputeLib =
struct

local

open HolKernel boolLib bossLib computeLib
open parmoveTheory reg_allocTheory state_transformerTheory
open reg_alloc
open sptreeSyntax numSyntax listSyntax
open basicComputeLib

in

val ERR = mk_HOL_ERR"reg_allocComputeLib";

(* --- cv --- *)

datatype cv = Num of int | Pair of cv * cv;

fun cv_of_term tm =
  if cvSyntax.is_cv_num tm then
    Num (numSyntax.int_of_term (rand tm))
  else if cvSyntax.is_cv_pair tm then
    let
      val (t1,t2) = cvSyntax.dest_cv_pair tm
    in
      Pair (cv_of_term t1, cv_of_term t2)
    end
  else (print_term tm; fail());

fun cv_fst (Pair (p, q)) = p | cv_fst (Num m) = Num 0;
fun cv_snd (Pair (p, q)) = q | cv_snd (Num m) = Num 0;

fun cv_has_shape v w =
  case (v,w) of
    ([],c) => true
  | (NONE::xs, Pair (x,y)) => cv_has_shape xs y
  | ((SOME n)::xs, Pair (x,y)) => x = Num n andalso cv_has_shape xs y
  | _ => false;

fun to_unit x = ();

fun to_pair t1 t2 (Pair (x, y)) = (t1 x,t2 y)
  | to_pair t1 t2 (Num v4) = fail();

fun to_list f (Num n) = []
  | to_list f (Pair (x, y)) = f x :: to_list f y;

fun c2n (Num n) = n
  | c2n _ = fail();

fun to_option t (Num n) = NONE
  | to_option t (Pair (x, y)) = SOME (t y);

fun to_sptree_spt t0 v =
  if cv_has_shape [SOME 2, NONE] v then
    Bn (to_sptree_spt t0 (cv_fst (cv_snd v)),
        to_sptree_spt t0 (cv_snd (cv_snd v)))
  else if cv_has_shape [SOME 3, NONE, NONE] v then
    Bs (to_sptree_spt t0 (cv_fst (cv_snd v)),
        t0 (cv_fst (cv_snd (cv_snd v))),
        to_sptree_spt t0 (cv_snd (cv_snd (cv_snd v))))
  else if v = Num 0 then Ln
  else Ls (t0 (cv_snd v));

fun to_reg_alloc_clash_tree v =
  if cv_has_shape [SOME 2, NONE, NONE] v then
    Branch (to_option (to_sptree_spt to_unit) (cv_fst (cv_snd v)),
            to_reg_alloc_clash_tree (cv_fst (cv_snd (cv_snd v))),
            to_reg_alloc_clash_tree (cv_snd (cv_snd (cv_snd v))))
  else if cv_has_shape [SOME 3, NONE] v then
    Seq (to_reg_alloc_clash_tree (cv_fst (cv_snd v)),
         to_reg_alloc_clash_tree (cv_snd (cv_snd v)))
  else if cv_has_shape [SOME 0, NONE] v then
    Delta (to_list c2n (cv_fst (cv_snd v)),
           to_list c2n (cv_snd (cv_snd v)))
  else Set (to_sptree_spt to_unit (cv_snd v));

val to_fun =
  to_pair c2n
    (to_list
       (to_pair to_reg_alloc_clash_tree
          (to_pair (to_list (to_pair c2n (to_pair c2n c2n)))
             (to_pair (to_option (to_sptree_spt c2n))
                (to_pair (to_list (to_pair c2n c2n))
                  (to_sptree_spt to_unit)
                  )))));

(* --- direct version --- *)

fun alloc_aux alg k [] n = (print"\n"; [])
  | alloc_aux alg k ((clash_tree,(moves,(sc,(force,fs))))::xs) n =
      let
        val _ = print (strcat (Int.toString n) " ")
        val clash_tree_poly = clash_tree
        val moves_poly = moves
        val force_poly = force
        val fs_poly = fs
        val sc_poly = sc
        val res = reg_alloc alg sc_poly k moves_poly clash_tree_poly force_poly fs_poly
      in
        case res of
          Success s => s :: alloc_aux alg k xs (n + 1)
        | Failure e => raise ERR "reg_alloc" "failure"
      end
  | alloc_aux _ _ _ _ = raise General.Bind;

(*
  Main thing to call for external allocator
  Should be passed a term of the form (k,(clashsetlist,moves) list)
*)

fun alg_to_str Simple = "Simple"
  | alg_to_str Irc = "IRC";

fun alloc_all_raw alg graphs_raw =
  let
    val (k,datals) = cv_of_term (rand graphs_raw) |> to_fun;
    val _ = print ("Num regs: "^Int.toString k ^" Alg: "^alg_to_str alg^ "\n")
  in
    alloc_aux alg k datals 0
  end

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

fun get_oracle_raw alg t =
  let
    val cols = alloc_all_raw alg t
  in
    listSyntax.mk_list
      (map (optionSyntax.mk_some o mk_num_sptree) cols,
       ``:num num_map option``)
  end;

(* --- old version --- *)

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
    reg_allocTheory.add_spill_wl_def,
    reg_allocTheory.add_freeze_wl_def,
    reg_allocTheory.push_stack_def,
    reg_allocTheory.add_unavail_moves_wl_def,
    reg_allocTheory.split_degree_def,
    reg_allocTheory.sort_moves_def,
    reg_allocTheory.smerge_def,
    reg_allocTheory.revive_moves_def,
    reg_allocTheory.unspill_def,
    reg_allocTheory.do_simplify_def,
    reg_allocTheory.inc_deg_def,
    reg_allocTheory.do_coalesce_real_def,
    reg_allocTheory.bg_ok_def,
    reg_allocTheory.is_Fixed_def,
    reg_allocTheory.consistency_ok_def,
    reg_allocTheory.st_ex_FIRST_def,
    reg_allocTheory.do_coalesce_def,
    reg_allocTheory.is_not_coalesced_def,
    reg_allocTheory.reset_move_related_def,
    reg_allocTheory.do_prefreeze_def,
    reg_allocTheory.do_freeze_def,
    reg_allocTheory.safe_div_def,
    reg_allocTheory.sorted_insert_def,
    reg_allocTheory.sorted_mem_def,
    reg_allocTheory.update_move_def,
    reg_allocTheory.coalesce_parent_def,
    reg_allocTheory.do_upd_coalesce_def,
    miscTheory.lookup_any_def,
    reg_allocTheory.st_ex_list_MIN_cost_def,
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


(* unit sptree to ML unit sptree_spt*)
fun dest_unit_sptree tm =
 case Lib.total boolSyntax.dest_strip_comb tm of
    SOME ("sptree$LN", []) => Ln
  | SOME ("sptree$LS", [t]) => Ls ()
  | SOME ("sptree$BN", [t1, t2]) => Bn (dest_unit_sptree t1, dest_unit_sptree t2)
  | SOME ("sptree$BS", [t1, v, t2]) => Bs (dest_unit_sptree t1, (), dest_unit_sptree t2)
  | _ => raise ERR "dest_unit_sptree" "";

(* int sptree to ML int sptree_spt*)
fun dest_int_sptree tm =
 case Lib.total boolSyntax.dest_strip_comb tm of
    SOME ("sptree$LN", []) => Ln
  | SOME ("sptree$LS", [v]) => Ls (int_of_term v)
  | SOME ("sptree$BN", [t1, t2]) => Bn (dest_int_sptree t1, dest_int_sptree t2)
  | SOME ("sptree$BS", [t1, v, t2]) => Bs (dest_int_sptree t1, int_of_term v, dest_int_sptree t2)
  | _ => raise ERR "dest_int_sptree" "";

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

fun dest_fs tm = dest_unit_sptree tm

fun alloc_aux alg k [] n = (print"\n";[])
|   alloc_aux alg k ([clash_tree,moves,sc,force,fs]::xs) n =
  let val _ = print (strcat (Int.toString n) " ")
      val clash_tree_poly = dest_clash_tree clash_tree
      val moves_poly = dest_moves moves
      val force_poly = dest_forced force
      val fs_poly = dest_fs fs
      val sc_poly =
        if optionSyntax.is_some sc then
          SOME (dest_int_sptree (optionSyntax.dest_some sc)) else NONE
      val res = reg_alloc alg sc_poly k moves_poly clash_tree_poly force_poly fs_poly in
    case res of
      Success s => s:: alloc_aux alg k xs (n+1)
    | Failure e => raise ERR "reg_alloc" "failure"
  end
|   alloc_aux _ _ _ _ = raise General.Bind;

(*Main thing to call for external allocator
  Should be passed a term of the form (k,(clashsetlist,moves) list)
*)
fun alg_to_str Simple = "Simple" |
   alg_to_str Irc = "IRC";

fun alloc_all alg t =
  let val (k,ls) = pairSyntax.dest_pair t
      val _ = print ("Num regs: "^Int.toString (int_of_term k) ^" Alg: "^alg_to_str alg^ "\n")
    val datals = map pairSyntax.strip_pair (fst(listSyntax.dest_list ls)) in
    alloc_aux alg (int_of_term k) datals 0
  end

fun get_oracle alg t =
  let val cols = alloc_all alg t
      val alloc = listSyntax.mk_list (
      map
        (optionSyntax.mk_some  o mk_num_sptree) cols,
        ``:num num_map option``) in
      alloc
  end

(*
  get_oracle 3 ``(5n,[(Seq (Delta [1;2;3][]) (Set LN),[],[(1n,2n)]);Set LN,[(1n,1n,2n)],[]])``
*)

end
end
