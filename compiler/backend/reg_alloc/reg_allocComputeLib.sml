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

val int_list_to_string = String.concatWith "," o map Int.toString;

val kv_list_to_string = String.concatWith "," o map (fn (k,v) => Int.toString k ^" -> "^Int.toString v);

val unit_spt_to_string : unit sptree_spt -> string = int_list_to_string o sort (fn i => fn j => i <= j) o map fst o toalist;

val int_spt_to_string : int sptree_spt -> string = kv_list_to_string o sort (fn (ki,_) => fn (kj,_) => ki <= kj) o toalist;

fun apply_spt f spt =
  fromalist (map (fn i => (f i,())) (map fst (toalist spt)));

fun apply_clash_tree f ct =
  case ct of
    Delta (ws,rs) => Delta (map f ws, map f rs)
  | Set ns => Set (apply_spt f ns)
  | Seq (ct1,ct2) => Seq (apply_clash_tree f ct1, apply_clash_tree f ct2)
  | Branch (topt,ct1,ct2) => (
    let val
      topt' =
        case topt of
          NONE => NONE
        | SOME t => SOME (apply_spt f t) in
      Branch (topt',apply_clash_tree f ct1, apply_clash_tree f ct2)
    end);

fun pr_clash_tree pr indent ct =
  let val pri = (fn s => pr (indent ^ s)) in
  case ct of
    Delta (ws,rs) => (
    pri "wr: {";
    pr (int_list_to_string ws);
    pr "} {";
    pr (int_list_to_string rs);
    pr "};\n")
  | Set ns => (
    pri "st: {";
    pr (unit_spt_to_string ns);
    pr"};\n")
  | Seq (ct1,ct2) => (
    pr_clash_tree pr indent ct1;
    pr_clash_tree pr indent ct2
  )
  | Branch (topt,ct1,ct2) => (
    case topt of
      NONE => (
      pri "ifn:\n";
      pri "{\n";
      pr_clash_tree pr (indent^"  ") ct1;
      pri "}\n";
      pri "{\n";
      pr_clash_tree pr (indent^"  ") ct2;
      pri "}\n")
    | SOME t => (
      pri "ifa: {";
      pr (unit_spt_to_string t);
      pr "}\n";
      pri "{\n";
      pr_clash_tree pr (indent^"  ") ct1;
      pri "}\n";
      pri "{\n";
      pr_clash_tree pr (indent^"  ") ct2;
      pri "}\n")
  )
  end;

fun pair_str (x,y) = "(" ^ Int.toString x ^ "," ^ Int.toString y ^ ")";
fun trip_str (p,(x,y)) = "(" ^ Int.toString p ^ "," ^ Int.toString x ^ "," ^ Int.toString y ^ ")";

fun pr_force pr force =
  pr ("force: {" ^ (String.concatWith "," (map pair_str force)) ^"}\n");

fun pr_moves pr mvs =
  pr ("moves: {" ^ (String.concatWith "," (map trip_str mvs)) ^"}\n");

fun pr_k pr k =
  pr ("regs: " ^ Int.toString k ^"\n");

fun pr_fs pr fs =
  pr ("fs: {" ^ unit_spt_to_string fs ^ "}\n");

fun pr_sol pr s =
  pr ("sol: {" ^ int_spt_to_string s ^ "}\n");

fun pr_clash_graph pr ct =
let
  val (ta,(fa,n)) = mk_bij ct;
  val adj_ls = Array.array (n, ([]:int list));

  val insert_edge =
    (fn  v4 =>
      (fn  v5 =>
        let val  v3 = Array.sub ( adj_ls, v4)
            val  v2 = Array.sub ( adj_ls, v5)
            val  v1 =
          Array.update ( adj_ls, v4, (sorted_insert v5 [] v3))
        in
          Array.update ( adj_ls, v5, (sorted_insert v4 [] v2))
        end));

  fun list_insert_edge v5 v4 =
    case  v4
    of  []  =>  ()
    |   v3::v2 =>  (let val  v1 = insert_edge v5 v3
     in
      list_insert_edge v5 v2
     end);

  fun clique_insert_edge v4 =
    case  v4
    of  []  =>  ()
    |   v3::v2 =>  (let val  v1 = list_insert_edge v3 v2
     in
      clique_insert_edge v2
     end)
        fun  extend_clique v5 v4 =
    case  v5
    of  []  =>  v4
    |   v3::v2 =>  (if  (member v3 v4)
    then  (extend_clique v2 v4)
    else  (let val  v1 = list_insert_edge v3 v4
     in
      extend_clique v2 (v3::v4)
    end));

  fun mk_graph v26 v25 v24 =
    case  v25
    of  Delta(v8,v7) =>  (let val  v6 = map v26 v8
        val  v5 = map v26 v7
        val  v4 = extend_clique v6 v24
        val  v3 =
      filter (fn  v1 => ((member v1 v6) = (0 < 0))) v4
        val  v2 = extend_clique v5 v3
     in
      v2
     end)
    |   Set(v11) =>  (let val  v10 =
      map v26 (map fst (toalist v11))
        val  v9 = clique_insert_edge v10
     in
      v10
     end)
    |   Branch(v20,v19,v18) =>  (let val  v17 =
      mk_graph v26 v19 v24
        val  v16 = mk_graph v26 v18 v24
     in
      case  v20
    of  NONE =>  (let val  v12 = extend_clique v17 v16
     in
      v12
     end)
    |   SOME(v15) =>  (let val  v14 =
      map v26 (map fst (toalist v15))
        val  v13 = clique_insert_edge v14
     in
      v14
     end)
    end)
    |   Seq(v23,v22) =>  (let val  v21 = mk_graph v26 v22 v24
     in
      mk_graph v26 v23 v21
     end)
        fun  extend_graph v6 v7 =
    case  v7
    of  []  =>  ()
    |   v5::v4 =>  (case  v5
    of  (v3,v2) =>  (let val  v1 = insert_edge (v6 v3) (v6 v2)
    in
      extend_graph v6 v4
     end))
  val u = mk_graph (sp_default ta) ct []
  val f = sp_default fa in
  Array.appi (fn(i,x) =>
    (pr (Int.toString (f i)); pr ": {"; pr (int_list_to_string (sort (fn a => fn b => a <= b) (map f x))); pr"}\n")) adj_ls
end;

val dump_to_file = ref NONE : string option ref;


fun dump_clash_graph_raw path ctp =
    let
      val fd = TextIO.openOut path
      val _ = pr_clash_graph (fn s => TextIO.output(fd,s)) ctp
    in
      TextIO.closeOut fd
    end;

fun dump_clash_tree_raw path n k ctp moves force fs s =
    let
      val fd = TextIO.openOut path
      val _ = pr_k (fn s => TextIO.output(fd,s)) k
      val _ = pr_moves (fn s => TextIO.output(fd,s)) moves
      val _ = pr_force (fn s => TextIO.output(fd,s)) force
      val _ = pr_fs (fn s => TextIO.output(fd,s)) fs
      val _ = pr_sol (fn s => TextIO.output(fd,s)) s
      val _ = pr_clash_tree (fn s => TextIO.output(fd,s)) "" ctp
    in
      TextIO.closeOut fd
    end;

fun dump_clash_tree n k ctp moves force fs =
  case !dump_to_file of
    NONE => ()
  | SOME prefix =>
    (dump_clash_tree_raw (prefix ^ Int.toString n ^".txt")
      n k ctp moves force fs Ln;
     dump_clash_graph_raw (prefix ^ Int.toString n ^".graph") ctp);

fun apply_moves f moves =
  map (fn (p,(x,y)) => (p,(f x, f y))) moves;

fun apply_force f force =
  map (fn (x,y) => (f x, f y)) force;

fun dump_clash_tree_sol n k ctp moves force fs s =
  case !dump_to_file of
    NONE => ()
  | SOME prefix =>
    let
      val f = (fn i => case lookup_1 i s of NONE => ~1 | SOME v => v)
      val ctp_s = apply_clash_tree f ctp
      val moves_s = apply_moves f moves
      val force_s = apply_force f force
      val fs_s = apply_spt f fs
    in
      (dump_clash_tree_raw (prefix ^ Int.toString n ^"_allocated.txt")
        n k ctp_s moves_s force_s fs_s s;
       dump_clash_graph_raw (prefix ^ Int.toString n ^"_allocated.graph") ctp_s)
    end;

(* --- direct version --- *)

fun alloc_aux alg k [] n = (if !verbose then print"\n" else (); [])
  | alloc_aux alg k ((clash_tree,(moves,(sc,(force,fs))))::xs) n =
      let
        val () = if !verbose then print (strcat (Int.toString n) " ") else ()
        val clash_tree_poly = clash_tree
        val moves_poly = moves
        val force_poly = force
        val fs_poly = fs
        val () = dump_clash_tree n k clash_tree_poly moves_poly force_poly fs_poly
        val sc_poly = sc
        val res = reg_alloc alg sc_poly k moves_poly clash_tree_poly force_poly fs_poly
      in
        case res of
          Success s =>
          let
            val () = dump_clash_tree_sol n k clash_tree_poly moves_poly force_poly fs_poly s
          in
            s :: alloc_aux alg k xs (n + 1)
          end
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
    val _ = if !verbose then print ("Num regs: "^Int.toString k ^" Alg: "^alg_to_str alg^ "\n") else ()
  in
    alloc_aux alg k datals 0
  end

(*Int ML sptree to HOL num sptree*)
fun mk_num_sptree t =
 case t of
    Ln => mk_ln ``:num$num``
  | Ls a => mk_ls (term_of_int a)
  | Bn (Ln, t2) =>
       let
          val tm = mk_num_sptree t2
       in
          mk_bn (mk_ln ``:num$num``, tm)
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
          val ln = mk_ln ``:num$num``
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
       ``:num$num sptree$spt option$option``)
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

fun alloc_aux alg k [] n = (if !verbose then print"\n" else ();[])
|   alloc_aux alg k ([clash_tree,moves,sc,force,fs]::xs) n =
  let val () = if !verbose then print (strcat (Int.toString n) " ") else ()
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
      val _ = if !verbose then print ("Num regs: "^Int.toString (int_of_term k) ^" Alg: "^alg_to_str alg^ "\n") else ()
    val datals = map pairSyntax.strip_pair (fst(listSyntax.dest_list ls)) in
    alloc_aux alg (int_of_term k) datals 0
  end

fun get_oracle alg t =
  let val cols = alloc_all alg t
      val alloc = listSyntax.mk_list (
      map
        (optionSyntax.mk_some  o mk_num_sptree) cols,
        ``:num$num sptree$spt option$option``) in
      alloc
  end

(*
  val tr = rhs (concl (EVAL
    ``Branch (SOME (fromList [();();();()]))
      (Branch NONE
        (Seq (Delta [1;2;3][4;5;6]) (Set (fromList [();();();()])))
        (Seq (Delta [1;2;3][4;5;6]) (Set (fromList [();();();()]))))
      (Seq (Seq (Delta [][]) (Branch NONE (Set LN) (Set LN))) (Seq (Set LN) (Delta [][])))``));
  val clash_tree_poly = pr_clash_tree print ""
  pr_clash_graph ct;
*)

end
end
