(*
  Functions for constructing a CakeML program (a list of declarations) together
  with the semantic environment resulting from evaluation of the program.
*)
structure ml_progLib :> ml_progLib =
struct

open preamble ml_progTheory astSyntax packLib alist_treeLib comparisonTheory
local open mlstringSyntax in end

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

(* state *)

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

(* converting nsLookups *)

val nsLookup_tm = prim_mk_const {Thy = "namespace", Name = "nsLookup"}
val nsLookup_Short_tm = prim_mk_const {Thy = "ml_prog", Name = "nsLookup_Short"}
val nsLookup_Mod1_tm = prim_mk_const {Thy = "ml_prog", Name = "nsLookup_Mod1"}
val nsLookup_pf_tms = [nsLookup_Mod1_tm, nsLookup_Short_tm]

val empty_env_tm = prim_mk_const {Name = "empty_env", Thy = "ml_prog"}
val env_type = type_of empty_env_tm

(* Runtime A/B switch: when true, nsLookup_conv falls through to the
   legacy alist_treeLib path (orig behaviour); when false, it uses the
   new env_tree path.  The let_env_abbrev finish hook saves theorems for
   BOTH paths so this can be toggled live without rebuilding.  Initial
   value is taken from the USE_ALIST_CONV env var ("1" / "true" => alist)
   so whole-chain A/B benchmarks can be driven by a single env setting. *)
val use_alist_conv : bool ref = ref (
  case Option.map (String.map Char.toLower) (OS.Process.getEnv "USE_ALIST_CONV") of
      SOME "1" => true
    | SOME "true" => true
    | SOME "yes" => true
    | _ => false)

(* --- alist_treeLib state for the legacy nsLookup_pf_conv path --- *)
fun pfun_eq_name const = "nsLookup_" ^ fst (dest_const const) ^ "_pfun_eqs"

fun str_dest tm = mlstringSyntax.dest_mlstring tm |> explode |> map ord

local

val nsLookup_repr_set = let
    val irrefl_thm =
        MATCH_MP good_cmp_Less_irrefl_trans mlstringTheory.good_cmp_compare
  in alist_treeLib.mk_alist_reprs irrefl_thm EVAL
       str_dest (list_compare Int.compare)
  end

val pfun_empty = (Redblackmap.mkDict Term.compare : (term, unit) Redblackmap.dict)
val pfun_eqs_in_repr = ref pfun_empty

fun add thm = List.app (add_alist_repr nsLookup_repr_set) (BODY_CONJUNCTS thm)

fun get_pfun_thm c = let
    val c_details = dest_thy_const c
    val thm = DB.fetch (#Thy c_details) (pfun_eq_name c)
    val _ = find_term (same_const (hd nsLookup_pf_tms)) (concl thm)
  in (c, thm) end

fun pfun_uniq [] = []
  | pfun_uniq [x] = [x]
  | pfun_uniq (x :: y :: zs) = if same_const x y then pfun_uniq (y :: zs)
    else x :: pfun_uniq (y :: zs)

fun mk_chain [] chain set = (chain, set)
  | mk_chain ((c, t) :: cs) chain set =
      if Redblackmap.peek (set, c) = SOME () then mk_chain cs chain set
      else let
        val cs2 = t |> concl |> strip_conj |> map (find_terms is_const o rhs)
            |> List.concat
            |> filter (fn tm => type_of tm = env_type)
            |> Listsort.sort Term.compare |> pfun_uniq
            |> filter (fn c => Redblackmap.peek (set, c) = NONE)
            |> List.mapPartial (total get_pfun_thm)
      in if null cs2 then
           mk_chain cs ((c, t) :: chain) (Redblackmap.insert (set, c, ()))
         else mk_chain (cs2 @ (c, t) :: cs) chain set end

in

fun check_in_repr_set tms = let
    val consts = List.concat (map (find_terms is_const) tms)
        |> filter (fn tm => type_of tm = env_type)
        |> Listsort.sort Term.compare |> pfun_uniq
        |> List.mapPartial (total get_pfun_thm)
    val (chain, set) = mk_chain consts [] (! pfun_eqs_in_repr)
    val _ = if null chain then raise Empty else ()
    val chain_names = map (fst o dest_const o fst) chain
    val msg_names = if length chain > 3
        then List.take (chain_names, 2) @ ["..."] @ [List.last chain_names]
        else chain_names
    val msg = "Adding nsLookup representation thms for "
        ^ (if length chain > 3 then Int.toString (length chain) ^ " consts ["
           else "[") ^ concat (commafy msg_names) ^ "]\n"
  in
    print msg; List.app (add o snd) (rev chain);
    pfun_eqs_in_repr := set
  end handle Empty => ()

fun nsLookup_pf_conv tm = let
    val (f, xs) = strip_comb tm
    val _ = length xs = 2 orelse raise UNCHANGED
    val _ = exists (same_const f) (nsLookup_tm :: nsLookup_pf_tms)
        orelse raise UNCHANGED
    val _ = check_in_repr_set [hd xs]
  in reprs_conv nsLookup_repr_set tm end

end

val nsLookup_conv_arg1_xs = [
  boolSyntax.conjunction, boolSyntax.disjunction,
  boolSyntax.equality, boolSyntax.conditional, optionSyntax.option_case_tm,
  prim_mk_const {Name = "OPTION_CHOICE", Thy = "option"}]

fun nsLookup_arg1_conv conv tm = let
  val (f, xs) = strip_comb tm
  val _ = exists (same_const f) nsLookup_conv_arg1_xs orelse raise UNCHANGED
  in
    if length xs > 1 then RATOR_CONV (nsLookup_arg1_conv conv) tm
    else if length xs = 1 then RAND_CONV conv tm
    else raise UNCHANGED
  end

(* Rewrites used by nsLookup_conv: dispatch (nsLookup_eq), compound
   intermediates (OPTION_CHOICE, option_case, etc.), merge_env/empty_env
   field projections (used when the lookup target is a literal record like
   <|v := Bind [] []; c := Bind [] []|> rather than a registered env_tree),
   and the underlying ALOOKUP unfold for the empty case. *)
val nsLookup_rewrs = List.concat (map BODY_CONJUNCTS [
  nsLookup_eq, option_choice_f_apply, boolTheory.COND_CLAUSES,
  optionTheory.option_case_def, optionTheory.OPTION_CHOICE_def,
  boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES, boolTheory.REFL_CLAUSE,
  nsLookup_pf_nsBind, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend,
  nsLookup_merge_env_eqs, nsLookup_empty_eqs,
  nsLookup_Short_Bind, nsLookup_Mod1_Bind, alistTheory.ALOOKUP_def])

(* The main nsLookup_conv and its computeLib registration are defined near
   the bottom of this file (after nsLookup_tree_conv, which it dispatches to). *)

val () = computeLib.the_compset := computeLib.add_thms [nsLookup_eq] (!computeLib.the_compset)

(* --- balanced env tree (env_tree) infrastructure ---
   A drop-in replacement for alist_treeLib for sem_env lookups: every env
   constructed by the translator is of the form (proj t) for some env_tree t.
   Each node carries an ML-side shadow (env_node) which remembers the HOL
   tree term, its WF theorem (with exact key bounds), and child links. *)

val EnvLeaf_tm   = prim_mk_const {Name = "EnvLeaf",   Thy = "ml_prog"}
val EnvBranch_tm = prim_mk_const {Name = "EnvBranch", Thy = "ml_prog"}
val env_tree_ty  = mk_thy_type {Thy = "ml_prog", Tyop = "env_tree", Args = []}

(* Per-session counter for fresh tree-node constant names. Each
   mk_leaf_node / mk_branch_node / rotate / coalesce step produces a new
   HOL Definition with a name like "env_tree_<N>". The theory name is
   implicit in the constant's {Thy, Name} pair, so collisions across
   theories are impossible even if counters reset. *)
val tree_const_counter = ref 0
fun next_tree_const_name () =
    let val n = !tree_const_counter
        val _ = tree_const_counter := n + 1
    in "env_tree_" ^ Int.toString n end

(* -- Profiling buckets: accumulate wall-clock time (seconds) per phase. --
   Call ml_progLib.print_let_env_profile() to see the breakdown. *)
val prof_user_conv        = ref 0.0
val prof_cond_let_other   = ref 0.0
val prof_tree_derive      = ref 0.0
val prof_tree_merge       = ref 0.0
val prof_tree_write       = ref 0.0
val prof_tree_save        = ref 0.0
(* Time spent in derive_nsLookup_thms — the legacy alist `_pfun_eqs`
   save run alongside derive_nsLookup_tree.  Useful when A/B-benchmarking
   the two paths so the always-on dual-save cost can be subtracted. *)
val prof_pfun_eqs_save    = ref 0.0
val prof_pfun_eqs_save_n  = ref 0
val prof_define_fresh     = ref 0.0
val prof_define_fresh_n   = ref 0
val prof_let_env_n        = ref 0
val prof_let_env          = ref 0.0
val prof_nslookup_conv    = ref 0.0
val prof_nslookup_conv_n  = ref 0
(* Finer-grained within tree derive *)
val prof_apply_cps        = ref 0.0
val prof_apply_cps_n      = ref 0
val prof_mk_branch        = ref 0.0
val prof_mk_branch_n      = ref 0
val prof_mk_lt            = ref 0.0
val prof_mk_lt_n          = ref 0
val prof_mk_lt_hits       = ref 0
val prof_mk_lt_site_branch  = ref 0  (* mk_branch_node_gen *)
val prof_mk_lt_site_miss_lt = ref 0  (* tree_lookup miss, k < n_k1 *)
val prof_mk_lt_site_miss_gt = ref 0  (* tree_lookup miss, k > n_k2 *)
val prof_mk_lt_site_swap_outer = ref 0  (* merge_trees outer swap (B<A) *)
val prof_mk_lt_site_swap_via_left = ref 0  (* merge_trees_via_left *)
val prof_mk_lt_site_swap_via_right = ref 0  (* merge_trees_via_right *)
val prof_tl_outer_hit     = ref 0   (* lookup_tree_entry returned SOME *)
val prof_tl_outer_miss    = ref 0   (* lookup_tree_entry returned NONE => miss_thm *)
val prof_tl_cache_hit     = ref 0   (* tree_lookup_thm cache returned cached thm *)
val prof_miss_thm_entry   = ref 0   (* top-level miss_thm calls *)
val prof_miss_thm_recur   = ref 0   (* recursive miss_thm into both children *)
val prof_build_anon       = ref 0.0
val prof_build_anon_n     = ref 0
(* Sub-buckets for nsLookup_tree_conv internals *)
val prof_nsl_eval    = ref 0.0   (* final RAND_CONV EVAL for record field *)
val prof_nsl_hit     = ref 0.0   (* apply_cps skel_tree_lookup_hit *)
val prof_nsl_branch  = ref 0.0   (* apply_cps skel_leaf_mem_branch_{l,r} *)
val prof_nsl_eval_n   = ref 0
val prof_nsl_hit_n    = ref 0
val prof_nsl_branch_n = ref 0
val prof_nsl_tree_body = ref 0.0   (* entire nsLookup_tree_conv body (excl EVAL) *)
val prof_nsl_tree_body_n = ref 0
val prof_nsl_dispatch = ref 0.0  (* strip_comb + dest_comb + env_tree_lookup *)
val prof_nsl_spec     = ref 0.0  (* SPECL proj_thm *)
val prof_nsl_apthm    = ref 0.0  (* AP_THM equiv_thm key_arg + subst *)
val prof_nsl_treethm  = ref 0.0  (* tree_lookup_thm + final subst *)
val prof_nsl_tlcall   = ref 0.0  (* just the tree_lookup_thm call *)
val prof_nsl_subst2   = ref 0.0  (* just the final CONV_RULE subst *)
(* Sub-buckets for derive_nsLookup_tree_add_via_merge (the "write" path) *)
val prof_wr_leaf      = ref 0.0  (* mk_leaf_node *)
val prof_wr_step      = ref 0.0  (* apply_cps skel_step *)
val prof_wr_merge     = ref 0.0  (* merge_trees call *)
val prof_wr_material  = ref 0.0  (* materialize_node *)
val prof_wr_finish    = ref 0.0  (* TRANS chain + AP_TERM + def rewrite *)
(* materialize_node sub-buckets *)
val prof_mat_mkbranch = ref 0.0  (* mk_branch_node_raw call (incl define_fresh) *)
val prof_mat_thmops   = ref 0.0  (* MK_COMB + AP_TERM + TRANS + SYM *)
val prof_mat_recurse  = ref 0.0  (* two recursive materialize_node calls *)
(* Hash-cons for EnvBranch constants by (L_const_tm, R_const_tm).
   Hits: how many times we reused a prior constant (skipped new_definition).
   Misses: how many new constants we created through this cache. *)
val branch_cons_hits   = ref 0
val branch_cons_misses = ref 0
local
  fun pair_cmp ((a1, b1), (a2, b2)) =
      case Term.compare (a1, a2) of
          EQUAL => Term.compare (b1, b2)
        | c => c
in
val branch_cons_cache :
      ((term * term), term * thm * thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict pair_cmp)
end

fun time_bucket bucket f x =
    let val t0 = Time.now ()
        val y = f x
        val t1 = Time.now ()
        val _ = bucket := !bucket + Time.toReal (Time.- (t1, t0))
    in y end

fun print_let_env_profile () = (
    print ("\n=== let_env_abbrev / nsLookup profile ===\n");
    print ("  let_env_abbrev calls: " ^ Int.toString (!prof_let_env_n) ^
           " (" ^ Real.toString (!prof_let_env) ^ " s)\n");
    print ("    user conv:        " ^ Real.toString (!prof_user_conv) ^ " s\n");
    print ("    cond_let other:   " ^ Real.toString (!prof_cond_let_other) ^ " s\n");
    print ("    tree derive:      " ^ Real.toString (!prof_tree_derive) ^ " s\n");
    print ("      write:          " ^ Real.toString (!prof_tree_write) ^ " s\n");
    print ("      merge:          " ^ Real.toString (!prof_tree_merge) ^ " s\n");
    print ("      save:           " ^ Real.toString (!prof_tree_save) ^ " s\n");
    print ("    pfun_eqs save:    " ^ Real.toString (!prof_pfun_eqs_save) ^
           " s (" ^ Int.toString (!prof_pfun_eqs_save_n) ^
           " calls — dual-save for alist A/B)\n");
    print ("    define_fresh:     " ^ Real.toString (!prof_define_fresh) ^ " s (" ^
           Int.toString (!prof_define_fresh_n) ^ " calls)\n");
    print ("  nsLookup_conv:      " ^ Real.toString (!prof_nslookup_conv) ^
           " s (" ^ Int.toString (!prof_nslookup_conv_n) ^ " top-level calls)\n");
    print ("    final EVAL:       " ^ Real.toString (!prof_nsl_eval) ^ " s (" ^
           Int.toString (!prof_nsl_eval_n) ^ " calls)\n");
    print ("    tree_lookup_hit:  " ^ Real.toString (!prof_nsl_hit) ^ " s (" ^
           Int.toString (!prof_nsl_hit_n) ^ " calls)\n");
    print ("    branch subset:    " ^ Real.toString (!prof_nsl_branch) ^ " s (" ^
           Int.toString (!prof_nsl_branch_n) ^ " calls)\n");
    print ("    tree_conv body (excl EVAL): " ^
           Real.toString (!prof_nsl_tree_body) ^ " s (" ^
           Int.toString (!prof_nsl_tree_body_n) ^ " calls)\n");
    print ("      dispatch (strip/lookup): " ^
           Real.toString (!prof_nsl_dispatch) ^ " s\n");
    print ("      SPECL proj_thm:          " ^
           Real.toString (!prof_nsl_spec) ^ " s\n");
    print ("      AP_THM + subst:          " ^
           Real.toString (!prof_nsl_apthm) ^ " s\n");
    print ("      tree_lookup_thm + subst: " ^
           Real.toString (!prof_nsl_treethm) ^ " s\n");
    print ("        tree_lookup_thm call:  " ^
           Real.toString (!prof_nsl_tlcall) ^ " s\n");
    print ("        CONV_RULE subst:       " ^
           Real.toString (!prof_nsl_subst2) ^ " s\n");
    print ("    derive_via_merge breakdown:\n");
    print ("      mk_leaf_node:     " ^ Real.toString (!prof_wr_leaf) ^ " s\n");
    print ("      step apply_cps:   " ^ Real.toString (!prof_wr_step) ^ " s\n");
    print ("      merge_trees:      " ^ Real.toString (!prof_wr_merge) ^ " s\n");
    print ("      materialize_node: " ^ Real.toString (!prof_wr_material) ^ " s\n");
    print ("        mk_branch_node_raw (inc new_def): " ^
           Real.toString (!prof_mat_mkbranch) ^ " s\n");
    print ("        recurse into children:            " ^
           Real.toString (!prof_mat_recurse) ^ " s\n");
    print ("        MK_COMB/AP_TERM/TRANS/SYM:        " ^
           Real.toString (!prof_mat_thmops) ^ " s\n");
    print ("      finish/TRANS:     " ^ Real.toString (!prof_wr_finish) ^ " s\n");
    print ("  apply_cps:          " ^ Real.toString (!prof_apply_cps) ^ " s (" ^
           Int.toString (!prof_apply_cps_n) ^ " calls)\n");
    print ("  mk_branch_node_raw: " ^ Real.toString (!prof_mk_branch) ^ " s (" ^
           Int.toString (!prof_mk_branch_n) ^ " calls)\n");
    print ("  mk_lt_thm:          " ^ Real.toString (!prof_mk_lt) ^ " s (" ^
           Int.toString (!prof_mk_lt_n) ^ " calls, " ^
           Int.toString (!prof_mk_lt_hits) ^ " cache hits)\n");
    print ("    by site: branch=" ^ Int.toString (!prof_mk_lt_site_branch) ^
           ", miss_lt=" ^ Int.toString (!prof_mk_lt_site_miss_lt) ^
           ", miss_gt=" ^ Int.toString (!prof_mk_lt_site_miss_gt) ^
           ", swap_outer=" ^ Int.toString (!prof_mk_lt_site_swap_outer) ^
           ", swap_via_left=" ^ Int.toString (!prof_mk_lt_site_swap_via_left) ^
           "\n");
    print ("    tree_lookup_thm: outer_hit=" ^ Int.toString (!prof_tl_outer_hit) ^
           ", outer_miss=" ^ Int.toString (!prof_tl_outer_miss) ^
           ", cache_hit=" ^ Int.toString (!prof_tl_cache_hit) ^
           ", miss_recur=" ^ Int.toString (!prof_miss_thm_recur) ^ "\n");
    print ("  build_tree_anon:    " ^ Real.toString (!prof_build_anon) ^
           " s (" ^ Int.toString (!prof_build_anon_n) ^ " top-level calls)\n");
    print ("  total tree consts:  " ^ Int.toString (!tree_const_counter) ^
           " (HOL Definitions created)\n");
    print ("  branch cons cache:  " ^ Int.toString (!branch_cons_hits) ^
           " hits, " ^ Int.toString (!branch_cons_misses) ^ " misses\n");
    print ("    → without hash-cons: " ^
           Int.toString (!tree_const_counter + !branch_cons_hits) ^
           " Definitions would be created\n");
    print ("==========================================\n"))

(* Define a fresh tree-node constant whose rhs is tree_tm.
   Returns (const_term, def_thm) where def_thm : |- <const> = <tree_tm>. *)
fun define_fresh_tree tree_tm = let
  val t0 = Time.now ()
  val nm = next_tree_const_name ()
  val lhs = mk_var (nm, env_tree_ty)
  val def = Definition.new_definition (nm ^ "_def", mk_eq (lhs, tree_tm))
  val const_tm = def |> concl |> dest_eq |> fst
  val t1 = Time.now ()
  val _ = prof_define_fresh := !prof_define_fresh + Time.toReal (Time.- (t1, t0))
  val _ = prof_define_fresh_n := !prof_define_fresh_n + 1
  in (const_tm, def) end

(* ThmSet exporters: cross-theory persistence for tree equivalences + WF.
   Each derive_nsLookup_tree exports under a naming convention so that
   downstream theories can lazily repopulate env_tree_map on demand. *)

val { export = export_tree_equiv, getDB = get_tree_equivs_DB, ... } =
  ThmSetData.export_simple_dictionary { settype = "nsLookup_all_tree", initial = [] }

val { export = export_tree_wf, getDB = get_tree_wfs_DB, ... } =
  ThmSetData.export_simple_dictionary { settype = "env_wf_tree", initial = [] }

(* Naming convention. For env constant named "foo" we save:
     foo_tree_equiv : nsLookup_all foo = tree_lookup <tree>
     foo_tree_wf    : env_wf <tree> k1 k2
   and export both to the ThmSets above. *)
fun tree_equiv_name env_name = env_name ^ "_tree_equiv"
fun tree_wf_name    env_name = env_name ^ "_tree_wf"

(* Each env_node now owns a freshly-defined HOL constant for its tree.
   - tree_tm : the fresh constant (e.g. env_tree_42).
   - def_thm : |- <tree_tm> = EnvLeaf k e       (for leaves)
              |- <tree_tm> = EnvBranch <l.tree_tm> <r.tree_tm>  (for branches)
   Branch children are env_nodes, so their tree_tms are themselves constants,
   giving the tree a chain of Definitions unfolding one level at a time. *)

datatype env_node =
  ELeaf of {
  key_tm: term, key_str: string, entry_tm: term, tree_tm: term, def_thm: thm, wf_thm: thm }
| EBranch of {
  left: env_node, right: env_node, k1_tm: term, k2_tm: term,
  k1_str: string, k2_str: string, depth: int, tree_tm: term, def_thm: thm, wf_thm: thm }

fun tree_tm_of (ELeaf r)   = #tree_tm r
  | tree_tm_of (EBranch r) = #tree_tm r

fun def_thm_of (ELeaf r)   = #def_thm r
  | def_thm_of (EBranch r) = #def_thm r

fun wf_thm_of (ELeaf r)   = #wf_thm r
  | wf_thm_of (EBranch r) = #wf_thm r

fun bounds_of (ELeaf r)   = (#key_tm r, #key_tm r)
  | bounds_of (EBranch r) = (#k1_tm r, #k2_tm r)

fun key_strs_of (ELeaf r)   = (#key_str r, #key_str r)
  | key_strs_of (EBranch r) = (#k1_str r, #k2_str r)

fun depth_of (ELeaf _)   = 1
  | depth_of (EBranch r) = #depth r

(* Collect all Definitions in a tree (leaves + branches).  Used to
   unfold tree-node constants back to their EnvLeaf/EnvBranch structure
   inside proof tactics that need to reduce tree_lookup concretely. *)
fun collect_def_thms (ELeaf {def_thm, ...}) = [def_thm]
  | collect_def_thms (EBranch {left, right, def_thm, ...}) =
    def_thm :: collect_def_thms left @ collect_def_thms right

val mlstring_lt_tm = prim_mk_const {Name = "mlstring_lt", Thy = "mlstring"}

local
  val lt_cache = ref (Redblackmap.mkDict (pair_compare (Term.compare, Term.compare)):
    ((term * term), thm) Redblackmap.dict)
in
  (* mk_lt_thm_via: same cache as mk_lt_thm, but on miss delegate to the
    provided thunk instead of EVAL.  Lets callers with a cheap alternative
    (e.g. apply_cps of env_wf_branch_split_lt_cps on a parent WF) supply a
    miss-path that's faster than `EQT_ELIM (EVAL ...)`. *)
  fun mk_lt_thm_via mkfallback a b = let
    val t0 = Time.now ()
    val r = case Redblackmap.peek (!lt_cache, (a, b)) of
      SOME th => (prof_mk_lt_hits := !prof_mk_lt_hits + 1; th)
    | NONE => case mkfallback () of th =>
      (lt_cache := Redblackmap.insert (!lt_cache, (a, b), th); th)
    val t1 = Time.now ()
    val _ = prof_mk_lt := !prof_mk_lt + Time.toReal (Time.- (t1, t0))
    val _ = prof_mk_lt_n := !prof_mk_lt_n + 1
    in r end
end

fun mk_lt_thm a b =
  mk_lt_thm_via (fn () => EQT_ELIM (EVAL (list_mk_icomb (mlstring_lt_tm, [a, b])))) a b

(* Convenience: apply a prepped skeleton by instantiating variables and
   discharging hypotheses with provided theorems (matched by aconv on
   conclusion).  Order of provided theorems is immaterial. *)
fun apply_cps skel subst provided = let
  val t0 = Time.now ()
  val r = List.foldl (fn (p, th) => PROVE_HYP p th) (INST subst skel) provided
  val t1 = Time.now ()
  val _ = prof_apply_cps := !prof_apply_cps + Time.toReal (Time.- (t1, t0))
  val _ = prof_apply_cps_n := !prof_apply_cps_n + 1
  in r end

(* --- CPS lemma preparation ---
   SPEC_ALL the lemma, split conjunctions in antecedent into iterated
   implications (via GSYM AND_IMP_INTRO), then UNDISCH_ALL so each premise
   becomes a hypothesis.  Result:
     [p1, p2, ..., pN] ⊢ conclusion
   with free variables in place (no universal quantifiers).  Callers build
   a substitution and INST it, then PROVE_HYP each provided premise theorem
   in against the hypothesis set. *)
val prep_cps = apply_cps o UNDISCH_ALL o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO] o SPEC_ALL

(* Env-tree and mlstring typed var builders. *)
val mlstring_ty = mk_thy_type {Thy = "mlstring", Tyop = "mlstring", Args = []}
fun mk_etv n = mk_var (n, env_tree_ty)
fun mk_msv n = mk_var (n, mlstring_ty)

(* Prepped skeletons for the hot CPS lemmas. *)
val skel_env_wf_branch_intro =
    prep_cps ml_progTheory.env_wf_branch_intro_cps
val skel_env_wf_branch_split_lt =
    prep_cps ml_progTheory.env_wf_branch_split_lt_cps
val skel_env_wf_leaf = prep_cps ml_progTheory.env_wf_leaf_cps
val skel_rotate_right = prep_cps ml_progTheory.tree_lookup_rotate_right_cps
val skel_rotate_left  = prep_cps ml_progTheory.tree_lookup_rotate_left_cps
val skel_branch_cong  = prep_cps ml_progTheory.tree_lookup_branch_cong_cps
val skel_prepend      = prep_cps ml_progTheory.tree_lookup_prepend_cps
val skel_append       = prep_cps ml_progTheory.tree_lookup_append_cps
val skel_branch_left_update =
    prep_cps ml_progTheory.tree_lookup_branch_left_update_cps
val skel_branch_right_update =
    prep_cps ml_progTheory.tree_lookup_branch_right_update_cps
val skel_replace_leaf = prep_cps ml_progTheory.tree_lookup_replace_leaf_cps
val skel_coalesce_leaves = prep_cps ml_progTheory.tree_lookup_coalesce_leaves_cps
val skel_commute      = prep_cps ml_progTheory.tree_lookup_commute_cps
val skel_swap         = prep_cps ml_progTheory.tree_lookup_swap_cps
val skel_leaf_mem_leaf     = prep_cps ml_progTheory.env_leaf_mem_leaf_cps
val skel_leaf_mem_branch_l = prep_cps ml_progTheory.env_leaf_mem_branch_l_cps
val skel_leaf_mem_branch_r = prep_cps ml_progTheory.env_leaf_mem_branch_r_cps
val skel_tree_lookup_hit   = prep_cps ml_progTheory.tree_lookup_hit
val skel_tree_lookup_miss  = prep_cps ml_progTheory.tree_lookup_miss
val skel_tree_lookup_branch_empty =
    prep_cps ml_progTheory.tree_lookup_branch_empty_cps
val skel_tree_miss_gap        = prep_cps ml_progTheory.tree_miss_gap_cps
val skel_tree_miss_branch_l   = prep_cps ml_progTheory.tree_miss_branch_l_cps
val skel_tree_miss_branch_r   = prep_cps ml_progTheory.tree_miss_branch_r_cps
val skel_write_tree     = prep_cps ml_progTheory.nsLookup_all_write_tree_cps
val skel_write_cons_tree= prep_cps ml_progTheory.nsLookup_all_write_cons_tree_cps
val skel_write_mod_tree = prep_cps ml_progTheory.nsLookup_all_write_mod_tree_cps

(* Var caches for the common names in these lemmas. *)
val vtT   = mk_etv "tT"
val vtT'  = mk_etv "tT'"
val vTnew = mk_etv "Tnew"
val vtL   = mk_etv "tL"
val vtR   = mk_etv "tR"
val vtA   = mk_etv "tA"
val vtB   = mk_etv "tB"
val vtC   = mk_etv "tC"
val v_l   = mk_etv "l"
val v_r   = mk_etv "r"
val v_l'  = mk_etv "l'"
val v_r'  = mk_etv "r'"
val v_t   = mk_etv "t"
val vtL1  = mk_etv "tL1"
val vtL2  = mk_etv "tL2"
val vtLinner  = mk_etv "tLinner"
val vtLinner' = mk_etv "tLinner'"

val vk    = mk_msv "k"
val vk1   = mk_msv "k1"
val vk2   = mk_msv "k2"
val vkl   = mk_msv "kl"
val vkr   = mk_msv "kr"
val vn    = mk_msv "n"
val vkB1  = mk_msv "kB1"
val vkB2  = mk_msv "kB2"
val vkC1  = mk_msv "kC1"
val vkC2  = mk_msv "kC2"
val vklf  = mk_msv "klf"
val vkL1  = mk_msv "kL1"
val vkL2  = mk_msv "kL2"
val vkL   = mk_msv "kL"
val vkR   = mk_msv "kR"
val vkX1  = mk_msv "kX1"
val vkX2  = mk_msv "kX2"
val vkY1  = mk_msv "kY1"
val vkY2  = mk_msv "kY2"
val vX    = mk_etv "X"
val vY    = mk_etv "Y"

(* Entry-typed variables used by prepend/append/update/replace CPS lemmas. *)
val env_entry_ty = mk_thy_type {Thy = "ml_prog", Tyop = "env_entry", Args = []}
fun mk_enev n = mk_var (n, env_entry_ty)
val v_entry     = mk_enev "entry"
val v_old_entry = mk_enev "old_entry"
val v_new_entry = mk_enev "new_entry"
val v_e         = mk_enev "e"
val v_e1        = mk_enev "e1"
val v_e2        = mk_enev "e2"
val vtTold      = mk_etv "tTold"
val vtTnew      = mk_etv "tTnew"

val v_env = mk_var ("env", env_type)

(* Naming convention: whenever we create a fresh env_tree_<N> (or
   init_env_<N>) constant, we also save_thm its env_wf proof under
   <name>_wf in the same theory.  rebuild_node then just DB.fetch'es
   the saved wf instead of re-deriving via env_wf_*_cps. *)
fun save_tree_wf tree_tm wf_thm =
  if is_const tree_tm then let
    val {Name, ...} = dest_thy_const tree_tm
    in ignore (allowing_rebind save_thm (Name ^ "_wf", wf_thm)) end
  else ()

fun mk_leaf_node key_tm entry_tm = let
  val key_str = mlstringSyntax.dest_mlstring key_tm
  val raw_tm  = mk_comb (mk_comb (EnvLeaf_tm, key_tm), entry_tm)
  val (const_tm, def_thm) = define_fresh_tree raw_tm
  val wf_thm = skel_env_wf_leaf
    [vtT |-> const_tm, vk |-> key_tm, v_e |-> entry_tm]
    [def_thm]
  val _ = save_tree_wf const_tm wf_thm
  in ELeaf {
    key_tm = key_tm, key_str = key_str, entry_tm = entry_tm,
    tree_tm = const_tm, def_thm = def_thm, wf_thm = wf_thm }
  end

(* Build an EBranch env_node.  When `make_const` is true, allocates a fresh
   env_tree_<N> constant via define_fresh_tree (heavy: hits HOL kernel +
   theory hooks).  When false, uses the compound `EnvBranch L.tt R.tt`
   term with REFL as def_thm (cheap: no kernel call).
   Compound nodes are intended for transient subnodes during merge — they
   should be MATERIALIZED via `materialize_node` before crossing any
   storage boundary (env_tree_map registration, theorem save). *)
(* Hash-cons cache declared at file top so print_let_env_profile (declared
   earlier) can reference the counters; see below for the actual dict. *)

(* mk_branch_node_gen_with: like mk_branch_node_gen but the caller supplies
   a thunk that produces the `mlstring_lt kl kr` theorem.  The default in
   `mk_branch_node_gen` is `fn () => mk_lt_thm kl_tm kr_tm`.  Callers that
   hold a parent WF already implying the needed lt can pass a thunk that
   extracts it — avoiding both the Redblackmap lookup in mk_lt_thm's cache
   and (on real misses) the EVAL. *)
fun mk_branch_node_gen_with make_const lt_thunk left right = let
  val t0 = Time.now ()
  val (k1_tm, kl_tm)    = bounds_of left
  val (kr_tm, k2_tm)    = bounds_of right
  val (k1_str, _)       = key_strs_of left
  val (_, k2_str)       = key_strs_of right
  val left_tm = tree_tm_of left
  val right_tm = tree_tm_of right
  val compound_tm = mk_comb (mk_comb (EnvBranch_tm, left_tm), right_tm)
  (* Try the hash-cons cache only when we'd materialize a constant
      AND both children are constants (the cache key is constant-only). *)
  val cached =
    if make_const andalso is_const left_tm andalso is_const right_tm
    then Redblackmap.peek (!branch_cons_cache, (left_tm, right_tm))
    else NONE
  val (tree_tm, def_thm, wf_thm) =
    case cached of
      SOME (const_tm, def_thm, wf_thm) => (
        branch_cons_hits := !branch_cons_hits + 1;
        (const_tm, def_thm, wf_thm))
    | NONE => let
      val _ = prof_mk_lt_site_branch := !prof_mk_lt_site_branch + 1
      val lt_thm = lt_thunk ()
      val (tree_tm, def_thm) =
        if make_const then define_fresh_tree compound_tm
        else (compound_tm, REFL compound_tm)
      val wf_thm = skel_env_wf_branch_intro
        [vtT |-> tree_tm, v_l |-> left_tm, v_r |-> right_tm,
          vk1 |-> k1_tm, vkl |-> kl_tm, vkr |-> kr_tm, vk2 |-> k2_tm]
        [def_thm, wf_thm_of left, wf_thm_of right, lt_thm]
      val _ = if make_const then save_tree_wf tree_tm wf_thm else ()
      val _ =
        if make_const andalso is_const left_tm andalso is_const right_tm
        then (
          branch_cons_misses := !branch_cons_misses + 1;
          branch_cons_cache := Redblackmap.insert (!branch_cons_cache,
            (left_tm, right_tm), (tree_tm, def_thm, wf_thm)))
        else ()
      in (tree_tm, def_thm, wf_thm) end
  val result = EBranch {
    left = left, right = right, k1_tm = k1_tm, k2_tm = k2_tm,
    k1_str = k1_str, k2_str = k2_str, tree_tm = tree_tm, def_thm = def_thm,
    depth = 1 + Int.max (depth_of left, depth_of right), wf_thm = wf_thm }
  val t1 = Time.now ()
  val _ = prof_mk_branch := !prof_mk_branch + Time.toReal (Time.- (t1, t0))
  val _ = prof_mk_branch_n := !prof_mk_branch_n + 1
  in result end

fun mk_branch_node_gen make_const left right = let
  fun thunk () = mk_lt_thm (#2 (bounds_of left)) (#1 (bounds_of right))
  in mk_branch_node_gen_with make_const thunk left right end

fun mk_branch_node_raw      left right = mk_branch_node_gen true  left right
fun mk_branch_node_compound left right = mk_branch_node_gen false left right
fun mk_branch_node_raw_with      lt_thunk left right =
    mk_branch_node_gen_with true  lt_thunk left right
fun mk_branch_node_compound_with lt_thunk left right =
    mk_branch_node_gen_with false lt_thunk left right

(* Build an lt thunk that derives `mlstring_lt kl kr` from an ancestor
   branch WF, via env_wf_branch_split_lt_cps.  `parent` must be an
   EBranch env_node whose immediate children (in the env_node sense) are
   `l` and `r` — that is, parent_wf witnesses env_wf parent_tm k1 k2 and
   parent_def witnesses parent_tm = EnvBranch l.tree_tm r.tree_tm.  The
   thunk routes through mk_lt_thm_via so cache hits remain cheap. *)
fun lt_from_parent_wf { parent_tm, parent_def, parent_wf, l, r } () = let
  val l_tm = tree_tm_of l
  val r_tm = tree_tm_of r
  val (k1_tm, kl_tm) = bounds_of l
  val (kr_tm, k2_tm) = bounds_of r
  fun fallback () = skel_env_wf_branch_split_lt
    [vtT |-> parent_tm, v_l |-> l_tm, v_r |-> r_tm,
      vk1 |-> k1_tm, vk2 |-> k2_tm, vkl |-> kl_tm, vkr |-> kr_tm]
    [parent_def, parent_wf, wf_thm_of l, wf_thm_of r]
  in mk_lt_thm_via fallback kl_tm kr_tm end

(* Materialize: walk an env_node and replace every compound (REFL-defined)
   EBranch with one backed by a fresh definition.  Stops descending into a
   subnode whose tree_tm is already a constant (invariant: definition-backed
   nodes have definition-backed children).  Returns
     (T', thm : T.tt = T'.tt)
   — a structural (term-level) equality, since materialization is purely
   definition unfolding.  Callers lift to tree_lookup via AP_TERM. *)
fun materialize_node (node as ELeaf {tree_tm, ...}) = (node, REFL tree_tm)
  | materialize_node (node as EBranch {left, right, tree_tm,
      def_thm = node_def, wf_thm = node_wf, ...}) =
    if is_const tree_tm then (node, REFL tree_tm) else let
      val t_r0 = Time.now ()
      val (L', thm_L) = materialize_node left
      val (R', thm_R) = materialize_node right
      val t_r1 = Time.now ()
      val _ = prof_mat_recurse := !prof_mat_recurse + Time.toReal (Time.- (t_r1, t_r0))
      val mk_comb_thm = MK_COMB (AP_TERM EnvBranch_tm thm_L, thm_R)
      val t_r2 = Time.now ()
      (* Bounds of L'/R' are the same mlstring terms as left/right
      (materialization preserves leaf keys), so the lt we need
      (mlstring_lt L'.max R'.min) is exactly the one witnessed
      by node_wf on EnvBranch left right. *)
      val lt_thunk = lt_from_parent_wf
        {parent_tm = tree_tm, parent_def = node_def, parent_wf = node_wf, l = left, r = right}
      val new_node = mk_branch_node_raw_with lt_thunk L' R'
      val t_r3 = Time.now ()
      val _ = prof_mat_mkbranch := !prof_mat_mkbranch + Time.toReal (Time.- (t_r3, t_r2))
      val combined = TRANS mk_comb_thm (SYM (def_thm_of new_node))
      val t_r4 = Time.now ()
      val _ = prof_mat_thmops :=
        !prof_mat_thmops + Time.toReal (Time.- (t_r2, t_r1)) + Time.toReal (Time.- (t_r4, t_r3))
      in (new_node, combined) end

(* --- AVL rotation helpers ---
   Each returns (rotated_node, tl_eq_thm) where
     tl_eq_thm : |- tree_lookup <old.tree_tm> = tree_lookup <new_node.tree_tm>
   Uses the CPS-form primitives, so every node referenced in the theorem
   is a HOL constant — the four defining equations (for old's L/T and new's
   R/T') are threaded as premises of tree_lookup_rotate_{right,left}_cps. *)

(* rotate_right_cps vars: tL, tT, tR, tT', tA, tB, tC.
   Hyps: tL=EnvBranch tA tB, tT=EnvBranch tL tC, tR=EnvBranch tB tC, tT'=EnvBranch tA tR. *)
fun rotate_right_node node =
  case node of
    EBranch { left as EBranch { left = A, right = B, ... }, right = C,
      def_thm = T_def, tree_tm = T_tm, wf_thm = T_wf, ... } => let
    val L_tm = tree_tm_of left
    val A_tm = tree_tm_of A
    val C_tm = tree_tm_of C
    (* lt (B.max) (C.min): from T_wf on T = EnvBranch L C. *)
    val lt_new_right = lt_from_parent_wf
      {parent_tm = T_tm, parent_def = T_def, parent_wf = T_wf, l = left, r = C}
    val new_right = mk_branch_node_gen_with false lt_new_right B C
    (* lt (A.max) (B.min): from L_wf on L = EnvBranch A B. *)
    val lt_new_node = lt_from_parent_wf
      {parent_tm = L_tm, parent_def = def_thm_of left, parent_wf = wf_thm_of left, l = A, r = B}
    val new_node = mk_branch_node_gen_with false lt_new_node A new_right
    val tl_eq = skel_rotate_right
      [vtA |-> A_tm, vtB |-> tree_tm_of B, vtC |-> C_tm, vtL |-> L_tm,
        vtR |-> tree_tm_of new_right, vtT |-> T_tm, vtT' |-> tree_tm_of new_node]
      [def_thm_of left, T_def, def_thm_of new_right, def_thm_of new_node]
    in (new_node, tl_eq) end
  | _ => failwith "rotate_right_node: node is not left-heavy ((A,B),C)"

(* rotate_left_cps vars: tR, tT, tL, tT', tA, tB, tC.
   Hyps: tR=EnvBranch tB tC, tT=EnvBranch tA tR, tL=EnvBranch tA tB, tT'=EnvBranch tL tC. *)
fun rotate_left_node node =
  case node of
    EBranch { left = A, right as EBranch { left = B, right = C, ... },
      def_thm = T_def, tree_tm = T_tm, wf_thm = T_wf, ... } => let
    val A_tm = tree_tm_of A
    val C_tm = tree_tm_of C
    val R_tm = tree_tm_of right
    (* lt (A.max) (B.min): from T_wf on T = EnvBranch A R. *)
    val lt_new_left = lt_from_parent_wf
      {parent_tm = T_tm, parent_def = T_def, parent_wf = T_wf, l = A, r = right}
    val new_left = mk_branch_node_gen_with false lt_new_left A B
    (* lt (B.max) (C.min): from R_wf on R = EnvBranch B C. *)
    val lt_new_node = lt_from_parent_wf
      {parent_tm = R_tm, parent_def = def_thm_of right, parent_wf = wf_thm_of right, l = B, r = C}
    val new_node = mk_branch_node_gen_with false lt_new_node new_left C
    val tl_eq = skel_rotate_left
      [vtA |-> A_tm, vtB |-> tree_tm_of B, vtC |-> C_tm, vtL |-> tree_tm_of new_left,
        vtR |-> R_tm, vtT |-> T_tm, vtT' |-> tree_tm_of new_node]
      [def_thm_of right, T_def, def_thm_of new_left, def_thm_of new_node]
    in (new_node, tl_eq) end
  | _ => failwith "rotate_left_node: node is not right-heavy (A,(B,C))"

(* REFL packaged as a tree_lookup equality for the "no rotation" case. *)
fun tl_refl tm = REFL (mk_icomb (prim_mk_const {Name = "tree_lookup", Thy = "ml_prog"}, tm))

(* Lift an inner rewrite  tree_lookup inner = tree_lookup inner'
   through a left-subtree position to the outer branch. *)
fun lift_left_eq left_eq right_tm =
  MATCH_MP ml_progTheory.tree_lookup_branch_cong (CONJ left_eq (tl_refl right_tm))

fun lift_right_eq left_tm right_eq =
  MATCH_MP ml_progTheory.tree_lookup_branch_cong (CONJ (tl_refl left_tm) right_eq)

(* Given a raw EBranch env_node (just-constructed via mk_branch_node_raw),
   check balance factor and rotate if off by more than 1. Returns
   (balanced_node, tl_eq_thm) where
     tl_eq_thm : |- tree_lookup <raw.tree_tm> = tree_lookup <balanced.tree_tm>
   Callers thread this equation into the insertion upd via ONCE_REWRITE_RULE. *)
fun rebalance_node node =
  case node of
    EBranch { left, right, def_thm = node_def, wf_thm = node_wf, ... } => let
    val dl = depth_of left
    val dr = depth_of right
    (* Rotation preserves bounds (same leaf set), so the lt we
        need for `pre = EnvBranch left' right` (or `left right'`)
        is the very one witnessed by node_wf on EnvBranch left
        right.  Build the thunk once from node's WF. *)
    val left_tm = tree_tm_of left
    val right_tm = tree_tm_of right
    val node_tm = tree_tm_of node
    val lt_pre = lt_from_parent_wf
      {parent_tm = node_tm, parent_def = node_def, parent_wf = node_wf, l = left, r = right}
    in
      if dl > dr + 1 then
        case left of
          EBranch { left = A, right = B, ... } =>
          if depth_of A >= depth_of B then rotate_right_node node else let
            (* L-R double: rotate left subtree, then right-rotate
                the reconstructed outer branch. Use branch_cong_cps
                to bridge node's constant to pre's fresh constant. *)
            val (left', inner_eq) = rotate_left_node left
            val pre = mk_branch_node_gen_with false lt_pre left' right
            val right_refl = tl_refl right_tm
            (* branch_cong_cps vars: tT, tT', l, r, l', r'.
                Hyps: tT=EnvBranch l r, tT'=EnvBranch l' r',
                      tree_lookup l = tree_lookup l',
                      tree_lookup r = tree_lookup r'. *)
            val lifted = skel_branch_cong
              [vtT |-> node_tm, vtT' |-> tree_tm_of pre, v_l |-> left_tm,
                v_l' |-> tree_tm_of left', v_r |-> right_tm, v_r' |-> right_tm]
              [node_def, def_thm_of pre, inner_eq, right_refl]
            val (rot, outer_eq) = rotate_right_node pre
            in (rot, TRANS lifted outer_eq) end
        | _ => (node, tl_refl node_tm)
      else if dr > dl + 1 then
        case right of
          EBranch { left = B, right = C, ... } =>
          if depth_of C >= depth_of B then rotate_left_node node else let
            val (right', inner_eq) = rotate_right_node right
            val pre = mk_branch_node_gen_with false lt_pre left right'
            val left_refl = tl_refl left_tm
            val lifted = skel_branch_cong
              [vtT |-> node_tm, vtT' |-> tree_tm_of pre, v_l |-> left_tm,
                v_l' |-> left_tm, v_r |-> right_tm, v_r' |-> tree_tm_of right']
              [node_def, def_thm_of pre, left_refl, inner_eq]
            val (rot, outer_eq) = rotate_left_node pre
            in (rot, TRANS lifted outer_eq) end
        | _ => (node, tl_refl node_tm)
      else (node, tl_refl node_tm)
    end
  | _ => (node, tl_refl (tree_tm_of node))

(* mk_branch_node: AVL-balanced branch builder. Returns (node, tl_eq_thm)
   where tl_eq_thm proves that the naïve mk_branch_node_raw left right has
   the same tree_lookup as the returned (possibly rotated) node. *)
fun mk_branch_node_balanced left right =
    rebalance_node (mk_branch_node_raw left right)

(* Default mk_branch_node is the raw builder; insert_leaf_into explicitly
   rebalances at each recursion level via rebalance_node so the AVL invariant
   is maintained while the CPS upd theorems reference the raw node's def. *)
val mk_branch_node = mk_branch_node_raw

(* Binary-search for key k in the tree. If found, return the leaf entry term
   and a theorem |- env_leaf_mem k entry <root.tree_tm>.  The membership
   theorem is in terms of the root's tree-constant (via the CPS forms of
   env_leaf_mem_{leaf, branch_l, branch_r}).
   Memoised on (tree_tm, k): repeated lookups of the same key against the
   same node avoid re-traversal and re-MATCH_MP. Sub-trees also benefit —
   each recursive call memoises independently. *)
val env_leaf_mem_cache = ref (
  Redblackmap.mkDict (pair_compare (Term.compare, String.compare)):
  (term * string, (term * thm) option) Redblackmap.dict)

fun build_leaf_mem node k =
  case (tree_tm_of node, k) of cache_key =>
  case Redblackmap.peek (!env_leaf_mem_cache, cache_key) of
    SOME cached => cached
  | NONE => let
    val result = case node of
      ELeaf {key_str, key_tm, entry_tm, def_thm, tree_tm, ...} =>
      if key_str = k then let
        val mem_thm = skel_leaf_mem_leaf
          [vtT |-> tree_tm, vk |-> key_tm, v_e |-> entry_tm]
          [def_thm]
        in SOME (entry_tm, mem_thm) end
      else NONE
    | EBranch {left, right, def_thm, tree_tm, ...} =>
      case key_strs_of left of (_, kl_str) =>
      if k <= kl_str then
        case build_leaf_mem left k of
          NONE => NONE
        | SOME (entry, sub_thm) => let
          val key_tm = mlstringSyntax.mk_mlstring k
          val t0 = Time.now ()
          val mem_thm = skel_leaf_mem_branch_l
            [vtT |-> tree_tm, v_l |-> tree_tm_of left, v_r |-> tree_tm_of right,
              vk |-> key_tm, v_e |-> entry]
            [def_thm, sub_thm]
          val t1 = Time.now ()
          val _ = prof_nsl_branch := !prof_nsl_branch + Time.toReal (Time.- (t1, t0))
          val _ = prof_nsl_branch_n := !prof_nsl_branch_n + 1
          in SOME (entry, mem_thm) end
      else
        case build_leaf_mem right k of
          NONE => NONE
        | SOME (entry, sub_thm) => let
          val key_tm = mlstringSyntax.mk_mlstring k
          val t0 = Time.now ()
          val mem_thm = skel_leaf_mem_branch_r
            [vtT |-> tree_tm, v_l |-> tree_tm_of left, v_r |-> tree_tm_of right,
              vk |-> key_tm, v_e |-> entry]
            [def_thm, sub_thm]
          val t1 = Time.now ()
          val _ = prof_nsl_branch := !prof_nsl_branch + Time.toReal (Time.- (t1, t0))
          val _ = prof_nsl_branch_n := !prof_nsl_branch_n + 1
          in SOME (entry, mem_thm) end
    val _ = env_leaf_mem_cache :=
      Redblackmap.insert (!env_leaf_mem_cache, cache_key, result)
    in result end

(* Unified lookup: given an env_node and key string, return
     SOME (|- tree_lookup root.tree_tm (strlit k) = <concrete entry>)
   or NONE when the key is absent. *)
fun lookup_tree_entry root k =
  case build_leaf_mem root k of
    NONE => NONE
  | SOME (entry, mem_thm) => let
    val wf_thm = wf_thm_of root
    val (k1_tm, k2_tm) = bounds_of root
    val key_tm = mlstringSyntax.mk_mlstring k
    val t0 = Time.now ()
    val thm = skel_tree_lookup_hit
      [v_t |-> tree_tm_of root, vk1 |-> k1_tm, vk2 |-> k2_tm,
        vk |-> key_tm, v_e |-> entry]
      [wf_thm, mem_thm]
    val t1 = Time.now ()
    val _ = prof_nsl_hit := !prof_nsl_hit + Time.toReal (Time.- (t1, t0))
    val _ = prof_nsl_hit_n := !prof_nsl_hit_n + 1
    in SOME thm end

(* Cache for tree_lookup_thm.  Key: (root.tree_tm, k_str). *)
local
  val tree_lookup_thm_cache = ref (
    Redblackmap.mkDict (pair_compare (Term.compare, String.compare)):
    ((term * string), thm) Redblackmap.dict)
in
  (* Produce |- tree_lookup tree_const (strlit k) = <concrete entry or empty_entry>.
    Uses the ML tree for binary search. On hit, uses tree_lookup_hit. On miss,
    either tree_lookup_miss (if k is out of tree bounds) or EVAL on the concrete
    tree structure (if k is within bounds but in a gap between leaves).
    Memoised on (tree_tm, k). *)
  fun tree_lookup_thm root k =
    case (tree_tm_of root, k) of cache_key =>
    case Redblackmap.peek (!tree_lookup_thm_cache, cache_key) of
      SOME thm => (prof_tl_cache_hit := !prof_tl_cache_hit + 1; thm)
    | NONE => let
      val thm = case lookup_tree_entry root k of
        SOME thm => (prof_tl_outer_hit := !prof_tl_outer_hit + 1; thm)
      | NONE => let
        val _ = prof_tl_outer_miss := !prof_tl_outer_miss + 1
        val key_tm = mlstringSyntax.mk_mlstring k
        val (root_k1, root_k2) = bounds_of root
        val (root_k1_str, root_k2_str) = key_strs_of root
        val root_wf = wf_thm_of root
        val root_tm = tree_tm_of root
        in
          if k < root_k1_str then let
            val _ = prof_mk_lt_site_miss_lt := !prof_mk_lt_site_miss_lt + 1
            val lt = mk_lt_thm key_tm root_k1
            val other = list_mk_icomb (mlstring_lt_tm, [root_k2, key_tm])
            val disj = DISJ1 lt other
            in skel_tree_lookup_miss
              [v_t |-> root_tm, vk1 |-> root_k1, vk2 |-> root_k2, vk |-> key_tm]
              [root_wf, disj] end
          else if k > root_k2_str then let
            val _ = prof_mk_lt_site_miss_gt := !prof_mk_lt_site_miss_gt + 1
            val lt = mk_lt_thm root_k2 key_tm
            val other = list_mk_icomb (mlstring_lt_tm, [key_tm, root_k1])
            val disj = DISJ2 other lt
            in skel_tree_lookup_miss
              [v_t |-> root_tm, vk1 |-> root_k1, vk2 |-> root_k2, vk |-> key_tm]
              [root_wf, disj] end
          else let
            (* In-range miss: descend to the gap between two adjacent
               leaves, apply tree_miss_gap (2 lt proofs), then chain up
               with tree_miss_branch_l/_r (0 lt proofs per level).
               Returns a tree_miss thm; extract tree_lookup via
               tree_miss_imp_lookup. *)
            fun tree_miss_thm n = let
              val (n_k1, n_k2) = bounds_of n
              val n_wf = wf_thm_of n
              val n_tm = tree_tm_of n
              in case n of
                ELeaf _ =>
                  raise Fail "tree_miss_thm: in-range leaf miss unexpected"
              | EBranch {left, right, def_thm, ...} => let
                val (_, l_k2) = bounds_of left
                val (_, l_k2_str) = key_strs_of left
                val (r_k1, _) = bounds_of right
                val (r_k1_str, _) = key_strs_of right
                val l_tm = tree_tm_of left
                val r_tm = tree_tm_of right
                in
                  if k <= l_k2_str then let
                    val sub = tree_miss_thm left
                    in skel_tree_miss_branch_l
                      [vtT |-> n_tm, vtL |-> l_tm, vtR |-> r_tm,
                       vk1 |-> n_k1, vk2 |-> n_k2, vkL |-> l_k2, vk |-> key_tm]
                      [def_thm, sub, n_wf] end
                  else if k >= r_k1_str then let
                    val sub = tree_miss_thm right
                    in skel_tree_miss_branch_r
                      [vtT |-> n_tm, vtL |-> l_tm, vtR |-> r_tm,
                       vk1 |-> n_k1, vk2 |-> n_k2, vkR |-> r_k1, vk |-> key_tm]
                      [def_thm, sub, n_wf] end
                  else let
                    (* gap: l_k2_str < k < r_k1_str *)
                    val _ = prof_mk_lt_site_miss_lt := !prof_mk_lt_site_miss_lt + 1
                    val _ = prof_mk_lt_site_miss_gt := !prof_mk_lt_site_miss_gt + 1
                    val lt_kL_k = mk_lt_thm l_k2 key_tm
                    val lt_k_kR = mk_lt_thm key_tm r_k1
                    val l_wf = wf_thm_of left
                    val r_wf = wf_thm_of right
                    in skel_tree_miss_gap
                      [vtT |-> n_tm, vtL |-> l_tm, vtR |-> r_tm,
                       vk1 |-> n_k1, vk2 |-> n_k2,
                       vkL |-> l_k2, vkR |-> r_k1, vk |-> key_tm]
                      [def_thm, l_wf, r_wf, lt_kL_k, lt_k_kR] end
                end
              end
            val tm_thm = tree_miss_thm root
            in MATCH_MP ml_progTheory.tree_miss_imp_lookup tm_thm end
          end
      val _ = tree_lookup_thm_cache :=
        Redblackmap.insert (!tree_lookup_thm_cache, cache_key, thm)
      in thm end
end

(* --- env-constant ↔ (env_node, equiv_thm) map ---
   For each env constant C we have proved  |- nsLookup_all C = tree_lookup T
   the map carries the ML tree shadow T together with the equivalence theorem.
   nsLookup_conv dispatches through this map to turn
     nsLookup C.v (Short k)
   into the concrete rhs via the chain
     nsLookup C.v (Short k) = (nsLookup_all C k).sv
                            = (tree_lookup T k).sv     [equiv]
                            = entry.sv                  [tree_lookup_hit]
                            = <concrete value>          [EVAL] *)

val env_tree_map : (term, env_node * thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)

fun env_tree_register env_const node equiv_thm =
    env_tree_map := Redblackmap.insert (!env_tree_map, env_const, (node, equiv_thm))

(* Rebuild env_node shadow from a tree term. Walks the structure and
   re-derives WF via mk_leaf_node / mk_branch_node. If the term is a
   defined constant (typical after cross-theory lazy-load), unfold it
   via its Definition first. *)
(* Rebuild an env_node shadow from an existing tree constant, REUSING the
   saved Definitions rather than creating fresh ones. Each node's tree_tm
   is the existing constant; def_thm is its saved Definition (via DB.fetch);
   WF is re-derived from the Definition + children's WFs using the CPS
   forms. Called from try_lazy_load so cross-theory lookups don't allocate
   parallel constants. *)
fun rebuild_node tree_tm = let
  val (def, rhs_tm) =
    if is_const tree_tm then let
      val {Name, Thy, ...} = dest_thy_const tree_tm
      val def = DB.fetch Thy (Name ^ "_def")
      val rhs_tm = rhs (concl def)
      in (def, rhs_tm) end
    else (REFL tree_tm, tree_tm)
  (* Look for a saved <name>_wf in the constant's home theory.  If
     absent (legacy theories, or non-constant tree_tm), derive fresh. *)
  fun fetch_saved_wf () =
    if is_const tree_tm then let
      val {Name, Thy, ...} = dest_thy_const tree_tm
      in SOME (DB.fetch Thy (Name ^ "_wf"))
         handle HOL_ERR _ => NONE end
    else NONE
  in
    case strip_comb rhs_tm of
      (c, [a, b]) =>
      if same_const c EnvLeaf_tm then let
        val key_str = mlstringSyntax.dest_mlstring a
        val wf_thm = case fetch_saved_wf () of
            SOME t => t
          | NONE => MATCH_MP ml_progTheory.env_wf_leaf_cps def
        in ELeaf { key_tm = a, key_str = key_str, entry_tm = b,
          tree_tm = tree_tm, def_thm = def, wf_thm = wf_thm } end
      else if same_const c EnvBranch_tm then let
        val left = rebuild_node a
        val right = rebuild_node b
        val (k1_tm, kl_tm) = bounds_of left
        val (kr_tm, k2_tm) = bounds_of right
        val (k1_str, _) = key_strs_of left
        val (_, k2_str) = key_strs_of right
        val wf_thm = case fetch_saved_wf () of
            SOME t => t
          | NONE => let
              val lt_thm = EQT_ELIM
                (EVAL (list_mk_icomb (mlstring_lt_tm, [kl_tm, kr_tm])))
            in MATCH_MP ml_progTheory.env_wf_branch_intro_cps
                 (LIST_CONJ [def, wf_thm_of left, wf_thm_of right, lt_thm])
            end
        in EBranch { left = left, right = right, k1_tm = k1_tm, k2_tm = k2_tm,
          k1_str = k1_str, k2_str = k2_str, tree_tm = tree_tm, def_thm = def,
          wf_thm = wf_thm, depth = 1 + Int.max (depth_of left, depth_of right) } end
      else failwith ("rebuild_node: constructor not recognised: " ^ Parse.term_to_string c)
    | _ => failwith ("rebuild_node: unexpected rhs shape " ^ Parse.term_to_string rhs_tm)
  end

(* Attempt to lazily load an env_const's tree data from previously saved
   theorems (via DB.fetch on the naming convention). Returns SOME if it
   succeeds in registering. *)
fun try_lazy_load env_const = let
  val {Name, Thy, ...} = dest_thy_const env_const handle HOL_ERR _ => raise UNCHANGED
  val equiv_thm = DB.fetch Thy (tree_equiv_name Name) handle HOL_ERR _ => raise UNCHANGED
  val tree_tm = rand (rhs (concl equiv_thm)) handle HOL_ERR _ => raise UNCHANGED
  val node = rebuild_node tree_tm
  val _ = env_tree_register env_const node equiv_thm
  in SOME (node, equiv_thm) end
  handle UNCHANGED => NONE | e => (
    TextIO.output (TextIO.stdErr,
      "try_lazy_load " ^ Parse.term_to_string env_const ^
      " error: " ^ General.exnMessage e ^ "\n");
    NONE)

(* Forward ref for the lazy init-env registration hook.  Filled in below
   (after register_init_env is defined) with the real ensure function. *)
val ensure_init_env_hook : (unit -> unit) ref = ref (fn () => ())

fun env_tree_lookup env_const = (
  !ensure_init_env_hook ();
  case Redblackmap.peek (!env_tree_map, env_const) of
    NONE => try_lazy_load env_const
  | entry => entry)

fun env_tree_has env_const = isSome (env_tree_lookup env_const)

(* --- derive_nsLookup_tree ---
   Replacement for derive_nsLookup_thms using the tree_lookup/nsLookup_all
   framework. Given the new env-abbrev def (env_N = <rhs>), walks the rhs,
   looks up the base env in env_tree_map, builds the new env_node, and
   proves the new equivalence
     |- !k. nsLookup_all env_N k = tree_lookup <new_tree_tm> k
   via the step lemmas. Currently handles WRITE at the edges (prepend
   when new key < tree.k1, append when new key > tree.k2). Other shapes
   and ops return NONE and let the caller fall through. *)

val sv_option_ty = mk_thy_type {Thy = "option", Tyop = "option", Args = [
  mk_thy_type {Thy = "semanticPrimitives", Tyop = "v", Args = []}]}

datatype env_op =
    OpWrite     of term * term * term     (* n,  v,       base *)
  | OpWriteCons of term * term * term     (* n,  c,       base *)
  | OpWriteMod  of term * term * term     (* mn, mod_env, base *)
  | OpMergeEnv  of term * term            (* e1, e2 *)

fun classify_rhs rhs = let
  val (f, args) = strip_comb rhs
  in
    case (fst (dest_const f) handle _ => "", args) of
      ("write",      [n, v, e])  => SOME (OpWrite     (n, v, e))
    | ("write_cons", [n, c, e])  => SOME (OpWriteCons (n, c, e))
    | ("write_mod",  [mn, m, e]) => SOME (OpWriteMod  (mn, m, e))
    | ("merge_env",  [e1, e2])   => SOME (OpMergeEnv  (e1, e2))
    | _ => NONE
  end handle HOL_ERR _ => NONE

(* --- env_entry / sem_env constants (bound once, used without Parse.Term) ---
   All record manipulation goes through these.  No Parse.Term calls in the
   library means scripts don't need ml_prog as an ancestor for the
   record-field parser. *)
val env_entry_sv_acc = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sv"}
val env_entry_sc_acc = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sc"}
val env_entry_mv_acc = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mv"}
val env_entry_mc_acc = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mc"}
val env_entry_sv_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sv_fupd"}
val env_entry_sc_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sc_fupd"}
val env_entry_mv_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mv_fupd"}
val env_entry_mc_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mc_fupd"}
val empty_entry_const = prim_mk_const {Thy = "ml_prog", Name = "empty_entry"}
val sem_env_v_sel = prim_mk_const {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.v"}
val sem_env_c_sel = prim_mk_const {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.c"}

(* Apply `fupd (K v) base` — build the term `fupd (\_. v) base`. *)
fun mk_field_update fupd v base = list_mk_comb (fupd, [combinSyntax.mk_K_1 (v, type_of v), base])

(* Build leaf entries as a single record update on `empty_entry`, matching
   the standard HOL4 record-literal representation sv_fupd (K ...) empty_entry
   (but reaching it constructively — no Parse.Term). *)
fun mk_sv_entry_tm v_tm =
  mk_field_update env_entry_sv_fupd (optionSyntax.mk_some v_tm) empty_entry_const

fun mk_sc_entry_tm c_tm =
  mk_field_update env_entry_sc_fupd (optionSyntax.mk_some c_tm) empty_entry_const

fun mk_mod_entry_tm mod_env_tm = let
  val mv_v = optionSyntax.mk_some (mk_icomb (sem_env_v_sel, mod_env_tm))
  val mc_v = optionSyntax.mk_some (mk_icomb (sem_env_c_sel, mod_env_tm))
  val with_mv = mk_field_update env_entry_mv_fupd mv_v empty_entry_const
  in mk_field_update env_entry_mc_fupd mc_v with_mv end

(* insert_leaf_into: given key n_tm (with string n_str), a prebuilt leaf
   entry_tm, and a base env_node, produce (new_node, update_thm) with
     update_thm : |- !k. tree_lookup new_node.tree_tm k =
                            if k = n then final_entry else tree_lookup base.tree_tm k
   Handles prepend/append/splice, recursive descent, and key collision (where
   the final_entry is computed from the old leaf's entry via merge_fn). *)
(* Apply AVL rebalance to a just-constructed EBranch env_node and transform
   the corresponding update theorem through the rotation. *)
val empty_env_tm = prim_mk_const {Name = "empty_env", Thy = "ml_prog"}

(* Pre-prepared theorems used by derive_nsLookup_tree_merge / build_tree_anon
   to avoid ONCE_REWRITE_RULE on per-call equiv composition.  The original
   merge_env_empty_env has shape `merge_env env empty_env = env /\
   merge_env empty_env env = env` with a single outer ! over env, so we
   GEN_ALL after taking CONJUNCTs to recover universally-quantified forms. *)
val (merge_empty_right, merge_empty_left) = CONJ_PAIR (SPEC_ALL ml_progTheory.merge_env_empty_env)

val nsLookup_all_const = prim_mk_const {Name = "nsLookup_all", Thy = "ml_prog"}
val tree_lookup_const = prim_mk_const {Name = "tree_lookup", Thy = "ml_prog"}

(* Shared: env_const = <op n x empty_env> where op ∈ {write, write_cons, ...}.
   Produces a singleton leaf without needing a base tree entry in the map. *)
fun derive_nsLookup_tree_add_empty env_const def n step_lemma entry_tm = let
  val () = let
    val f = TextIO.openAppend "/tmp/dump.log"
    val _ = TextIO.output (f,
      "[add_empty] env_const: " ^
      Parse.term_to_string env_const ^ "\n  n: " ^
      Parse.term_to_string n ^ "\n")
    in TextIO.closeOut f end
  val new_leaf = mk_leaf_node n entry_tm
  val goal_lhs = mk_icomb (nsLookup_all_const, env_const)
  val goal_rhs = mk_icomb (tree_lookup_const, tree_tm_of new_leaf)
  val k_ty = fst (dom_rng (type_of goal_lhs))
  val k_var = mk_var ("k", k_ty)
  val applied_goal = mk_eq (mk_comb (goal_lhs, k_var), mk_comb (goal_rhs, k_var))
  (* If def is a REFL (anonymous env), PURE_REWRITE_TAC [def] is a
      no-op — skip it to avoid the risk of it looping on compound LHS. *)
  val def_is_refl = aconv (lhs (concl def)) (rhs (concl def))
  val pointwise_thm = prove (applied_goal,
    (if def_is_refl then all_tac else PURE_REWRITE_TAC [def])
    \\ once_rewrite_tac [step_lemma]
    \\ simp [ml_progTheory.nsLookup_all_empty_env,
              def_thm_of new_leaf, ml_progTheory.tree_lookup_def,
              ml_progTheory.empty_entry_def])
  val equiv_thm = CONV_RULE (REWR_CONV (GSYM FUN_EQ_THM)) (GEN k_var pointwise_thm)
  in (new_leaf, equiv_thm) end

fun derive_nsLookup_tree_write_empty env_const def n v =
    derive_nsLookup_tree_add_empty env_const def n
      ml_progTheory.nsLookup_all_write (mk_sv_entry_tm v)

fun derive_nsLookup_tree_write_cons_empty env_const def n c =
    derive_nsLookup_tree_add_empty env_const def n
      ml_progTheory.nsLookup_all_write_cons (mk_sc_entry_tm c)

fun derive_nsLookup_tree_write_mod_empty env_const def mn mod_env =
    derive_nsLookup_tree_add_empty env_const def mn
      ml_progTheory.nsLookup_all_write_mod (mk_mod_entry_tm mod_env)

(* merge_env with coalescing.  Walks T2's leaves; for each (k, v):
   - if T1 already has (k, v) with the exact same entry, skip (reuse T1);
   - otherwise insert into the accumulator using insert_leaf_into + a
     combine_entries-based merge_fn (normalized via combine_entries_*_fupd
     simp rules).  The final equivalence is proved pointwise via FUN_EQ_THM
     + case analysis on k against each distinct leaf key. *)
val combine_entries_tm = prim_mk_const {Name = "combine_entries", Thy = "ml_prog"}

val combine_entries_simps = [
  ml_progTheory.combine_entries_empty_left,
  ml_progTheory.combine_entries_empty_right,
  ml_progTheory.combine_entries_sv_fupd,
  ml_progTheory.combine_entries_sc_fupd,
  ml_progTheory.combine_entries_mv_fupd,
  ml_progTheory.combine_entries_mc_fupd]

(* Helper: tree_lookup expression, for TRANS/AP_TERM use *)
val tree_lookup_tm = prim_mk_const {Name = "tree_lookup", Thy = "ml_prog"}
fun mk_tree_lookup_tm tree_tm = mk_icomb (tree_lookup_tm, tree_tm)

(* thm relating two env_node's tree_tm via tree_lookup: REFL case. *)
fun refl_tree_lookup node = REFL (mk_tree_lookup_tm (tree_tm_of node))

(* From def_thm : node.tt = <rhs>,  derive
     tree_lookup node.tt = tree_lookup <rhs>
   (i.e. lift equality through tree_lookup). *)
val lift_tree_lookup = AP_TERM tree_lookup_tm

(* Compute a normalized-entry theorem for coalesce:
     combine_entries v1 v2 = <simplified> (using combine_entries_simps).
   If the result is aconv to v1 or v2, we can reuse that as the new entry. *)
fun simp_combine_entries v1 v2 = let
  val tm = list_mk_comb (combine_entries_tm, [v1, v2])
  in QCONV (SIMP_CONV (srw_ss()) combine_entries_simps) tm handle UNCHANGED => REFL tm end

(* Create a new EnvBranch env_node without trying to prove WF (no lt_thm).
   Used when WF is proved externally (e.g. via an established equivalence).
   Returns a node with wf_thm = TRUTH (placeholder).  Callers should supply
   the real wf_thm via a separate construction. *)
(* Actually we don't need a WF-free builder; callers know k vs T's range
   and always route to WF-preserving constructions. *)

(* Build EnvBranch a b as a HOL term (faster than list_mk_comb). *)
fun mk_envbranch a b = mk_comb (mk_comb (EnvBranch_tm, a), b)

(* rebalance_join A B: builds an env_node representing EnvBranch A B.
   Precondition: A.max_key < B.min_key (disjoint, strictly ordered).
   Returns (result, thm : tree_lookup (EnvBranch A.tm B.tm) = tree_lookup result.tm).

   Algorithm: AVL join — descend the spine of the taller tree until
   heights are within 1, then mk_branch_node_raw + single rebalance_node
   to absorb the residual imbalance.

   Result is AVL-balanced (depth ≤ max(depth A, depth B) + 1).
   Time: O(|depth A - depth B|).

   Cost note: each level of descent allocates 1 fresh tree constant
   (via mk_branch_node_raw on the way back up), so this can create more
   constants per call than a single mk_branch when heights are very
   different.  The trade-off: the AVL invariant keeps subsequent
   operations near-optimal. *)
(* rebalance_join_with: caller supplies an lt_thunk producing the
   precondition mlstring_lt A.max B.min — used at the base case (and
   forwarded unchanged to recursive calls, since A2.max = A.max and
   B1.min = B.min keep the same bounds).  The two mid-recursion
   mk_branch_node_compound calls get their lt from A's / B's WF via
   lt_from_parent_wf, not from the thunk. *)
fun rebalance_join_with lt_thunk A B =
  case (depth_of A, depth_of B) of (dA, dB) =>
  if dA > dB + 1 then let
    (* A is taller: descend its right spine.
        Recurse on (A.right, B) → D, then re-attach A.left as a single
        mk_branch + rebalance_node (heights of A.left and D differ by ≤ 2). *)
    val {left = A1, right = A2, ...} = case A of EBranch b => b | _ =>
      failwith "avl_join: A is a leaf but reportedly much taller than B"
    val A_def = def_thm_of A
    val A_wf  = wf_thm_of A
    val A_tm  = tree_tm_of A
    val A1_tm = tree_tm_of A1
    val A2_tm = tree_tm_of A2
    val B_tm  = tree_tm_of B
    val branch_AB     = mk_envbranch A_tm B_tm
    val branch_A2_B   = mk_envbranch A2_tm B_tm
    val branch_A1_A2B = mk_envbranch A1_tm branch_A2_B
    val rot_right = skel_rotate_right
      [vtA |-> A1_tm, vtB |-> A2_tm, vtC |-> B_tm, vtL |-> A_tm, vtR |-> branch_A2_B,
        vtT |-> branch_AB, vtT' |-> branch_A1_A2B]
      [A_def, REFL branch_AB, REFL branch_A2_B, REFL branch_A1_A2B]
    (* A2.max = A.max, so the precondition for (A2, B) is the same lt. *)
    val (D, thm_D) = rebalance_join_with lt_thunk A2 B
    val D_tm = tree_tm_of D
    val branch_A1_D = mk_envbranch A1_tm D_tm
    val lift_D = skel_branch_cong
      [vtT |-> branch_A1_A2B, vtT' |-> branch_A1_D, v_l |-> A1_tm, v_l' |-> A1_tm,
        v_r |-> branch_A2_B, v_r' |-> D_tm]
      [REFL branch_A1_A2B, REFL branch_A1_D, tl_refl A1_tm, thm_D]
    (* Single mk_branch + rebalance_node: A1 and D heights ≤ 2
        apart, so one rotation handles any imbalance.  No recursion
        here — that would be exponential. *)
    (* D.min = A2.min (A2 < B), so lt(A1.max, D.min) = lt(A1.max, A2.min),
       which is witnessed by A's WF on EnvBranch A1 A2. *)
    val lt_A1_D = lt_from_parent_wf
      {parent_tm = A_tm, parent_def = A_def, parent_wf = A_wf, l = A1, r = A2}
    val raw = mk_branch_node_compound_with lt_A1_D A1 D
    val raw_unfold = lift_tree_lookup (def_thm_of raw)
    val (result, rot_eq) = rebalance_node raw
    val join_thm = TRANS (SYM raw_unfold) rot_eq
    in (result, TRANS rot_right (TRANS lift_D join_thm)) end
  else if dB > dA + 1 then let
    (* B is taller: descend its left spine. *)
    val {left = B1, right = B2, ...} = case B of EBranch b => b | _ =>
      failwith "avl_join: B is a leaf but reportedly much taller than A"
    val B_def = def_thm_of B
    val B_wf  = wf_thm_of B
    val A_tm  = tree_tm_of A
    val B_tm  = tree_tm_of B
    val B1_tm = tree_tm_of B1
    val B2_tm = tree_tm_of B2
    val branch_AB     = mk_envbranch A_tm B_tm
    val branch_A_B1   = mk_envbranch A_tm B1_tm
    val branch_AB1_B2 = mk_envbranch branch_A_B1 B2_tm
    val rot_left = skel_rotate_left
      [vtA |-> A_tm, vtB |-> B1_tm, vtC |-> B2_tm, vtR |-> B_tm, vtL |-> branch_A_B1,
        vtT |-> branch_AB, vtT' |-> branch_AB1_B2]
      [B_def, REFL branch_AB, REFL branch_A_B1, REFL branch_AB1_B2]
    (* B1.min = B.min, so the precondition for (A, B1) is the same lt. *)
    val (D, thm_D) = rebalance_join_with lt_thunk A B1
    val D_tm = tree_tm_of D
    val branch_D_B2 = mk_envbranch D_tm B2_tm
    val lift_D = skel_branch_cong
      [vtT |-> branch_AB1_B2, vtT' |-> branch_D_B2, v_l |-> branch_A_B1, v_l' |-> D_tm,
        v_r |-> B2_tm, v_r' |-> B2_tm]
      [REFL branch_AB1_B2, REFL branch_D_B2, thm_D, tl_refl B2_tm]
    (* D.max = B1.max (A < B1), so lt(D.max, B2.min) = lt(B1.max, B2.min),
       witnessed by B's WF on EnvBranch B1 B2. *)
    val lt_D_B2 = lt_from_parent_wf
      {parent_tm = B_tm, parent_def = B_def, parent_wf = B_wf, l = B1, r = B2}
    val raw = mk_branch_node_compound_with lt_D_B2 D B2
    val raw_unfold = lift_tree_lookup (def_thm_of raw)
    val (result, rot_eq) = rebalance_node raw
    val join_thm = TRANS (SYM raw_unfold) rot_eq
    in (result, TRANS rot_left (TRANS lift_D join_thm)) end
  else let
    (* Base case: heights close enough that one rebalance_node suffices.
       The caller's lt_thunk is the precondition. *)
    val raw = mk_branch_node_compound_with lt_thunk A B
    val raw_unfold = lift_tree_lookup (def_thm_of raw)
    val (bal, rot_eq) = rebalance_node raw
    in (bal, TRANS (SYM raw_unfold) rot_eq) end

fun rebalance_join A B = let
  fun thunk () = mk_lt_thm (#2 (bounds_of A)) (#1 (bounds_of B))
  in rebalance_join_with thunk A B end

(* Unified merge/insert.  Given two env_nodes A, B, produce an env_node
   whose tree_lookup equals tree_lookup (EnvBranch A.tm B.tm), coalescing
   shared keys with LEFT priority (merge_env semantics).
   Cases:
   (1) Ranges disjoint: rebalance_join in the correct order.
   (2) A = EBranch (A1, A2), B's range entirely on one side of A: split A.
   (3) B = EBranch (B1, B2): split B; recurse A+B1 then result+B2.
   (4) Both leaves with same key: coalesce via combine_entries.  *)
fun merge_trees A B = let
  val A_tm = tree_tm_of A
  val B_tm = tree_tm_of B
  val A_wf = wf_thm_of A
  val B_wf = wf_thm_of B
  val (A_min_tm, A_max_tm) = bounds_of A
  val (B_min_tm, B_max_tm) = bounds_of B
  val (A_min_str, A_max_str) = key_strs_of A
  val (B_min_str, B_max_str) = key_strs_of B
  val branch_AB = mk_envbranch A_tm B_tm
  in
    if A_max_str < B_min_str then
      (* Case 1a: A.keys < B.keys, disjoint. *)
      rebalance_join_with (fn () => mk_lt_thm A_max_tm B_min_tm) A B
    else if B_max_str < A_min_str then let
      (* Case 1b: B.keys < A.keys, commute then join.  Thunk is lazy so
         rebalance_join_with only pays for mk_lt_thm when its base case
         actually needs it; the swap disjunct below also threads the
         lt through once via the shared lt_cache. *)
      val lt_BA = mk_lt_thm B_max_tm A_min_tm
      val (result, thm_BA) = rebalance_join_with (K lt_BA) B A
      val branch_BA = mk_envbranch B_tm A_tm
      val _ = prof_mk_lt_site_swap_outer := !prof_mk_lt_site_swap_outer + 1
      (* swap_cps disjunct: mlstring_lt A_max B_min OR mlstring_lt B_max A_min.
          We have B_max < A_min, which is the 2nd disjunct. *)
      val disj_thm = DISJ2 (list_mk_icomb (mlstring_lt_tm, [A_max_tm, B_min_tm])) lt_BA
      val swap_thm = skel_swap
        [vtT |-> branch_AB, vtT' |-> branch_BA, vX |-> A_tm, vY |-> B_tm,
          vkX1 |-> A_min_tm, vkX2 |-> A_max_tm, vkY1 |-> B_min_tm, vkY2 |-> B_max_tm]
        [REFL branch_AB, REFL branch_BA, A_wf, B_wf, disj_thm]
      in (result, TRANS swap_thm thm_BA) end
    else
      (* Ranges overlap.  Dispatch on A's shape. *)
      case A of
        EBranch {left = A1, right = A2, ...} => let
        val (_, A1_max_str) = key_strs_of A1
        val (A2_min_str, _) = key_strs_of A2
        in
          if B_max_str < A2_min_str then
            merge_trees_via_left A A1 A2 B branch_AB
          else if B_min_str > A1_max_str then
            merge_trees_via_right A A1 A2 B branch_AB
          else
            merge_trees_split_right A B branch_AB
        end
      | _ =>
        case B of
          EBranch _ => merge_trees_split_right A B branch_AB
        | ELeaf _ => merge_trees_coalesce A B branch_AB
  end

(* Case 2a: A = EBranch(A1, A2), B's keys all < A2.min.
   Transform tree_lookup (EnvBranch A B) into tree_lookup (EnvBranch (EnvBranch A1 B) A2)
   via rotate_right + inner commute + rotate_left, then recurse merge_trees(A1, B). *)
and merge_trees_via_left A A1 A2 B branch_AB = let
  val A_def = def_thm_of A
  val A_tm = tree_tm_of A
  val A1_tm = tree_tm_of A1
  val A2_tm = tree_tm_of A2
  val B_tm = tree_tm_of B
  val (A2_min_tm, A2_max_tm) = bounds_of A2
  val (B_min_tm, B_max_tm) = bounds_of B
  val A2_wf = wf_thm_of A2
  val B_wf = wf_thm_of B
  val branch_A2_B = mk_envbranch A2_tm B_tm
  val branch_A1_A2B = mk_envbranch A1_tm branch_A2_B
  val rot_right = skel_rotate_right
    [vtA |-> A1_tm, vtB |-> A2_tm, vtC |-> B_tm, vtL |-> A_tm, vtR |-> branch_A2_B,
      vtT |-> branch_AB, vtT' |-> branch_A1_A2B]
    [A_def, REFL branch_AB, REFL branch_A2_B, REFL branch_A1_A2B]
  val branch_B_A2 = mk_envbranch B_tm A2_tm
  val _ = prof_mk_lt_site_swap_via_left :=
            !prof_mk_lt_site_swap_via_left + 1
  val lt_B_A2 = mk_lt_thm B_max_tm A2_min_tm
  (* swap_cps disjunct for X=A2, Y=B: (A2_max < B_min) OR (B_max < A2_min).
      We have B_max < A2_min — that's the RIGHT disjunct, use DISJ2. *)
  val disj_swap = DISJ2 (list_mk_icomb (mlstring_lt_tm, [A2_max_tm, B_min_tm])) lt_B_A2
  val inner_swap = skel_swap
    [vtT |-> branch_A2_B, vtT' |-> branch_B_A2, vX |-> A2_tm, vY |-> B_tm,
      vkX1 |-> A2_min_tm, vkX2 |-> A2_max_tm, vkY1 |-> B_min_tm, vkY2 |-> B_max_tm]
    [REFL branch_A2_B, REFL branch_B_A2, A2_wf, B_wf, disj_swap]
  val branch_A1_BA2 = mk_envbranch A1_tm branch_B_A2
  val lift_swap = skel_branch_cong
    [vtT |-> branch_A1_A2B, vtT' |-> branch_A1_BA2, v_l |-> A1_tm, v_l' |-> A1_tm,
      v_r |-> branch_A2_B, v_r' |-> branch_B_A2]
    [REFL branch_A1_A2B, REFL branch_A1_BA2, tl_refl A1_tm, inner_swap]
  val branch_A1_B = mk_envbranch A1_tm B_tm
  val branch_A1B_A2 = mk_envbranch branch_A1_B A2_tm
  val rot_left = skel_rotate_left
    [vtA |-> A1_tm, vtB |-> B_tm, vtC |-> A2_tm, vtR |-> branch_B_A2,
      vtL |-> branch_A1_B, vtT |-> branch_A1_BA2, vtT' |-> branch_A1B_A2]
    [REFL branch_B_A2, REFL branch_A1_BA2, REFL branch_A1_B, REFL branch_A1B_A2]
  val setup = TRANS rot_right (TRANS lift_swap rot_left)
  val (D, thm_D) = merge_trees A1 B
  val D_tm = tree_tm_of D
  val branch_D_A2 = mk_envbranch D_tm A2_tm
  val lift_D = skel_branch_cong
    [vtT |-> branch_A1B_A2, vtT' |-> branch_D_A2, v_l |-> branch_A1_B, v_l' |-> D_tm,
      v_r |-> A2_tm, v_r' |-> A2_tm]
    [REFL branch_A1B_A2, REFL branch_D_A2, thm_D, tl_refl A2_tm]
  val (result, thm_bal) = rebalance_join D A2
  in (result, TRANS setup (TRANS lift_D thm_bal)) end

(* Case 2b: A = EBranch(A1, A2), B's keys all > A1.max.
   Transform via rotate_right, then recurse merge_trees(A2, B), rejoin with A1. *)
and merge_trees_via_right A A1 A2 B branch_AB = let
  val A_def = def_thm_of A
  val A_tm = tree_tm_of A
  val A1_tm = tree_tm_of A1
  val A2_tm = tree_tm_of A2
  val B_tm = tree_tm_of B
  val branch_A2_B = mk_envbranch A2_tm B_tm
  val branch_A1_A2B = mk_envbranch A1_tm branch_A2_B
  val rot_right = skel_rotate_right
    [vtA |-> A1_tm, vtB |-> A2_tm, vtC |-> B_tm, vtL |-> A_tm,
      vtR |-> branch_A2_B, vtT |-> branch_AB, vtT' |-> branch_A1_A2B]
    [A_def, REFL branch_AB, REFL branch_A2_B, REFL branch_A1_A2B]
  val (D, thm_D) = merge_trees A2 B
  val D_tm = tree_tm_of D
  val branch_A1_D = mk_envbranch A1_tm D_tm
  val lift_D = skel_branch_cong
    [vtT |-> branch_A1_A2B, vtT' |-> branch_A1_D, v_l |-> A1_tm,
      v_l' |-> A1_tm, v_r |-> branch_A2_B, v_r' |-> D_tm]
    [REFL branch_A1_A2B, REFL branch_A1_D, tl_refl A1_tm, thm_D]
  val (result, thm_bal) = rebalance_join A1 D
  in (result, TRANS rot_right (TRANS lift_D thm_bal)) end

(* Case 3: B = EBranch(B1, B2), split B and recurse.
   rotate_left to transform (A, (B1, B2)) -> ((A, B1), B2),
   recurse merge_trees(A, B1) = D, lift via branch_cong,
   then recurse merge_trees(D, B2) to finish. *)
and merge_trees_split_right A B branch_AB = let
  val A_tm = tree_tm_of A
  val B_tm = tree_tm_of B
  val {left = B1, right = B2, ...} = case B of EBranch b => b | _ =>
    failwith "merge_trees_split_right: B not a branch"
  val B1_tm = tree_tm_of B1
  val B2_tm = tree_tm_of B2
  val B_def = def_thm_of B
  val branch_A_B1 = mk_envbranch A_tm B1_tm
  val branch_AB1_B2 = mk_envbranch branch_A_B1 B2_tm
  val rot_left = skel_rotate_left
    [vtA |-> A_tm, vtB |-> B1_tm, vtC |-> B2_tm,
      vtR |-> B_tm, vtL |-> branch_A_B1,
      vtT |-> branch_AB, vtT' |-> branch_AB1_B2]
    [B_def, REFL branch_AB, REFL branch_A_B1, REFL branch_AB1_B2]
  val (D, thm_D) = merge_trees A B1
  val D_tm = tree_tm_of D
  val branch_D_B2 = mk_envbranch D_tm B2_tm
  val lift_D = skel_branch_cong
    [vtT |-> branch_AB1_B2, vtT' |-> branch_D_B2,
      v_l |-> branch_A_B1, v_l' |-> D_tm,
      v_r |-> B2_tm, v_r' |-> B2_tm]
    [REFL branch_AB1_B2, REFL branch_D_B2, thm_D, tl_refl B2_tm]
  val (result, thm_E) = merge_trees D B2
  (* thm_E : tree_lookup (EnvBranch D.tm B2.tm) = tree_lookup result.tm *)
  in (result, TRANS rot_left (TRANS lift_D thm_E)) end

(* Case 4: both are leaves with the same key — coalesce via combine_entries. *)
and merge_trees_coalesce A B branch_AB = let
  val {key_tm = k_tm, entry_tm = v1_tm, ...} = case A of ELeaf r => r | _ =>
    failwith "coalesce: A not leaf"
  val {entry_tm = v2_tm, ...} = case B of ELeaf r => r | _ => failwith "coalesce: B not leaf"
  val A_def = def_thm_of A
  val B_def = def_thm_of B
  val combine_tm = list_mk_comb (combine_entries_tm, [v1_tm, v2_tm])
  val envleaf_k_combine = mk_comb (mk_comb (EnvLeaf_tm, k_tm), combine_tm)
  val coalesce_thm = skel_coalesce_leaves
    [vtL1 |-> tree_tm_of A, vtL2 |-> tree_tm_of B, vtT |-> branch_AB,
      vtL |-> envleaf_k_combine, vk |-> k_tm, v_e1 |-> v1_tm, v_e2 |-> v2_tm]
    [A_def, B_def, REFL branch_AB, REFL envleaf_k_combine]
  val simp_eq = simp_combine_entries v1_tm v2_tm
  val combined_v = rhs (concl simp_eq)
  val envleaf_k = mk_icomb (EnvLeaf_tm, k_tm)
  val leaf_eq = AP_TERM envleaf_k simp_eq
  val under_lookup = AP_TERM tree_lookup_tm leaf_eq
  in
    if aconv combined_v v1_tm then let
      val t_unfold = lift_tree_lookup A_def
      in (A, TRANS coalesce_thm (TRANS under_lookup (SYM t_unfold))) end
    else let
      val new_leaf = mk_leaf_node k_tm combined_v
      val new_unfold = lift_tree_lookup (def_thm_of new_leaf)
      in (new_leaf, TRANS coalesce_thm (TRANS under_lookup (SYM new_unfold))) end
  end

(* Generic builder for write/write_cons/write_mod using merge_trees.
   Builds a singleton leaf, calls merge_trees(leaf, base), and threads through
   the tree-level step theorem (nsLookup_all_write_tree_cps, etc.). *)
fun derive_nsLookup_tree_add_via_merge def n skel_step entry_tm
    subst_extra (base_node, base_equiv) = let
  val t0 = Time.now ()
  val new_leaf = mk_leaf_node n entry_tm
  val t1 = Time.now ()
  val _ = prof_wr_leaf := !prof_wr_leaf + Time.toReal (Time.- (t1, t0))
  val base_tm = tree_tm_of base_node
  val leaf_tm = tree_tm_of new_leaf
  val branch_leaf_base = mk_envbranch leaf_tm base_tm
  val base_env_tm = rand (lhs (concl base_equiv))
  val step_thm = skel_step
    ([vtT  |-> base_tm, vtL  |-> leaf_tm, vTnew |-> branch_leaf_base,
      vn   |-> n, v_env |-> base_env_tm] @ subst_extra)
    [base_equiv, def_thm_of new_leaf, REFL branch_leaf_base]
  val t2 = Time.now ()
  val _ = prof_wr_step := !prof_wr_step + Time.toReal (Time.- (t2, t1))
  val (transient_node, merge_thm) = merge_trees new_leaf base_node
  val t3 = Time.now ()
  val _ = prof_wr_merge := !prof_wr_merge + Time.toReal (Time.- (t3, t2))
  val (new_node, mat_eq) = materialize_node transient_node
  val t4 = Time.now ()
  val _ = prof_wr_material := !prof_wr_material + Time.toReal (Time.- (t4, t3))
  val mat_thm = AP_TERM tree_lookup_tm mat_eq
  val combined = TRANS step_thm (TRANS merge_thm mat_thm)
  val equiv_thm =
    if aconv (lhs (concl def)) (rhs (concl def))
    then combined
    else TRANS (AP_TERM nsLookup_all_const def) combined
  val t5 = Time.now ()
  val _ = prof_wr_finish := !prof_wr_finish + Time.toReal (Time.- (t5, t4))
  in (new_node, equiv_thm) end

fun derive_nsLookup_tree_write def n v base = let
  val v_var = mk_var ("v", type_of v)
  in derive_nsLookup_tree_add_via_merge def n
    skel_write_tree (mk_sv_entry_tm v) [v_var |-> v] base end

fun derive_nsLookup_tree_write_cons def n c base = let
  val c_var = mk_var ("c", type_of c)
  in derive_nsLookup_tree_add_via_merge def n
    skel_write_cons_tree (mk_sc_entry_tm c) [c_var |-> c] base end

fun derive_nsLookup_tree_write_mod def mn mod_env base = let
  val mod_env_var = mk_var ("mod_env", type_of mod_env)
  in derive_nsLookup_tree_add_via_merge def mn
    skel_write_mod_tree (mk_mod_entry_tm mod_env) [mod_env_var |-> mod_env] base end

(* Coalescing merge_env entry point: function-level, no Cases_on. *)
fun derive_nsLookup_tree_merge env_const def e1 e2 (node1, equiv1) (node2, equiv2) = let
  val (transient_node, tree_merge_eq) = merge_trees node1 node2
  val (final_node, mat_eq) = materialize_node transient_node
  val mat_thm = AP_TERM tree_lookup_tm mat_eq
  val merge_tree_equiv = MATCH_MP ml_progTheory.nsLookup_all_merge_tree (CONJ equiv1 equiv2)
  val combined = TRANS merge_tree_equiv (TRANS tree_merge_eq mat_thm)
  val equiv_thm = TRANS (AP_TERM nsLookup_all_const def) combined
  in (final_node, equiv_thm) end

(* Build (env_node, equiv_thm) for a compound env term anonymously: no
   theory-constant save, no env_tree_map registration.  Used by `need_base`
   when the base of a write/write_cons/write_mod is itself a compound
   (e.g. nested Dtype expansions produce `write_cons A (write_cons B env_c)`
   in a single abbreviation RHS).  For empty_env bases, uses the *_empty
   builders; otherwise recurses. *)
val build_tree_anon_depth = ref 0
fun build_tree_anon env_tm = let
  val d = !build_tree_anon_depth
  val _ = build_tree_anon_depth := d + 1
  val t0 = if d = 0 then SOME (Time.now ()) else NONE
  fun finish r = (
    build_tree_anon_depth := d;
    case t0 of
      SOME t0' => (
      prof_build_anon := !prof_build_anon + Time.toReal (Time.- (Time.now (), t0'));
      prof_build_anon_n := !prof_build_anon_n + 1)
    | NONE => ();
    r)
  val r = case env_tree_lookup env_tm of
    SOME (node, equiv) => (node, equiv)
  | NONE =>
    if aconv env_tm empty_env_tm then
      failwith "build_tree_anon: empty_env has no tree representation"
    else let
      val anon_def = REFL env_tm
      (* NB: build_empty is a thunk, so the _empty proof only
          runs when b is actually empty_env. *)
      fun on_base b build_with_base build_empty =
        if aconv b empty_env_tm then build_empty ()
        else build_with_base (build_tree_anon b)
      in
        case classify_rhs env_tm of
          SOME (OpWrite (n, v, b)) =>
          on_base b
            (derive_nsLookup_tree_write anon_def n v)
            (fn () => derive_nsLookup_tree_write_empty env_tm anon_def n v)
        | SOME (OpWriteCons (n, c, b)) =>
          on_base b
            (derive_nsLookup_tree_write_cons anon_def n c)
            (fn () => derive_nsLookup_tree_write_cons_empty env_tm anon_def n c)
        | SOME (OpWriteMod (mn, m, b)) =>
          on_base b
            (derive_nsLookup_tree_write_mod anon_def mn m)
            (fn () => derive_nsLookup_tree_write_mod_empty env_tm anon_def mn m)
        | SOME (OpMergeEnv (e1, e2)) =>
          if aconv e1 empty_env_tm then let
            val (node, eq) = build_tree_anon e2
            (* eq : nsLookup_all e2 = tree_lookup tree.
                Build: nsLookup_all (merge_env empty_env e2)
                    = nsLookup_all e2 = tree_lookup tree *)
            val collapse = INST [v_env |-> e2] merge_empty_left
            val ap = AP_TERM nsLookup_all_const collapse
            val equiv = TRANS ap eq
            in (node, equiv) end
          else if aconv e2 empty_env_tm then let
            val (node, eq) = build_tree_anon e1
            val collapse = INST [v_env |-> e1] merge_empty_right
            val ap = AP_TERM nsLookup_all_const collapse
            val equiv = TRANS ap eq
            in (node, equiv) end
          else let
            val base1 = build_tree_anon e1
            val base2 = build_tree_anon e2
            in derive_nsLookup_tree_merge env_tm anon_def e1 e2 base1 base2 end
        | NONE =>
          failwith ("build_tree_anon: unrecognized env shape: " ^ Parse.term_to_string env_tm)
      end
  (* Cache the (anon) compound env_tm so that if the same compound
      term appears again (e.g. shared subterm across Dtypes), we hit
      the map instead of rebuilding. Key is a compound term, not a
      named constant — Term.compare handles aconv equality. *)
  val _ = case r of (node, equiv) => env_tree_register env_tm node equiv
  in finish r end

fun derive_nsLookup_tree def = let
  val (env_const, rhs) = def |> concl |> dest_eq
  val env_name = case Lib.total dest_const env_const of SOME (n, _) => n | NONE => "<compound>"
  fun need_base b =
    if aconv b empty_env_tm then NONE
    else case env_tree_lookup b of SOME base => SOME base | NONE =>
      SOME (build_tree_anon b)
  fun finish new_node equiv_thm = let
    val t_save0 = Time.now ()
    (* Cache in the in-memory map for any shape of env term. *)
    val _ = env_tree_register env_const new_node equiv_thm
    (* Only persist to the theory / ThmSet when the env is a
        named constant; compound terms (merge_env, write, etc.)
        have no stable name to save under. *)
    val _ = case Lib.total dest_const env_const of
      NONE => ()
    | SOME (env_name, _) => let
      val eq_name = tree_equiv_name env_name
      val wf_name = tree_wf_name env_name
      val thy = current_theory ()
      in
        allowing_rebind save_thm (eq_name, equiv_thm);
        allowing_rebind save_thm (wf_name, wf_thm_of new_node);
        (export_tree_equiv (thy ^ "." ^ eq_name) handle _ => ());
        (export_tree_wf (thy ^ "." ^ wf_name) handle _ => ())
      end
    val t_save1 = Time.now ()
    val _ = prof_tree_save := !prof_tree_save + Time.toReal (Time.- (t_save1, t_save0))
    in equiv_thm end
  in
    case classify_rhs rhs of
      SOME (OpWrite (n, v, base_const)) => let
      val t0 = Time.now ()
      val (new_node, equiv_thm) =
        case need_base base_const of
          NONE => derive_nsLookup_tree_write_empty env_const def n v
        | SOME base => derive_nsLookup_tree_write def n v base
      val t1 = Time.now ()
      val _ = prof_tree_write := !prof_tree_write + Time.toReal (Time.- (t1, t0))
      in finish new_node equiv_thm end
    | SOME (OpWriteCons (n, c, base_const)) => let
      val t0 = Time.now ()
      val (new_node, equiv_thm) =
        case need_base base_const of
          NONE => derive_nsLookup_tree_write_cons_empty env_const def n c
        | SOME base => derive_nsLookup_tree_write_cons def n c base
      val t1 = Time.now ()
      val _ = prof_tree_write := !prof_tree_write + Time.toReal (Time.- (t1, t0))
      in finish new_node equiv_thm end
    | SOME (OpWriteMod (mn, mod_env, base_const)) => let
      val t0 = Time.now ()
      val (new_node, equiv_thm) =
        case need_base base_const of
          NONE => derive_nsLookup_tree_write_mod_empty env_const def mn mod_env
        | SOME base => derive_nsLookup_tree_write_mod def mn mod_env base
      val t1 = Time.now ()
      val _ = prof_tree_write := !prof_tree_write + Time.toReal (Time.- (t1, t0))
      in finish new_node equiv_thm end
    | SOME (OpMergeEnv (e1, e2)) => let
      val t_m0 = Time.now ()
      val (new_node, equiv_thm) =
        if aconv e2 empty_env_tm then let
          (* merge_env e1 empty_env = e1.
              Compose: nsLookup_all env_const  [via def]
                    = nsLookup_all (merge_env e1 empty_env)
                    = nsLookup_all e1  [via merge_empty_right]
                    = tree_lookup base.tt  [base_equiv] *)
          val (base, base_equiv) = case need_base e1 of SOME s => s | _ =>
            failwith "derive_nsLookup_tree: merge_env e1 empty_env — e1 has no base"
          val collapse = INST [v_env |-> e1] merge_empty_right
          val collapse_v = AP_TERM nsLookup_all_const collapse
          val def_v = AP_TERM nsLookup_all_const def
          val equiv_thm = TRANS def_v (TRANS collapse_v base_equiv)
          in (base, equiv_thm) end
        else if aconv e1 empty_env_tm then let
          val (base, base_equiv) = case need_base e2 of SOME s => s | _ =>
            failwith "derive_nsLookup_tree: merge_env empty_env e2 — e2 has no base"
          val collapse = INST [v_env |-> e2] merge_empty_left
          val collapse_v = AP_TERM nsLookup_all_const collapse
          val def_v = AP_TERM nsLookup_all_const def
          val equiv_thm = TRANS def_v (TRANS collapse_v base_equiv)
          in (base, equiv_thm) end
        else let
          val base1 = case need_base e1 of SOME b => b | NONE =>
            failwith "impossible: e1 not empty but no base"
          val base2 = case need_base e2 of SOME b => b | NONE =>
            failwith "impossible: e2 not empty but no base"
          in derive_nsLookup_tree_merge env_const def e1 e2 base1 base2 end
      val t_m1 = Time.now ()
      val _ = prof_tree_merge := !prof_tree_merge + Time.toReal (Time.- (t_m1, t_m0))
      in finish new_node equiv_thm end
    | NONE => failwith ("derive_nsLookup_tree: unsupported rhs shape: " ^ Parse.term_to_string rhs)
  end

(* --- init_env registration ---
   Assemble the env_node shadow for init_env by walking the pre-built
   init_env_15 tree via rebuild_node.  Each init_env_N_wf is fetched
   from ml_progTheory via the naming convention — no re-derivation. *)
fun register_init_env () =
    let val init_env_const =
            prim_mk_const {Name = "init_env", Thy = "ml_prog"}
        val root_const =
            prim_mk_const {Name = "init_env_15", Thy = "ml_prog"}
        val node = rebuild_node root_const
    in env_tree_register init_env_const node
         ml_progTheory.nsLookup_all_init_env end

(* Lazy: register_init_env runs on first demand (inside the user's
   current theory) rather than at module load time, so the fresh
   env_tree_N constants end up in a theory the user actually keeps. *)
val init_env_registered = ref false
val () = ensure_init_env_hook :=
           (fn () => if !init_env_registered then ()
                     else (register_init_env ();
                           init_env_registered := true))

(* --- tree-backed lookup conv ---
   Handles `nsLookup_Short env.v k` / `nsLookup_Short env.c k` /
           `nsLookup_Mod1  env.v k` / `nsLookup_Mod1  env.c k`
   when env is registered in env_tree_map and k is a concrete strlit.
   Dispatches through nsLookup_pf_from_tree + the ML tree to produce
     |- <original_tm> = <SOME v | NONE | SOME ns_term>
   (concrete). Raises UNCHANGED otherwise. *)

val sem_env_v_tm = prim_mk_const
  {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.v"}
val sem_env_c_tm = prim_mk_const
  {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.c"}

fun nsLookup_tree_conv tm = let
  val t_d0 = Time.now ()
  val (f, args) = strip_comb tm
  val ismod = if same_const f nsLookup_Mod1_tm then true else
    if same_const f nsLookup_Short_tm then false else raise UNCHANGED
  val (ns_arg, key_arg) = case args of [a, b] => (a, b) | _ => raise UNCHANGED
  val (accessor, env_const) = dest_comb ns_arg handle _ => raise UNCHANGED
  val is_v = if same_const accessor sem_env_v_tm then true else
    if same_const accessor sem_env_c_tm then false else raise UNCHANGED
  val (node, equiv_thm) = case env_tree_lookup env_const of SOME p => p | NONE => raise UNCHANGED
  val key_str = mlstringSyntax.dest_mlstring key_arg handle _ => raise UNCHANGED
  val proj_thm = case (ismod, is_v) of
    (false, true)  => ml_progTheory.nsLookup_Short_v_via_all
  | (false, false) => ml_progTheory.nsLookup_Short_c_via_all
  | (true,  true)  => ml_progTheory.nsLookup_Mod1_v_via_all
  | (true,  false) => ml_progTheory.nsLookup_Mod1_c_via_all
  val t_body_0 = t_d0
  val t_d1 = Time.now ()
  val _ = prof_nsl_dispatch := !prof_nsl_dispatch + Time.toReal (Time.- (t_d1, t_d0))
  val spec = INST [v_env |-> env_const, vk |-> key_arg] proj_thm
  val t_d2 = Time.now ()
  val _ = prof_nsl_spec := !prof_nsl_spec + Time.toReal (Time.- (t_d2, t_d1))
  (* spec : nsLookup_<kind> env_const.<field> key_arg
          = (nsLookup_all env_const key_arg).<field> *)
  (* Avoid ONCE_REWRITE_RULE (which pattern-matches on equiv_thm).
      We know the position to substitute: it's RAND of RAND of spec.
      equiv_thm : nsLookup_all env_const = tree_lookup tree_tm.
      AP_THM equiv_thm key_arg : nsLookup_all env_const key_arg
                                  = tree_lookup tree_tm key_arg. *)
  val ap_thm = AP_THM equiv_thm key_arg
  val step1 = CONV_RULE (RAND_CONV (RAND_CONV (K ap_thm))) spec
  val t_d3 = Time.now ()
  val _ = prof_nsl_apthm := !prof_nsl_apthm + Time.toReal (Time.- (t_d3, t_d2))
  val lookup_thm = tree_lookup_thm node key_str
  val t_d3b = Time.now ()
  val _ = prof_nsl_tlcall := !prof_nsl_tlcall + Time.toReal (Time.- (t_d3b, t_d3))
  val step2 = CONV_RULE (RAND_CONV (RAND_CONV (K lookup_thm))) step1 handle _ => step1
  val t_d4 = Time.now ()
  val _ = prof_nsl_subst2 := !prof_nsl_subst2 + Time.toReal (Time.- (t_d4, t_d3b))
  val _ = prof_nsl_treethm := !prof_nsl_treethm + Time.toReal (Time.- (t_d4, t_d3))
  val t_body_1 = Time.now ()
  val _ = prof_nsl_tree_body := !prof_nsl_tree_body + Time.toReal (Time.- (t_body_1, t_body_0))
  val _ = prof_nsl_tree_body_n := !prof_nsl_tree_body_n + 1
  val t_e0 = Time.now ()
  val final = CONV_RULE (RAND_CONV EVAL) step2
  val t_e1 = Time.now ()
  val _ = prof_nsl_eval := !prof_nsl_eval + Time.toReal (Time.- (t_e1, t_e0))
  val _ = prof_nsl_eval_n := !prof_nsl_eval_n + 1
  in final end

(* The main nsLookup_conv.  Only the env_tree path is live — the legacy
   alist_treeLib fallback has been removed. *)
val nsLookup_conv_depth = ref 0
(* Fast path: nsLookup_tree_conv on a top-level nsLookup_<kind> env.<field> k
   produces a fully concrete result.  If it succeeds, no further REPEATC
   iteration is needed — skip the second pass entirely. *)
fun nsLookup_conv_raw tm =
  if !use_alist_conv then
    REPEATC (BETA_CONV ORELSEC FIRST_CONV
      (map REWR_CONV nsLookup_rewrs @ map (RATOR_CONV o REWR_CONV) nsLookup_rewrs
        @ map QCHANGED_CONV [nsLookup_arg1_conv nsLookup_conv, nsLookup_pf_conv])) tm
  else
    nsLookup_tree_conv tm handle UNCHANGED =>
      REPEATC (BETA_CONV ORELSEC FIRST_CONV
        (map REWR_CONV nsLookup_rewrs @ map (RATOR_CONV o REWR_CONV) nsLookup_rewrs
          @ map QCHANGED_CONV [nsLookup_arg1_conv nsLookup_conv, nsLookup_tree_conv])) tm
and nsLookup_conv tm = let
  val depth = !nsLookup_conv_depth
  val _ = nsLookup_conv_depth := depth + 1
  val t0 = Time.now ()
  val r  = nsLookup_conv_raw tm handle e => (nsLookup_conv_depth := depth; raise e)
  val t1 = Time.now ()
  val _  = nsLookup_conv_depth := depth
  val _  = if depth = 0 then (
    prof_nslookup_conv := !prof_nslookup_conv + Time.toReal (Time.- (t1, t0));
    prof_nslookup_conv_n := !prof_nslookup_conv_n + 1
  ) else ()
  in r end

val () = computeLib.add_convs (map (fn t => (t, 2, QCHANGED_CONV nsLookup_conv)) nsLookup_pf_tms)

fun get_nslookup_conv_calls () = !prof_nslookup_conv_n
fun get_nslookup_conv_time () = !prof_nslookup_conv
fun reset_nslookup_conv_counters () =
    (prof_nslookup_conv := 0.0; prof_nslookup_conv_n := 0)

(* helper functions *)

val reduce_conv =
  (* this could be a custom compset, but it's easier to get the
     necessary state updates directly from EVAL
     TODO: Might need more custom rewrites for env-refactor updates
  *)
  EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC
  EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL;

fun prove_assum_by_conv conv th = let
  val (x, _) = dest_imp (concl th)
  val lemma1 = conv x
  val lemma = CONV_RULE (RATOR_CONV $ RAND_CONV $ REWR_CONV lemma1) th
  in
    MP lemma TRUTH
    handle HOL_ERR _ => (
      print "Failed to convert:\n\n";
      print_term x;
      print "\n\nto T. It only reduced to:\n\n";
      print_term (lemma1 |> concl |> dest_eq |> snd);
      print "\n\n";
      failwith "prove_assum_by_conv: unable to reduce term to T")
  end;

(*
val eval_every_exp_one_con_check =
  SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_con_check_def,ML_code_env_def]
  THENC DEPTH_CONV nsLookup_conv
  THENC reduce_conv;
*)

fun is_const_str str = can prim_mk_const {Thy=current_theory(), Name=str};

fun find_name name = let
  val ns = map (#1 o dest_const) (constants (current_theory()))
  fun aux n = let
    val str = name ^ "_" ^ int_to_string n
    in if mem str ns then aux (n+1) else str end
  in aux 0 end

fun ok_char c =
  (#"0" <= c andalso c <= #"9") orelse
  (#"a" <= c andalso c <= #"z") orelse
  (#"A" <= c andalso c <= #"Z") orelse
  mem c [#"_",#"'"]

val ml_name = String.translate
  (fn c => if ok_char c then implode [c] else "c" ^ int_to_string (ord c))

fun define_abbrev for_eval name tm = let
  val name = ml_name name
  val name = (if is_const_str name then find_name name else name)
  val tm = if List.null (free_vars tm) then
    mk_eq (mk_var (name, type_of tm), tm)
  else let
    val vs = free_vars tm |> sort (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
    val vars = foldr mk_pair (last vs) (butlast vs)
    val n = mk_var (name, type_of vars --> type_of tm)
    in mk_eq (mk_comb (n, vars), tm) end
  val def_name = name ^ "_def"
  val def = Definition.new_definition(def_name,tm)
  val _ = if for_eval then computeLib.add_persistent_funs [def_name] else ()
  in def end

val ML_code_tm = prim_mk_const {Name = "ML_code", Thy = "ml_prog"}

fun dest_ML_code_block tm = let
  (* mn might or might not be a syntactic tuple,
      so make sure the list length is fixed. *)
  val (mn, elts) = pairSyntax.dest_pair tm
  in mn :: pairSyntax.strip_pair elts end

fun ML_code_blocks tm = let
  val (f, xs) = strip_comb tm
  val _ = (same_const f ML_code_tm andalso length xs = 3) orelse
    (print_term tm; failwith "ML_code_blocks: not ML_code")
  val (block_tms, _) = listSyntax.dest_list (hd (tl xs))
  in map dest_ML_code_block block_tms end

val let_conv = REWR_CONV LET_THM THENC (TRY_CONV BETA_CONV)

fun let_conv_ML_upd conv nm (th, code) = let
  val msg = "let_conv_ML_upd: " ^ nm ^ ": not let"
  val _ = is_let (concl th) orelse (print (msg ^ ":\n\n"); print_thm th; failwith msg)
  val th = CONV_RULE (RAND_CONV conv THENC let_conv) th
  in (th, code) end

fun cond_let_abbrev cond for_eval name conv op_nm th = let
  val msg = "cond_let_abbrev: " ^ op_nm ^ ": not let"
  val _ = is_let (concl th) orelse (print (msg ^ ":\n\n"); print_thm th; failwith msg)
  val th = CONV_RULE (RAND_CONV conv) th
  val (_, tm) = dest_let (concl th)
  val (f, xs) = strip_comb tm
  in
    if cond andalso is_const f andalso all is_var xs
    then (CONV_RULE let_conv th, [])
    else let
      val def = define_abbrev for_eval name tm |> SPEC_ALL
      in (CONV_RULE (RAND_CONV (REWR_CONV (GSYM def)) THENC let_conv) th, [def]) end
  end

fun auto_name sfx = current_theory () ^ "_" ^ sfx

fun let_st_abbrev conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
  val (th, abbrev_defs) = cond_let_abbrev true true (auto_name "st") conv op_nm th
  in (th, ML_code (abbrev_defs @ ss, envs, vs, ml_th)) end

fun let_env_abbrev conv op_nm st = let
    val le_t0 = Time.now ()
    val le_r = let_env_abbrev_body conv op_nm st
    val le_t1 = Time.now ()
    val _ = prof_let_env := !prof_let_env + Time.toReal (Time.- (le_t1, le_t0))
  in le_r end
and let_env_abbrev_body conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
    val _ = prof_let_env_n := !prof_let_env_n + 1
    (* Accumulate user-conv time locally for this call, then split
       cond_let_abbrev's wall time into conv vs other. *)
    val conv_local = ref 0.0
    val user_conv_prof = fn tm => let
      val t0 = Time.now ()
      val r  = conv tm
      val t1 = Time.now ()
      val dt = Time.toReal (Time.- (t1, t0))
      val _  = conv_local := !conv_local + dt
      val _  = prof_user_conv := !prof_user_conv + dt
      in r end
    val t_cl0 = Time.now ()
    val (th, abbrev_defs) = cond_let_abbrev true false
        (auto_name "env") user_conv_prof op_nm th
    val t_cl1 = Time.now ()
    val cl_total = Time.toReal (Time.- (t_cl1, t_cl0))
    val _ = prof_cond_let_other := !prof_cond_let_other + cl_total - !conv_local
    val t_td0 = Time.now ()
    val _ = List.app
      (fn d =>
        ignore (derive_nsLookup_tree d)
        handle e => (
          TextIO.output (TextIO.stdErr,
            "derive_nsLookup_tree failed on:\n  "
            ^ Parse.thm_to_string d ^ "\n  error: "
            ^ General.exnMessage e ^ "\n");
          raise e))
      abbrev_defs
    (* Also save legacy alist <env>_pfun_eqs theorems so the alist
       fallback (toggled via use_alist_conv) can find them. Time it
       separately so it can be subtracted from comparative benchmarks. *)
    val t_pf0 = Time.now ()
    val _ = List.app (fn d => ignore (derive_nsLookup_thms d) handle _ => ())
              abbrev_defs
    val t_pf1 = Time.now ()
    val _ = prof_pfun_eqs_save :=
              !prof_pfun_eqs_save + Time.toReal (Time.- (t_pf1, t_pf0))
    val _ = prof_pfun_eqs_save_n :=
              !prof_pfun_eqs_save_n + length abbrev_defs
    val t_td1 = Time.now ()
    val _ = prof_tree_derive := !prof_tree_derive + Time.toReal (Time.- (t_td1, t_td0))
  in (th, ML_code (ss, abbrev_defs @ envs, vs, ml_th)) end

(* Legacy alist-fallback save: <env>_pfun_eqs theorem, used by the orig
   nsLookup_pf_conv path.  Run alongside derive_nsLookup_tree. *)
and derive_nsLookup_thms def = let
    val env_const = def |> concl |> dest_eq |> fst
    val xs = nsLookup_eq_format |> SPEC env_const |> concl
                |> find_terms is_eq |> map (fst o dest_eq)
    val rewrs = [def, nsLookup_write_eqs, nsLookup_write_cons_eqs,
                  nsLookup_merge_env_eqs, nsLookup_write_mod_eqs,
                  nsLookup_empty_eqs]
    val pfun_eqs = LIST_CONJ (map (REWRITE_CONV rewrs) xs)
    val thm_name = "nsLookup_" ^ fst (dest_const env_const) ^ "_pfun_eqs"
  in allowing_rebind save_thm (thm_name, pfun_eqs) end

fun let_v_abbrev nm conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
  val (th, abbrev_defs) = cond_let_abbrev false false nm conv op_nm th
  in (th, ML_code (ss, envs, abbrev_defs @ vs, ml_th)) end

(*
val tm = ``!n. n = 5 ==> n < 8``
*)
fun unwind_forall_conv tm = let
  val (v,_) = dest_forall tm
  in
    (QUANT_CONV (RAND_CONV (UNBETA_CONV v))
     THENC (REWR_CONV UNWIND_FORALL_THM1 ORELSEC
            REWR_CONV UNWIND_FORALL_THM2)
     THENC BETA_CONV) tm
  end

fun forall_nsLookup_upd _ (th,x) =
  (CONV_RULE
    (QUANT_CONV
      ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) (nsLookup_conv THENC EVAL)
       THENC (RATOR_CONV o RAND_CONV) (REWR_CONV SOME_11))
     THENC unwind_forall_conv) th,
   x) handle HOL_ERR _ =>
  failwith "forall_nsLookup_upd: nsLookup failed to produce SOME"

fun solve_ml_imp f nm (th, ML_code code) = let
  val msg = "solve_ml_imp: " ^ nm ^ ": not imp"
  val _ = is_imp (concl th) orelse (print (msg ^ "\n\n"); print_term (concl th); failwith msg)
  in (f th, ML_code code) end
fun solve_ml_imp_mp lemma = solve_ml_imp (fn th => MATCH_MP th lemma)
fun solve_ml_imp_conv conv = solve_ml_imp (prove_assum_by_conv conv)

(*
val (ML_code (ss,envs,vs,th)) = (ML_code (ss,envs,v_def :: vs,th))
*)

fun ML_code_upd nm mp_thm adjs (ML_code code) = let
  (* when updating an ML_code thm by forward reasoning, first
     abstract over all the program components (which can be large
     snoc-lists or cons-lists) and process on the smaller abstracted
     theorem, connecting to the original ML_code thm with a single
     final MATCH_MP step. *)
  val orig_th = #4 code
  val blocks = ML_code_blocks (concl orig_th)
  val (f, xs) = strip_comb (concl orig_th)
  val abs_blocks = mapi (fn i => pairSyntax.list_mk_pair o mapi (fn j =>
    if j = 2 then (fn _ => mk_var ("prog_var_" ^ Int.toString i, decs_ty)) else I)) blocks
  val abs_blocks_tm = listSyntax.mk_list (abs_blocks, type_of (hd abs_blocks))
  val abs_concl = list_mk_comb (f, mapi (fn i => if i = 1 then K abs_blocks_tm else I) xs)
  val preproc_th = MATCH_MP mp_thm (ASSUME abs_concl)
  val (proc_th, ML_code (ss, envs, vs, _)) =
    foldl (fn (adj, x) => adj nm x) (preproc_th, ML_code code) adjs
  val _ = same_const ML_code_tm (fst (strip_comb (concl proc_th))) orelse
    failwith ("ML_code_upd: " ^ nm ^ ": unfinished: " ^ Parse.thm_to_string proc_th)
  val th = MATCH_MP (DISCH abs_concl proc_th) orig_th
  in ML_code (ss, envs, vs, th) end

(* --- *)

val unknown_loc = locationTheory.unknown_loc_def |> concl |> dest_eq |> fst

val init_state = ML_code ([SPEC_ALL init_state_def], [init_env_def], [], ML_code_NIL)

fun mk_comment (s1, s2) =
  pairSyntax.mk_pair (mlstringSyntax.mk_mlstring s1, mlstringSyntax.mk_mlstring s2)

fun dest_comment t = let
  val (s1, s2) = pairSyntax.dest_pair t
  in (mlstringSyntax.dest_mlstring s1, mlstringSyntax.dest_mlstring s2) end

fun open_block nm comment =
  ML_code_upd nm (SPEC comment ML_code_new_block) [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def])]

fun open_module mn_str = open_block "open_module" (mk_comment ("Module", mn_str))

fun close_module _ = ML_code_upd "close_module" ML_code_close_module [let_env_abbrev ALL_CONV]

val open_local_block = open_block "open_local_block" (mk_comment ("Local", "local"))

val open_local_in_block = open_block "open_local_in_block" (mk_comment ("Local", "in"))

val close_local_block =
  ML_code_upd "close_local_block" ML_code_close_local [let_env_abbrev ALL_CONV]

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype loc tds_tm = ML_code_upd "add_Dtype"
  (SPECL [tds_tm, loc] ML_code_Dtype)
  [solve_ml_imp_conv EVAL, let_conv_ML_upd EVAL,
    let_st_abbrev reduce_conv,
    let_env_abbrev (SIMP_CONV std_ss [
      write_tdefs_def, MAP, FLAT, FOLDR, REVERSE_DEF, write_conses_def, LENGTH,
      semanticPrimitivesTheory.build_constrs_def, APPEND, namespaceTheory.mk_id_def])]

(*
val loc = unknown_loc
val n_tm = ``"bar"``
val l_tm = ``[]:ast_t list``
*)

fun add_Dexn loc n_tm l_tm = ML_code_upd "add_Dexn"
  (SPECL [n_tm, l_tm, loc] ML_code_Dexn)
  [let_conv_ML_upd EVAL, let_st_abbrev reduce_conv,
    let_env_abbrev (SIMP_CONV std_ss [
      MAP, FLAT, FOLDR, REVERSE_DEF, APPEND, namespaceTheory.mk_id_def])]

fun add_Dtabbrev loc l1_tm l2_tm l3_tm = ML_code_upd "add_Dtabbrev"
  (SPECL [l1_tm,l2_tm,l3_tm,loc] ML_code_Dtabbrev) []

fun add_Dlet eval_thm var_str = let
  val (_, eval_thm_xs) = strip_comb (concl eval_thm)
  val mp_thm = ML_code_Dlet_var |> SPECL (tl eval_thm_xs
    @ [mlstringSyntax.mk_mlstring var_str,unknown_loc])
  in
    ML_code_upd "add_Dlet" mp_thm [
      solve_ml_imp_mp eval_thm,
      solve_ml_imp_conv (SIMP_CONV bool_ss [] THENC SIMP_CONV bool_ss [ML_code_env_def]),
      let_env_abbrev ALL_CONV, let_st_abbrev reduce_conv]
  end

fun add_Dlet_lit loc n l = let
  val mp_thm = SPECL [loc,n,l] ML_code_Dlet_var_lit
  in ML_code_upd "add_Dlet_lit" mp_thm [let_env_abbrev ALL_CONV, let_env_abbrev ALL_CONV] end

fun add_Denv eval_thm var_str = let
  val (_, eval_thm_xs) = strip_comb (concl eval_thm)
  val mp_thm = ML_code_Denv |> SPECL (mlstringSyntax.mk_mlstring var_str :: tl eval_thm_xs)
  in
    ML_code_upd "add_Denv" mp_thm [
      solve_ml_imp_mp eval_thm,
      solve_ml_imp_conv (SIMP_CONV bool_ss [] THENC SIMP_CONV bool_ss [ML_code_env_def]),
      let_env_abbrev ALL_CONV, let_st_abbrev reduce_conv]
  end

(*
val (ML_code (ss,envs,vs,th)) = s
val (n,v,exp) = (v_tm,w,body)
*)

fun add_Dlet_Fun loc n v exp v_name = ML_code_upd "add_Dlet_Fun"
  (SPECL [n, v, exp, loc] ML_code_Dlet_Fun)
  [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
    let_v_abbrev v_name ALL_CONV, let_env_abbrev ALL_CONV]

fun add_Dlet_Var_Var loc n var_name = ML_code_upd "add_Dlet_Var_Var"
  (SPECL [n, var_name, loc] ML_code_Dlet_Var_Var)
  [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
    forall_nsLookup_upd, let_env_abbrev ALL_CONV]

fun add_Dlet_Var_Ref_Var loc n var_name v_name = ML_code_upd "add_Dlet_Var_Ref_Var"
  (SPECL [n, var_name, loc] ML_code_Dlet_Var_Ref_Var)
  [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]), forall_nsLookup_upd, let_conv_ML_upd EVAL,
    let_v_abbrev v_name ALL_CONV, let_env_abbrev ALL_CONV, let_st_abbrev reduce_conv]

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> concl |> find_term (fn tm =>
    total (fst o dest_const o fst o strip_comb o snd o dest_eq) tm = SOME "Recclosure")
  |> dest_eq |> snd

fun add_Dletrec loc funs v_names = let
  fun proc nm (th, (ML_code (ss,envs,vs,mlth))) = let
    val th = CONV_RULE (RAND_CONV (SIMP_CONV std_ss [
      write_rec_def, FOLDR, semanticPrimitivesTheory.build_rec_env_def])) th
    val _ = is_let (concl th) orelse failwith "add_Dletrec: not let"
    val (_, tm) = dest_let (concl th)
    val tms = rev (find_terms (can (match_term Recclosure_pat)) tm)
    val xs = zip v_names tms
    val v_defs = map (fn (x,y) => define_abbrev false x y) xs
    val th = CONV_RULE (RAND_CONV (REWRITE_CONV (map GSYM v_defs))) th
    in let_env_abbrev ALL_CONV nm (th, ML_code (ss,envs,v_defs @ vs,mlth)) end
  in
    ML_code_upd "add_Dletrec" (SPECL [funs, loc] ML_code_Dletrec)
      [solve_ml_imp_conv EVAL, let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]), proc]
  end

fun get_block_names (ML_code (ss,envs,vs,th)) = ML_code_blocks (concl th) |> map (dest_comment o hd)

fun get_open_modules code = get_block_names code
  |> filter (fn ("Module", _) => true | _ => false)
  |> map snd |> rev

fun get_mod_prefix code = case get_open_modules code of [] => "" | (m :: _) => m ^ "_"

fun close_local_blocks code = case get_block_names code of
    ("Local", "in") :: _ => close_local_blocks (close_local_block code)
  | ("Local", "local") :: _ => open_local_in_block code |> close_local_block |> close_local_blocks
  | _ => code


(*
val dec_tm = dec1_tm
*)
fun add_dec dec_tm pick_name s =
  if is_Dexn dec_tm then let
    val (loc,x1,x2) = dest_Dexn dec_tm
    in add_Dexn loc x1 x2 s end
  else if is_Dtype dec_tm then let
    val (loc,x1) = dest_Dtype dec_tm
    in add_Dtype loc x1 s end
  else if is_Dtabbrev dec_tm then let
    val (loc,x1,x2,x3) = dest_Dtabbrev dec_tm
    in add_Dtabbrev loc x1 x2 x3 s end
  else if is_Dletrec dec_tm then let
    val (loc,x1) = dest_Dletrec dec_tm
    val prefix = get_mod_prefix s
    fun f str = prefix ^ pick_name str ^ "_v"
    val xs = listSyntax.dest_list x1 |> fst
               |> map (f o mlstringSyntax.dest_mlstring o rand o rator)
    in add_Dletrec loc x1 xs s end
  else if is_Dlet dec_tm
          andalso is_Fun (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val (w,body) = dest_Fun f
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (mlstringSyntax.dest_mlstring v_tm) ^ "_v"
    in add_Dlet_Fun loc v_tm w body v_name s end
  else if is_Dlet dec_tm
          andalso is_Lit (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,lit) = dest_Dlet dec_tm
    val l = dest_Lit lit
    val n = dest_Pvar p
    in add_Dlet_lit loc n l s end
  else if is_Dlet dec_tm
          andalso is_Var (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val var_name = dest_Var f
    in add_Dlet_Var_Var loc v_tm var_name s end
  else if is_Dlet dec_tm
          andalso is_App (rand dec_tm)
          andalso aconv Opref (rand (rator (rand dec_tm)))
          andalso length (fst (listSyntax.dest_list (rand (rand dec_tm)))) = 1
          andalso is_Var (rand (rator (rand (rand dec_tm))))
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val n = dest_Pvar p
    val (_,args) = dest_App f
    val var_name = dest_Var (listSyntax.dest_list args |> fst |> hd)
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (mlstringSyntax.dest_mlstring n) ^ "_v"
    in add_Dlet_Var_Ref_Var loc n var_name v_name s end
  else if is_Dmod dec_tm then let
    val (name,(*spec,*)decs) = dest_Dmod dec_tm
    val ds = fst (listSyntax.dest_list decs)
    val name_str = mlstringSyntax.dest_mlstring name
    val s = open_module name_str s handle HOL_ERR _ =>
            failwith ("add_top: failed to open module " ^ name_str)
    fun each [] s = s
      | each (d::ds) s = let
           val s = add_dec d pick_name s handle HOL_ERR e =>
                   failwith ("add_top: in module " ^ name_str ^
                             "failed to add " ^ term_to_string d ^ "\n " ^
                             message_of e)
           in each ds s end
    val s = each ds s
    val spec = (* SOME (optionSyntax.dest_some spec)
                  handle HOL_ERR _ => *) NONE
    val s = close_module spec s handle HOL_ERR e =>
            failwith ("add_top: failed to close module " ^ name_str ^ "\n " ^
                             message_of e)
    in s end
  else failwith("add_dec does not support this shape: " ^ term_to_string dec_tm);

fun remove_snocs (ML_code (ss,envs,vs,th)) = let
  val th = th
    |> PURE_REWRITE_RULE [listTheory.SNOC_APPEND]
    |> PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC]
    |> PURE_REWRITE_RULE [listTheory.APPEND]
  in (ML_code (ss, envs, vs, th)) end

fun get_thm (ML_code (ss,envs,vs,th)) = th
fun get_v_defs (ML_code (ss,envs,vs,th)) = vs

fun get_prog (ML_code (ss,envs,vs,th)) =
  case ML_code_blocks (concl th) of
    [comm :: st :: prog :: _] => prog
  | _ => failwith ("get_prog: couldn't get toplevel declarations")
fun get_Decls_thm code = let
  val _ = get_prog code
  in MATCH_MP ML_code_Decls (get_thm code) end

val merge_env_tm = prim_mk_const {Name = "merge_env", Thy = "ml_prog"}
val ML_code_env_tm = prim_mk_const {Name = "ML_code_env", Thy = "ml_prog"}

fun get_env s = let
  val th = get_thm s
  val bls = ML_code_blocks (concl th)
  fun mk [] = hd (snd (strip_comb (concl th)))
    | mk (bl :: bls) = list_mk_icomb (merge_env_tm, [List.last bl, mk bls])
  in mk bls end

fun get_state s = get_thm s |> concl |> rand

fun mk_acc nm rec_tm = let
  val fields = TypeBase.fields_of (type_of rec_tm)
  val field = assoc nm fields
  in mk_icomb (#accessor field, rec_tm) end

fun get_next_type_stamp s =
  get_state s |> mk_acc "next_type_stamp" |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term

fun get_next_exn_stamp s =
  get_state s |> mk_acc "next_exn_stamp" |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term

fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x, y) => add_dec x pick_name y) s ts) end

(* Snapshot env_tree_map for pack/unpack.  We store (env_const, equiv_thm)
   pairs; the tree's root constant is extractable from the RHS of equiv_thm,
   and rebuild_node rehydrates the env_node from its saved Definition chain.
   Entries keyed by ml_prog's init_env are skipped — register_init_env
   rebuilds them lazily via ensure_init_env_hook. *)
val init_env_const = prim_mk_const {Name = "init_env", Thy = "ml_prog"}
fun snapshot_env_tree_map () =
  Redblackmap.listItems (!env_tree_map)
  |> filter (fn (k, _) => not (same_const k init_env_const))
  |> map (fn (k, (_, equiv)) => (k, equiv))

fun restore_env_tree_map entries =
  app (fn (env_const, equiv_thm) =>
    case Redblackmap.peek (!env_tree_map, env_const) of
      SOME _ => ()  (* already present — keep existing *)
    | NONE => let
      val tree_tm = rand (rhs (concl equiv_thm))
      val node = rebuild_node tree_tm
      in env_tree_register env_const node equiv_thm end
      handle e => TextIO.output (TextIO.stdErr,
        "restore_env_tree_map: skipping " ^ Parse.term_to_string env_const ^
        " (" ^ General.exnMessage e ^ ")\n"))
    entries

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) = let
  val pack_entry = pack_pair pack_term pack_thm
  val snapshot = snapshot_env_tree_map ()
  in pack_5tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (pack_list pack_entry)
    (ss, envs, vs, th, snapshot) end

fun unpack_ml_prog_state t = let
  val unpack_entry = unpack_pair unpack_term unpack_thm
  val (ss, envs, vs, th, snapshot) =
    unpack_5tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
      (unpack_list unpack_thm) unpack_thm (unpack_list unpack_entry) t
    handle HOL_ERR _ => let
      (* Backward compat: old pickles are 4-tuples without env_tree
          snapshot. *)
      val (ss, envs, vs, th) =
        unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
          (unpack_list unpack_thm) unpack_thm t
      in (ss, envs, vs, th, []) end
  val _ = restore_env_tree_map snapshot
  in ML_code (ss, envs, vs, th) end

fun set_eval_state es (ML_code (ss, envs, vs, th)) = let
  val th1 = MATCH_MP ML_code_set_eval_state th
  val th2 = th1 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL)
  val th3 = MP th2 TRUTH handle HOL_ERR _ =>
            failwith "set_eval_state: unable to prove that eval_state was NONE"
  val th4 = SPEC es th3
  in ML_code (ss, envs, vs, th4) end

fun clean_state (ML_code (ss, envs, vs, th)) = let
  fun FIRST_CONJUNCT th = CONJUNCTS th |> hd handle HOL_ERR _ => th
  fun delete_def def = let
    val {Name, Thy, Ty = _} =
      def |> SPEC_ALL |> FIRST_CONJUNCT |> SPEC_ALL |> concl
          |> dest_eq |> fst |> repeat rator |> dest_thy_const
    in if Thy = Theory.current_theory () then Theory.delete_binding (Name ^ "_def") else () end
  fun split x = ([hd x], tl x) handle Empty => (x,x)
  fun dd ls = let val (ls, ds) = split ls in app delete_def ds; ls end
  val () = app delete_def vs
  in (ML_code (dd ss, dd envs, [], th)) end

fun pick_name "<" = "lt"
  | pick_name ">" = "gt"
  | pick_name "<=" = "le"
  | pick_name ">=" = "ge"
  | pick_name "=" = "eq"
  | pick_name "<>" = "neq"
  | pick_name "~" = "uminus"
  | pick_name "+" = "plus"
  | pick_name "-" = "minus"
  | pick_name "*" = "times"
  | pick_name "/" = "div"
  | pick_name "!" = "deref"
  | pick_name ":=" = "assign"
  | pick_name "@" = "append"
  | pick_name "^" = "strcat"
  | pick_name "<<" = "lsl"
  | pick_name ">>" = "lsr"
  | pick_name "~>>" = "asr"
  | pick_name str = str (* name is fine *)

(*

val s = init_state
val dec1_tm = ``Dlet (ARB 1) (Pvar "f") (Lit (IntLit 5))``
val dec2_tm = ``Dlet (ARB 2) (Pvar "g") (Fun "x" (Var (Short "x")))``
val dec3_tm = ``Dletrec (ARB 3) [("foo","n",Con (SOME (Short "::"))
                  [Var (Short "n");Var (Short "n")])]``
val prog_tm = ``[^dec1_tm; ^dec2_tm; ^dec3_tm]``

val s = (add_prog prog_tm pick_name init_state)

val th = get_env s

*)

end
