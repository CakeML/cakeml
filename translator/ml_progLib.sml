(*
  Functions for constructing a CakeML program (a list of declarations) together
  with the semantic environment resulting from evaluation of the program.
*)
structure ml_progLib :> ml_progLib =
struct

open preamble ml_progTheory astSyntax packLib comparisonTheory
local open mlstringSyntax in end

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

val mlstring_lt_tm = prim_mk_const {Thy = "mlstring", Name = "mlstring_lt"}
val sem_env_v_tm = prim_mk_const {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.v"}
val sem_env_c_tm = prim_mk_const {Thy = "semanticPrimitives", Name = "recordtype.sem_env.seldef.c"}
val nsLookup_Short_tm = prim_mk_const {Thy = "ml_prog", Name = "nsLookup_Short"}
val nsLookup_Mod1_tm  = prim_mk_const {Thy = "ml_prog", Name = "nsLookup_Mod1"}
val nsLookup_all_const= prim_mk_const {Thy = "ml_prog", Name = "nsLookup_all"}
val EnvLeaf_tm        = prim_mk_const {Thy = "ml_prog", Name = "EnvLeaf"}
val EnvBranch_tm      = prim_mk_const {Thy = "ml_prog", Name = "EnvBranch"}
val empty_env_tm      = prim_mk_const {Thy = "ml_prog", Name = "empty_env"}
val init_env_const    = prim_mk_const {Thy = "ml_prog", Name = "init_env"}
val merge_env_tm      = prim_mk_const {Thy = "ml_prog", Name = "merge_env"}
val empty_entry_const = prim_mk_const {Thy = "ml_prog", Name = "empty_entry"}
val combine_entries_tm= prim_mk_const {Thy = "ml_prog", Name = "combine_entries"}
val tree_lookup_tm    = prim_mk_const {Thy = "ml_prog", Name = "tree_lookup"}
val env_entry_sv_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sv_fupd"}
val env_entry_sc_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.sc_fupd"}
val env_entry_mv_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mv_fupd"}
val env_entry_mc_fupd = prim_mk_const {Thy = "ml_prog", Name = "recordtype.env_entry.seldef.mc_fupd"}
val ML_code_tm        = prim_mk_const {Thy = "ml_prog", Name = "ML_code"}

val mlstring_ty  = mk_thy_type {Thy = "mlstring", Tyop = "mlstring", Args = []}
val env_tree_ty  = mk_thy_type {Thy = "ml_prog", Tyop = "env_tree", Args = []}
val env_entry_ty = mk_thy_type {Thy = "ml_prog", Tyop = "env_entry", Args = []}
val env_ty       = type_of empty_env_tm

(* The main nsLookup_conv and its computeLib registration are defined near
   the bottom of this file (after nsLookup_tree_conv, which it dispatches to). *)

val () = computeLib.the_compset := computeLib.add_thms [nsLookup_eq] (!computeLib.the_compset)

(* --- balanced env tree (env_tree) infrastructure ---
   For each env constant the translator produces, we maintain an env_tree
   with a saved equivalence  |- nsLookup_all env = tree_lookup <tree>.
   Each node carries an ML-side shadow (env_node) remembering the HOL
   tree term, its WF theorem (with exact key bounds), and child links. *)
fun mk_etv n = mk_var (n, env_tree_ty)
fun mk_msv n = mk_var (n, mlstring_ty)
fun mk_enev n = mk_var (n, env_entry_ty)

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
val v_t   = mk_etv "t"
val vtL1  = mk_etv "tL1"
val vtL2  = mk_etv "tL2"
val vX    = mk_etv "X"
val vY    = mk_etv "Y"

val vk    = mk_msv "k"
val vk1   = mk_msv "k1"
val vk2   = mk_msv "k2"
val vkl   = mk_msv "kl"
val vkr   = mk_msv "kr"
val vn    = mk_msv "n"
val vkL   = mk_msv "kL"
val vkR   = mk_msv "kR"
val vkX1  = mk_msv "kX1"
val vkX2  = mk_msv "kX2"
val vkB1  = mk_msv "kB1"
val vkB2  = mk_msv "kB2"
val vkC1  = mk_msv "kC1"
val vkC2  = mk_msv "kC2"
val vkY1  = mk_msv "kY1"
val vkY2  = mk_msv "kY2"

val v_e   = mk_enev "e"
val v_e1  = mk_enev "e1"
val v_e2  = mk_enev "e2"

val v_env = mk_var ("env", env_ty)

(* Convenience: apply a prepped skeleton by instantiating variables and
   discharging hypotheses with provided theorems (matched by aconv on
   conclusion).  Order of provided theorems is immaterial. *)
fun apply_cps skel subst = foldl (fn (p, th) => PROVE_HYP p th) (INST subst skel)
val prep_cps = apply_cps o UNDISCH_ALL o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO] o SPEC_ALL

(* Prepped skeletons for the hot CPS lemmas. *)
val skel_env_wf_branch_intro    = prep_cps env_wf_branch_intro_cps
val skel_env_wf_branch_split_lt = prep_cps env_wf_branch_split_lt_cps
val skel_env_wf_leaf            = prep_cps env_wf_leaf_cps
val skel_coalesce_leaves        = prep_cps tree_lookup_coalesce_leaves_cps
val skel_join_left              = prep_cps tree_lookup_join_left_cps
val skel_join_right             = prep_cps tree_lookup_join_right_cps
val skel_commute_left           = prep_cps tree_lookup_commute_left_cps
val skel_swap                   = prep_cps tree_lookup_swap_cps
val skel_leaf_mem_leaf          = prep_cps env_leaf_mem_leaf_cps
val skel_leaf_mem_branch_l      = prep_cps env_leaf_mem_branch_l_cps
val skel_leaf_mem_branch_r      = prep_cps env_leaf_mem_branch_r_cps
val skel_tree_lookup_hit        = prep_cps tree_lookup_hit
val skel_tree_lookup_miss       = prep_cps tree_lookup_miss
val skel_tree_miss_gap          = prep_cps tree_miss_gap_cps
val skel_tree_miss_branch_l     = prep_cps tree_miss_branch_l_cps
val skel_tree_miss_branch_r     = prep_cps tree_miss_branch_r_cps
val skel_write_tree             = prep_cps nsLookup_all_write_tree_cps
val skel_write_cons_tree        = prep_cps nsLookup_all_write_cons_tree_cps
val skel_write_mod_tree         = prep_cps nsLookup_all_write_mod_tree_cps

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

val branch_cons_cache = ref (
  Redblackmap.mkDict (pair_compare (Term.compare, Term.compare)):
  (term * term, term * thm * thm) Redblackmap.dict)

(* Define a fresh tree-node constant whose rhs is tree_tm.
   Returns (const_term, def_thm) where def_thm : |- <const> = <tree_tm>. *)
fun define_fresh_tree tree_tm = Profile.profile "define_fresh_tree" (fn () => let
  val nm = next_tree_const_name ()
  val lhs = mk_var (nm, env_tree_ty)
  val def = Definition.new_definition (nm ^ "_def", mk_eq (lhs, tree_tm))
  val const_tm = def |> concl |> dest_eq |> fst
  (* Inner tree constants exist for fast in-script ops, but their _def/_wf
     bindings are not persisted: cross-script callers walk the inlined rhs
     of the named env's tree_def instead. *)
  val _ = Theory.delete_binding (nm ^ "_def")
  in (const_tm, def) end) ()

(* Naming convention. For env constant named "foo" we save:
     foo_tree_equiv : nsLookup_all foo = tree_lookup <tree>
     foo_tree_wf    : env_wf <tree> k1 k2 *)
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

local
  val lt_cache = ref (Redblackmap.mkDict (pair_compare (Term.compare, Term.compare)):
    ((term * term), thm) Redblackmap.dict)
in
  (* mk_lt_thm_via: same cache as mk_lt_thm, but on miss delegate to the
    provided thunk instead of EVAL.  Lets callers with a cheap alternative
    (e.g. apply_cps of env_wf_branch_split_lt_cps on a parent WF) supply a
    miss-path that's faster than `EQT_ELIM (EVAL ...)`. *)
  fun mk_lt_thm_via thunk a b =
    case Redblackmap.peek (!lt_cache, (a, b)) of
      SOME th => th
    | NONE => case thunk () of th =>
      (lt_cache := Redblackmap.insert (!lt_cache, (a, b), th); th)
end

fun mk_lt_thm a b =
  mk_lt_thm_via (fn () => EQT_ELIM (EVAL (list_mk_icomb (mlstring_lt_tm, [a, b])))) a b

(* Naming convention: whenever we create a fresh env_tree_<N> (or
   init_env_<N>) constant, we also save_thm its env_wf proof under
   <name>_wf in the same theory.  rebuild_node then just DB.fetch'es
   the saved wf instead of re-deriving via env_wf_*_cps. *)
(* DEBUG: bypass save to test export-cost hypothesis *)
fun save_tree_wf _ _ = ()

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
(* mk_branch_node_gen_with: like mk_branch_node_gen but the caller supplies
   a thunk that produces the `mlstring_lt kl kr` theorem.  The default in
   `mk_branch_node_gen` is `fn () => mk_lt_thm kl_tm kr_tm`.  Callers that
   hold a parent WF already implying the needed lt can pass a thunk that
   extracts it — avoiding both the Redblackmap lookup in mk_lt_thm's cache
   and (on real misses) the EVAL. *)
fun mk_branch_node_gen_with make_const lt_thunk left right = let
  val (k1_tm, kl_tm) = bounds_of left
  val (kr_tm, k2_tm) = bounds_of right
  val (k1_str, _)    = key_strs_of left
  val (_, k2_str)    = key_strs_of right
  val left_tm        = tree_tm_of left
  val right_tm       = tree_tm_of right
  val compound_tm = mk_comb (mk_comb (EnvBranch_tm, left_tm), right_tm)
  (* Try the hash-cons cache only when we'd materialize a constant
      AND both children are constants (the cache key is constant-only). *)
  val cached =
    if make_const andalso is_const left_tm andalso is_const right_tm
    then Redblackmap.peek (!branch_cons_cache, (left_tm, right_tm))
    else NONE
  val (tree_tm, def_thm, wf_thm) = case cached of SOME c => c | NONE => let
    val lt_thm = lt_thunk ()
    val (tree_tm, def_thm) =
      if make_const then define_fresh_tree compound_tm
      else (compound_tm, REFL compound_tm)
    val wf_thm = skel_env_wf_branch_intro
      [vtT |-> tree_tm, v_l |-> left_tm, v_r |-> right_tm,
        vk1 |-> k1_tm, vkl |-> kl_tm, vkr |-> kr_tm, vk2 |-> k2_tm]
      [def_thm, wf_thm_of left, wf_thm_of right, lt_thm]
    val _ = if make_const then save_tree_wf tree_tm wf_thm else ()
    val _ = if make_const andalso is_const left_tm andalso is_const right_tm then
      branch_cons_cache := Redblackmap.insert (!branch_cons_cache,
        (left_tm, right_tm), (tree_tm, def_thm, wf_thm))
    else ()
    in (tree_tm, def_thm, wf_thm) end
  (* AVL invariant is checked at higher levels; loose intermediates from
     rebalance_join_with's ROTATE path may violate it transiently. *)
  val result = EBranch {
    left = left, right = right, k1_tm = k1_tm, k2_tm = k2_tm,
    k1_str = k1_str, k2_str = k2_str, tree_tm = tree_tm, def_thm = def_thm,
    depth = 1 + Int.max (depth_of left, depth_of right), wf_thm = wf_thm }
  in result end

val mk_branch_node_raw_with = mk_branch_node_gen_with true
val mk_branch_node_compound_with = mk_branch_node_gen_with false

(* Build an lt thunk that derives `mlstring_lt kl kr` from an ancestor
   branch WF, via env_wf_branch_split_lt_cps.  `parent` must be an
   EBranch env_node whose immediate children (in the env_node sense) are
   `l` and `r` — that is, parent_wf witnesses env_wf parent_tm k1 k2 and
   parent_def witnesses parent_tm = EnvBranch l.tree_tm r.tree_tm.  The
   thunk routes through mk_lt_thm_via so cache hits remain cheap. *)
fun lt_from_parent_wf { parent_tm, parent_def, parent_wf, l, r } () = let
  val (k1_tm, kl_tm) = bounds_of l
  val (kr_tm, k2_tm) = bounds_of r
  fun fallback () = skel_env_wf_branch_split_lt
    [vtT |-> parent_tm, v_l |-> tree_tm_of l, v_r |-> tree_tm_of r,
      vk1 |-> k1_tm, vk2 |-> k2_tm, vkl |-> kl_tm, vkr |-> kr_tm]
    [parent_def, parent_wf, wf_thm_of l, wf_thm_of r]
  in mk_lt_thm_via fallback kl_tm kr_tm end

(* Materialize: walk an env_node and replace every compound (REFL-defined)
   EBranch with one backed by a fresh definition. *)
fun materialize_node (node as ELeaf {tree_tm, ...}) = (node, REFL tree_tm)
  | materialize_node (node as EBranch {left, right, tree_tm,
      def_thm = node_def, wf_thm = node_wf, ...}) =
    if is_const tree_tm then (node, REFL tree_tm) else let
      val (L', thm_L) = materialize_node left
      val (R', thm_R) = materialize_node right
      val mk_comb_thm = MK_COMB (AP_TERM EnvBranch_tm thm_L, thm_R)
      val lt_thunk = lt_from_parent_wf
        {parent_tm = tree_tm, parent_def = node_def, parent_wf = node_wf, l = left, r = right}
      val new_node = mk_branch_node_raw_with lt_thunk L' R'
      val combined = TRANS mk_comb_thm (SYM (def_thm_of new_node))
      in (new_node, combined) end

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
          val mem_thm = skel_leaf_mem_branch_l
            [vtT |-> tree_tm, v_l |-> tree_tm_of left, v_r |-> tree_tm_of right,
              vk |-> key_tm, v_e |-> entry]
            [def_thm, sub_thm]
          in SOME (entry, mem_thm) end
      else
        case build_leaf_mem right k of
          NONE => NONE
        | SOME (entry, sub_thm) => let
          val key_tm = mlstringSyntax.mk_mlstring k
          val mem_thm = skel_leaf_mem_branch_r
            [vtT |-> tree_tm, v_l |-> tree_tm_of left, v_r |-> tree_tm_of right,
              vk |-> key_tm, v_e |-> entry]
            [def_thm, sub_thm]
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
    val thm = skel_tree_lookup_hit
      [v_t |-> tree_tm_of root, vk1 |-> k1_tm, vk2 |-> k2_tm,
        vk |-> key_tm, v_e |-> entry]
      [wf_thm, mem_thm]
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
      SOME thm => thm
    | NONE => let
      val thm = case lookup_tree_entry root k of SOME thm => thm | NONE => let
        val key_tm = mlstringSyntax.mk_mlstring k
        val (root_k1, root_k2) = bounds_of root
        val (root_k1_str, root_k2_str) = key_strs_of root
        val root_wf = wf_thm_of root
        val root_tm = tree_tm_of root
        in
          if k < root_k1_str then let
            val lt = mk_lt_thm key_tm root_k1
            val other = list_mk_icomb (mlstring_lt_tm, [root_k2, key_tm])
            val disj = DISJ1 lt other
            in skel_tree_lookup_miss
              [v_t |-> root_tm, vk1 |-> root_k1, vk2 |-> root_k2, vk |-> key_tm]
              [root_wf, disj] end
          else if k > root_k2_str then let
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
              val {left, right, def_thm, ...} = case n of EBranch b => b | _ =>
                failwith "tree_miss_thm: in-range leaf miss unexpected"
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
            in MATCH_MP tree_miss_imp_lookup (tree_miss_thm root) end
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
      in SOME (DB.fetch Thy (Name ^ "_wf")) handle HOL_ERR _ => NONE end
    else NONE
  in
    case strip_comb rhs_tm of
      (c, [a, b]) =>
      if same_const c EnvLeaf_tm then let
        val key_str = mlstringSyntax.dest_mlstring a
        val wf_thm = case fetch_saved_wf () of SOME t => t | NONE =>
          MATCH_MP env_wf_leaf_cps def
        in ELeaf { key_tm = a, key_str = key_str, entry_tm = b,
          tree_tm = tree_tm, def_thm = def, wf_thm = wf_thm } end
      else if same_const c EnvBranch_tm then let
        val left = rebuild_node a
        val right = rebuild_node b
        val (k1_tm, kl_tm) = bounds_of left
        val (kr_tm, k2_tm) = bounds_of right
        val (k1_str, _) = key_strs_of left
        val (_, k2_str) = key_strs_of right
        val wf_thm = case fetch_saved_wf () of SOME t => t | NONE => let
          val lt_thm = EQT_ELIM
            (EVAL (list_mk_icomb (mlstring_lt_tm, [kl_tm, kr_tm])))
          val partial = MATCH_MP env_wf_branch_intro_cps
            (LIST_CONJ [def, wf_thm_of left, wf_thm_of right])
          in MATCH_MP partial lt_thm end
        in EBranch { left = left, right = right, k1_tm = k1_tm, k2_tm = k2_tm,
          k1_str = k1_str, k2_str = k2_str, tree_tm = tree_tm, def_thm = def,
          wf_thm = wf_thm, depth = 1 + Int.max (depth_of left, depth_of right) } end
      else failwith ("rebuild_node: constructor not recognised: " ^ Parse.term_to_string c)
    | _ => failwith ("rebuild_node: unexpected rhs shape " ^ Parse.term_to_string rhs_tm)
  end

(* Single cache for build_tree_anon results.  Value = env_node option * thm:
   - (SOME node, equiv) where equiv : nsLookup_all env_tm = tree_lookup <tree>
   - (NONE,      eq)    where eq    : env_tm = empty_env *)
val env_tree_map : (term, env_node option * thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)

fun env_tree_register env_tm result =
  env_tree_map := Redblackmap.insert (!env_tree_map, env_tm, result)

val () = env_tree_register empty_env_tm (NONE, REFL empty_env_tm)

(* --- init_env registration ---
   Assemble the env_node shadow for init_env by walking the pre-built
   init_env_15 tree via rebuild_node.  Each init_env_N_wf is fetched
   from ml_progTheory via the naming convention — no re-derivation. *)
val () = let
  val node = rebuild_node (prim_mk_const {Name = "init_env_15", Thy = "ml_prog"})
  in env_tree_register init_env_const (SOME node, nsLookup_all_init_env) end

(* Attempt to lazily load an env_const's tree data from previously saved
   theorems (via DB.fetch on the naming convention). Returns SOME if it
   succeeds in registering. *)
fun lazy_load env_const = let
  val {Name, Thy, ...} = dest_thy_const env_const
  val equiv_thm = DB.fetch Thy (tree_equiv_name Name)
  val tree_tm = rand (rhs (concl equiv_thm))
  val node = rebuild_node tree_tm
  val _ = env_tree_register env_const (SOME node, equiv_thm)
  in (node, equiv_thm) end

(* Filtered lookup for callers that only care about non-empty trees.
   Empty-cache hits are reported as NONE here. *)
fun env_tree_lookup env_const =
  case Redblackmap.peek (!env_tree_map, env_const) of
    SOME (SOME node, equiv) => SOME (node, equiv)
  | SOME (NONE, _) => NONE
  | NONE => Lib.total lazy_load env_const

fun env_tree_has env_const = isSome (env_tree_lookup env_const)

(* --- derive_nsLookup_tree ---
   Given the new env-abbrev def (env_N = <rhs>), walks the rhs, looks up
   the base env in env_tree_map, builds the new env_node, and proves
     |- nsLookup_all env_N = tree_lookup <new_tree_tm>
   via the step lemmas. Currently handles WRITE at the edges (prepend
   when new key < tree.k1, append when new key > tree.k2). Other shapes
   and ops return NONE and let the caller fall through. *)

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
  val mv_v = optionSyntax.mk_some (mk_icomb (sem_env_v_tm, mod_env_tm))
  val mc_v = optionSyntax.mk_some (mk_icomb (sem_env_c_tm, mod_env_tm))
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

(* Pre-prepared theorems used by derive_nsLookup_tree_merge / build_tree_anon
   to avoid ONCE_REWRITE_RULE on per-call equiv composition.  The original
   merge_env_empty_env has shape `merge_env env empty_env = env /\
   merge_env empty_env env = env` with a single outer ! over env, so we
   GEN_ALL after taking CONJUNCTs to recover universally-quantified forms. *)
val (merge_empty_right, merge_empty_left) = CONJ_PAIR (SPEC_ALL merge_env_empty_env)

(* Shared: env_const = <op n x empty_env> where op ∈ {write, write_cons, ...}.
   Produces a singleton leaf without needing a base tree entry in the map. *)
fun derive_nsLookup_tree_add_empty env_const def n step_lemma entry_tm = let
  val new_leaf = mk_leaf_node n entry_tm
  val goal_lhs = mk_icomb (nsLookup_all_const, env_const)
  val goal_rhs = mk_icomb (tree_lookup_tm, tree_tm_of new_leaf)
  val k_ty = fst (dom_rng (type_of goal_lhs))
  val k_var = mk_var ("k", k_ty)
  val applied_goal = mk_eq (mk_comb (goal_lhs, k_var), mk_comb (goal_rhs, k_var))
  (* If def is a REFL (anonymous env), PURE_REWRITE_TAC [def] is a
      no-op — skip it to avoid the risk of it looping on compound LHS. *)
  val def_is_refl = aconv (lhs (concl def)) (rhs (concl def))
  val pointwise_thm = prove (applied_goal,
    (if def_is_refl then all_tac else PURE_REWRITE_TAC [def])
    \\ once_rewrite_tac [step_lemma]
    \\ simp [nsLookup_all_empty_env,
              def_thm_of new_leaf, tree_lookup_def,
              empty_entry_def])
  val equiv_thm = CONV_RULE (REWR_CONV (GSYM FUN_EQ_THM)) (GEN k_var pointwise_thm)
  in (new_leaf, equiv_thm) end

fun derive_nsLookup_tree_write_empty env_const def n v =
  derive_nsLookup_tree_add_empty env_const def n
    nsLookup_all_write (mk_sv_entry_tm v)

fun derive_nsLookup_tree_write_cons_empty env_const def n c =
  derive_nsLookup_tree_add_empty env_const def n
    nsLookup_all_write_cons (mk_sc_entry_tm c)

fun derive_nsLookup_tree_write_mod_empty env_const def mn mod_env =
  derive_nsLookup_tree_add_empty env_const def mn
    nsLookup_all_write_mod (mk_mod_entry_tm mod_env)

val combine_entries_simps = [
  combine_entries_empty_left,
  combine_entries_empty_right,
  combine_entries_sv_fupd,
  combine_entries_sc_fupd,
  combine_entries_mv_fupd,
  combine_entries_mc_fupd]

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

(* rebalance_join A B: builds an env_node representing EnvBranch A B.
   Precondition: A.max_key < B.min_key (disjoint, strictly ordered).
   Returns (result, thm : tree_lookup (EnvBranch A.tm B.tm) = tree_lookup result.tm).

   Algorithm: AVL join — descend the spine of the taller tree until
   heights are within 1, then mk_branch_node_raw + single rebalance_node
   to absorb the residual imbalance.

   Result is AVL-balanced (0 ≤ depth - max(depth A, depth B) ≤ 1).
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
(* mk_branch packaged with the tree_lookup-equation theorem. *)
fun mk_branch_compound_join lt_thunk A B = let
  val node = mk_branch_node_compound_with lt_thunk A B
  in (node, lift_tree_lookup (SYM (def_thm_of node))) end

(* Flag-controlled AVL join.
   - rotate = false: standard recursive AVL join.  Base case at |diff| ≤ 1.
     When the inner sub-call would otherwise produce an unbalanced result
     (diff = 2 with the heavier side's outer-opposite child taller — the
     classic LR/RL case requiring double rotation), the inner sub-calls
     are flagged rotate = true.
   - rotate = true: the call is the inner of a parent's "single rotation"
     step.  Force destructure (no base case) and dispatch sub-calls to
     plain mk_branch (no further recursion) — the resulting tree may be
     transiently unbalanced, but the parent's second sub-call rebalances. *)
fun rebalance_join_with rotate lt_thunk A B =
  case (depth_of A, depth_of B) of (dA, dB) =>
  if not rotate andalso dA <= dB + 1 andalso dB <= dA + 1 then
    mk_branch_compound_join lt_thunk A B
  else if dA >= dB then let
    val {left = A1, right = A2, def_thm = A_def, wf_thm = A_wf, tree_tm = A_tm, ...} =
      case A of EBranch b => b | _ => failwith "rebalance_join_with: A leaf"
    val inner = if rotate then mk_branch_compound_join else
      rebalance_join_with (dA = dB + 2 andalso depth_of A1 < depth_of A2)
    val (D, thm_D) = inner lt_thunk A2 B
    val lt_A1_D = lt_from_parent_wf
      {parent_tm = A_tm, parent_def = A_def, parent_wf = A_wf, l = A1, r = A2}
    val (E, thm_E) = inner lt_A1_D A1 D
    val th = skel_join_left
      [vtA |-> tree_tm_of A1, vtB |-> tree_tm_of A2, vtC |-> tree_tm_of B,
        vtL |-> A_tm, vtT |-> tree_tm_of D, vtT' |-> tree_tm_of E]
      [A_def, thm_D, thm_E]
    in (E, th) end
  else let
    val {left = B1, right = B2, def_thm = B_def, wf_thm = B_wf, tree_tm = B_tm, ...} =
      case B of EBranch b => b | _ => failwith "rebalance_join_with: B leaf"
    val inner = if rotate then mk_branch_compound_join else
      rebalance_join_with (dB = dA + 2 andalso depth_of B2 < depth_of B1)
    val (D, thm_D) = inner lt_thunk A B1
    val lt_D_B2 = lt_from_parent_wf
      {parent_tm = B_tm, parent_def = B_def, parent_wf = B_wf, l = B1, r = B2}
    val (E, thm_E) = inner lt_D_B2 D B2
    val th = skel_join_right
      [vtA |-> tree_tm_of A, vtB |-> tree_tm_of B1, vtC |-> tree_tm_of B2,
        vtR |-> B_tm, vtT |-> tree_tm_of D, vtT' |-> tree_tm_of E]
      [B_def, thm_D, thm_E]
    in (E, th) end

fun rebalance_join_unprofiled A B = let
  fun thunk () = mk_lt_thm (#2 (bounds_of A)) (#1 (bounds_of B))
  in rebalance_join_with false thunk A B end
fun rebalance_join A B =
  Profile.profile "rebalance_join" (fn () => rebalance_join_unprofiled A B) ()

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
  in
    if A_max_str < B_min_str then
      rebalance_join A B  (* Case 1a: A.keys < B.keys, disjoint. *)
    else if B_max_str < A_min_str then let
      (* Case 1b: B.keys < A.keys, commute then join.  Thunk is lazy so
         rebalance_join_with only pays for mk_lt_thm when its base case
         actually needs it; the swap disjunct below also threads the
         lt through once via the shared lt_cache. *)
      val (D, thm_D) = rebalance_join B A
      val lt_BA = mk_lt_thm B_max_tm A_min_tm
      val th = skel_swap
        [vX |-> A_tm, vY |-> B_tm, vkX1 |-> A_min_tm, vkX2 |-> A_max_tm,
          vkY1 |-> B_min_tm, vkY2 |-> B_max_tm, vtT |-> tree_tm_of D]
        [thm_D, A_wf, B_wf, lt_BA]
      in (D, th) end
    else
      (* Ranges overlap.  Dispatch on A's shape. *)
      case A of
        EBranch {left = A1, right = A2, tree_tm = A_tm, def_thm = A_def, ...} =>
        (case (key_strs_of A1, key_strs_of A2) of ((_, A1_max_str), (A2_min_str, _)) =>
        if B_max_str < A2_min_str then let
          (* Case 2a: A = EBranch(A1, A2), B's keys all < A2.min.
            Transform tree_lookup (EnvBranch A B) into tree_lookup (EnvBranch (EnvBranch A1 B) A2)
            via rotate_right + inner commute + rotate_left, then recurse merge_trees(A1, B). *)
          val lt_B_A2 = mk_lt_thm (#2 (bounds_of B)) (#1 (bounds_of A2))
          val (D, thm_D) = merge_trees A1 B
          val (E, thm_E) = rebalance_join D A2
          val (A2_min_tm, A2_max_tm) = bounds_of A2
          val (B_min_tm, B_max_tm) = bounds_of B
          val th = skel_commute_left
            [vtA |-> tree_tm_of A1, vtB |-> tree_tm_of A2, vtC |-> tree_tm_of B,
              vtL |-> A_tm, vtT |-> tree_tm_of D, vtT' |-> tree_tm_of E,
              vkB1 |-> A2_min_tm, vkB2 |-> A2_max_tm,
              vkC1 |-> B_min_tm,  vkC2 |-> B_max_tm]
            [A_def, thm_D, thm_E, wf_thm_of A2, wf_thm_of B, lt_B_A2]
          in (E, th) end
        else if B_min_str > A1_max_str then let
          (* Case 2b: A = EBranch(A1, A2), B's keys all > A1.max.
            Transform via rotate_right, then recurse merge_trees(A2, B), rejoin with A1. *)
          val (D, thm_D) = merge_trees A2 B
          val (E, thm_E) = rebalance_join A1 D
          val th = skel_join_left
            [vtA |-> tree_tm_of A1, vtB |-> tree_tm_of A2, vtC |-> tree_tm_of B,
              vtL |-> A_tm, vtT |-> tree_tm_of D, vtT' |-> tree_tm_of E]
            [A_def, thm_D, thm_E]
          in (E, th) end
        else
          case B of EBranch B => merge_trees_split_right A B
          | _ => failwith "merge_trees_split_right: B not a branch")
      | ELeaf {key_tm = k_tm, entry_tm = v1_tm, def_thm = A_def, ...} => case B of
        EBranch B => merge_trees_split_right A B
      | ELeaf {entry_tm = v2_tm, def_thm = B_def, ...} => let
        (* Case 4: Both A and B are leaves, combine entries. *)
        val simp_eq = simp_combine_entries v1_tm v2_tm
        val combined_v = rhs (concl simp_eq)
        val D = if aconv combined_v v1_tm then A else mk_leaf_node k_tm combined_v
        val th = skel_coalesce_leaves
          [vtL1 |-> tree_tm_of A, vtL2 |-> tree_tm_of B, vk |-> k_tm,
            v_e1 |-> v1_tm, v_e2 |-> v2_tm, v_e |-> combined_v, vtT |-> tree_tm_of D]
          [A_def, B_def, simp_eq, def_thm_of D]
        in (D, th) end
  end

(* Case 3: B = EBranch(B1, B2), split B and recurse.
   rotate_left to transform (A, (B1, B2)) -> ((A, B1), B2),
   recurse merge_trees(A, B1) = D,
   then recurse merge_trees(D, B2) = E to finish. *)
and merge_trees_split_right A {left = B1, right = B2, def_thm = B_def, tree_tm = B_tm, ...} = let
  val (D, thm_D) = merge_trees A B1
  val (result, thm_E) = merge_trees D B2
  val th = skel_join_right
    [vtA |-> tree_tm_of A, vtB |-> tree_tm_of B1, vtC |-> tree_tm_of B2,
      vtR |-> B_tm, vtT |-> tree_tm_of D, vtT' |-> tree_tm_of result]
    [B_def, thm_D, thm_E]
  in (result, th) end

(* Generic builder for write/write_cons/write_mod using merge_trees.
   Builds a singleton leaf, calls merge_trees(leaf, base), and threads through
   the tree-level step theorem (nsLookup_all_write_tree_cps, etc.). *)
fun derive_nsLookup_tree_add_via_merge def n skel_step entry_tm
    subst_extra (base_node, base_equiv) = let
  val new_leaf = mk_leaf_node n entry_tm
  val base_tm = tree_tm_of base_node
  val leaf_tm = tree_tm_of new_leaf
  val branch_leaf_base = list_mk_comb (EnvBranch_tm, [leaf_tm, base_tm])
  val base_env_tm = rand (lhs (concl base_equiv))
  val step_thm = skel_step
    ([vtT  |-> base_tm, vtL  |-> leaf_tm, vTnew |-> branch_leaf_base,
      vn   |-> n, v_env |-> base_env_tm] @ subst_extra)
    [base_equiv, def_thm_of new_leaf, REFL branch_leaf_base]
  val (transient_node, merge_thm) = merge_trees new_leaf base_node
  val (new_node, mat_eq) = materialize_node transient_node
  val mat_thm = lift_tree_lookup mat_eq
  val combined = TRANS step_thm (TRANS merge_thm mat_thm)
  val equiv_thm =
    if aconv (lhs (concl def)) (rhs (concl def))
    then combined
    else TRANS (AP_TERM nsLookup_all_const def) combined
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
fun derive_nsLookup_tree_merge def (node1, equiv1) (node2, equiv2) = let
  val (transient_node, tree_merge_eq) = merge_trees node1 node2
  val (final_node, mat_eq) = materialize_node transient_node
  val mat_thm = lift_tree_lookup mat_eq
  val merge_tree_equiv = MATCH_MP nsLookup_all_merge_tree (CONJ equiv1 equiv2)
  val combined = TRANS merge_tree_equiv (TRANS tree_merge_eq mat_thm)
  val equiv_thm = TRANS (AP_TERM nsLookup_all_const def) combined
  in (final_node, equiv_thm) end

(* Build (env_node, equiv_thm) for a compound env term anonymously: no
   theory-constant save, no env_tree_map registration.  Used by `need_base`
   when the base of a write/write_cons/write_mod is itself a compound
   (e.g. nested Dtype expansions produce `write_cons A (write_cons B env_c)`
   in a single abbreviation RHS).  For empty_env bases, uses the *_empty
   builders; otherwise recurses. *)
(* build_tree_anon env_tm : env_node option * thm
   - (SOME node, equiv) where equiv : nsLookup_all env_tm = tree_lookup <node.tree_tm>
   - (NONE,      eq)    where eq    : env_tm = empty_env
   Raises HOL_ERR for shapes the tree builder can't classify (e.g. literal
   sem_env records); the caller falls back to a focused rewrite path. *)
fun build_tree_anon env_tm = let
  fun get () = let
    val anon_def = REFL env_tm
    (* On NONE base for OpWrite/Cons/Mod: substitute b with empty_env
      in env_tm, run the _empty handler for `op n x empty_env`, then
      compose its equiv back through the substitution. *)
    fun on_empty_base n step_lemma entry_tm base_eq = let
      val partial = rator env_tm  (* = <op> n x *)
      val sub_eq = AP_TERM partial base_eq
        (* env_tm = <op> n x empty_env *)
      val empty_const = rhs (concl sub_eq)
      val (new_node, equiv') =
        derive_nsLookup_tree_add_empty empty_const (REFL empty_const)
          n step_lemma entry_tm
      val ap = AP_TERM nsLookup_all_const sub_eq
      val equiv = TRANS ap equiv'
      in (SOME new_node, equiv) end
    in
      case classify_rhs env_tm of
        SOME (OpWrite (n, v, b)) =>
        (case build_tree_anon b of
          (NONE, base_eq) =>
          on_empty_base n nsLookup_all_write (mk_sv_entry_tm v) base_eq
        | (SOME node, equiv) => let
          val (new_node, equiv') = derive_nsLookup_tree_write anon_def n v (node, equiv)
          in (SOME new_node, equiv') end)
      | SOME (OpWriteCons (n, c, b)) =>
        (case build_tree_anon b of
          (NONE, base_eq) =>
          on_empty_base n nsLookup_all_write_cons (mk_sc_entry_tm c) base_eq
        | (SOME node, equiv) => let
          val (new_node, equiv') = derive_nsLookup_tree_write_cons anon_def n c (node, equiv)
          in (SOME new_node, equiv') end)
      | SOME (OpWriteMod (mn, m, b)) =>
        (case build_tree_anon b of
          (NONE, base_eq) =>
          on_empty_base mn nsLookup_all_write_mod (mk_mod_entry_tm m) base_eq
        | (SOME node, equiv) => let
          val (new_node, equiv') = derive_nsLookup_tree_write_mod anon_def mn m (node, equiv)
          in (SOME new_node, equiv') end)
      | SOME (OpMergeEnv (e1, e2)) =>
        (case rator (rator env_tm) of merge_const =>
        case (build_tree_anon e1, build_tree_anon e2) of
          ((NONE, eq1), (NONE, eq2)) => let
          (* merge_env e1 e2 = merge_env empty_env empty_env = empty_env *)
          val ap1 = AP_TERM merge_const eq1
          val combined = MK_COMB (ap1, eq2)
          val collapse = INST [v_env |-> empty_env_tm] merge_empty_left
          val final_eq = TRANS combined collapse
          in (NONE, final_eq) end
        | ((NONE, eq1), (SOME node, equiv2)) => let
          (* merge_env e1 e2 = merge_env empty_env e2 = e2;
            nsLookup_all env_tm = nsLookup_all e2 = tree_lookup tree *)
          val ap1 = AP_TERM merge_const eq1
          val sub  = MK_COMB (ap1, REFL e2)
            (* merge_env e1 e2 = merge_env empty_env e2 *)
          val collapse = INST [v_env |-> e2] merge_empty_left
          val sub_eq = TRANS sub collapse
            (* merge_env e1 e2 = e2 *)
          val ap_all = AP_TERM nsLookup_all_const sub_eq
          val equiv  = TRANS ap_all equiv2
          in (SOME node, equiv) end
        | ((SOME node, equiv1), (NONE, eq2)) => let
          val ap2 = MK_COMB (AP_TERM merge_const (REFL e1), eq2)
            (* merge_env e1 e2 = merge_env e1 empty_env *)
          val collapse = INST [v_env |-> e1] merge_empty_right
          val sub_eq = TRANS ap2 collapse
            (* merge_env e1 e2 = e1 *)
          val ap_all = AP_TERM nsLookup_all_const sub_eq
          val equiv  = TRANS ap_all equiv1
          in (SOME node, equiv) end
        | ((SOME node1, equiv1), (SOME node2, equiv2)) => let
          val (new_node, new_equiv) =
            derive_nsLookup_tree_merge anon_def (node1, equiv1) (node2, equiv2)
          in (SOME new_node, new_equiv) end)
      | NONE => failwith ("build_tree_anon: unrecognized env shape: " ^ Parse.term_to_string env_tm)
    end
  in
    case Redblackmap.peek (!env_tree_map, env_tm) of
      SOME r => r
    | NONE => let
      val r = case Lib.total lazy_load env_tm of
        SOME (node, equiv) => (SOME node, equiv)
      | NONE => get ()
      in env_tree_register env_tm r; r end
  end

(* PROFILE *)
val build_tree_anon = fn t => Profile.profile "build_tree_anon" build_tree_anon t

fun derive_nsLookup_tree def = let
  val (env_const, rhs) = def |> concl |> dest_eq
  val need_base = build_tree_anon
  val (new_node, equiv_thm) = case classify_rhs rhs of
    SOME (OpWrite (n, v, base_const)) =>
    (case need_base base_const of
      (NONE, _) => derive_nsLookup_tree_write_empty env_const def n v
    | (SOME node, equiv) => derive_nsLookup_tree_write def n v (node, equiv))
  | SOME (OpWriteCons (n, c, base_const)) =>
    (case need_base base_const of
      (NONE, _) => derive_nsLookup_tree_write_cons_empty env_const def n c
    | (SOME node, equiv) => derive_nsLookup_tree_write_cons def n c (node, equiv))
  | SOME (OpWriteMod (mn, mod_env, base_const)) =>
    (case need_base base_const of
      (NONE, _) => derive_nsLookup_tree_write_mod_empty env_const def mn mod_env
    | (SOME node, equiv) => derive_nsLookup_tree_write_mod def mn mod_env (node, equiv))
  | SOME (OpMergeEnv (e1, e2)) =>
    (case (need_base e1, need_base e2) of
      ((NONE, _), (NONE, _)) =>
        failwith "derive_nsLookup_tree: merge_env empty empty at named env_const"
    | ((NONE, _), (SOME node, equiv)) => let
      val collapse = INST [v_env |-> e2] merge_empty_left
      val collapse_v = AP_TERM nsLookup_all_const collapse
      val def_v = AP_TERM nsLookup_all_const def
      val equiv_thm = TRANS def_v (TRANS collapse_v equiv)
      in (node, equiv_thm) end
    | ((SOME node, equiv), (NONE, _)) => let
      val collapse = INST [v_env |-> e1] merge_empty_right
      val collapse_v = AP_TERM nsLookup_all_const collapse
      val def_v = AP_TERM nsLookup_all_const def
      val equiv_thm = TRANS def_v (TRANS collapse_v equiv)
      in (node, equiv_thm) end
    | ((SOME node1, equiv1), (SOME node2, equiv2)) =>
      derive_nsLookup_tree_merge def (node1, equiv1) (node2, equiv2))
  | NONE => failwith ("derive_nsLookup_tree: unsupported rhs shape: " ^ Parse.term_to_string rhs)
  (* Walk env_node, building |- <node.tree_tm> = <fully-inline tree>.
     Each EBranch's def_thm is `tree_tm = EnvBranch L R` (where L, R are
     inner-const tree_tms whose own _def is not persisted); we recursively
     inline them. *)
  fun inline_node (ELeaf {def_thm, ...}) = def_thm
    | inline_node (EBranch {def_thm, left, right, ...}) = let
      val eL = inline_node left
      val eR = inline_node right
      val branch_eq = MK_COMB (AP_TERM EnvBranch_tm eL, eR)
      in TRANS def_thm branch_eq end
  val _ = env_tree_register env_const (SOME new_node, equiv_thm)
  (* For named env: define a separate "<env_name>_tree" constant whose def
     has the FULLY INLINED tree rhs (no inner-const refs). Save tree_equiv
     and tree_wf in terms of this outer const so cross-script lazy_load
     can rebuild without needing the inner consts' deleted _def bindings.
     The env_node itself is unchanged: its tree_tm/def_thm still reference
     the shallow inner const, which is what subsequent in-script merges
     expect. *)
  val _ = case Lib.total dest_const env_const of
    NONE => ()
  | SOME (env_name, _) => let
    val expand_thm = inline_node new_node
      (* expand_thm : <new_node.tree_tm> = <inline_tree> *)
    val inline_tree = boolSyntax.rhs (concl expand_thm)
    val const_nm = env_name ^ "_tree"
    val lhs_v = mk_var (const_nm, env_tree_ty)
    val root_def = Definition.new_definition (const_nm ^ "_def", mk_eq (lhs_v, inline_tree))
    val tree_eq_root = TRANS expand_thm (SYM root_def)
      (* tree_eq_root : <new_node.tree_tm> = <env_name>_tree *)
    val outer_wf = SUBS [tree_eq_root] (wf_thm_of new_node)
    val outer_equiv = TRANS equiv_thm (AP_TERM tree_lookup_tm tree_eq_root)
    in
      allowing_rebind save_thm (tree_equiv_name env_name, outer_equiv);
      allowing_rebind save_thm (tree_wf_name env_name, outer_wf); ()
    end
  in equiv_thm end

(* PROFILE *)
val derive_nsLookup_tree = fn d => Profile.profile "derive_nsLookup_tree" derive_nsLookup_tree d

(* Reduce  (sv_fupd ... (sc_fupd ... empty_entry)).<field>  to its
   payload, leaving the payload (e.g. SOME v) opaque. *)
val proj_field_conv : conv = computeLib.WEAK_CBV_CONV $ computeLib.new_compset (
  BODY_CONJUNCTS env_entry_accfupds @
  BODY_CONJUNCTS env_entry_accessors @
  [combinTheory.K_THM, empty_entry_def])

fun nsLookup_tree_conv tm = let
  val (f, args) = strip_comb tm
  val ismod = if same_const f nsLookup_Mod1_tm then true else
    if same_const f nsLookup_Short_tm then false else raise UNCHANGED
  val (ns_arg, key_arg) = case args of [a, b] => (a, b) | _ => raise UNCHANGED
  val (accessor, env_const) = dest_comb ns_arg handle _ => raise UNCHANGED
  val is_v = if same_const accessor sem_env_v_tm then true else
    if same_const accessor sem_env_c_tm then false else raise UNCHANGED
  val key_str = mlstringSyntax.dest_mlstring key_arg handle _ => raise UNCHANGED
  val proj_thm = case (ismod, is_v) of
    (false, true)  => nsLookup_Short_v_via_all
  | (false, false) => nsLookup_Short_c_via_all
  | (true,  true)  => nsLookup_Mod1_v_via_all
  | (true,  false) => nsLookup_Mod1_c_via_all
  val spec = INST [v_env |-> env_const, vk |-> key_arg] proj_thm
  (* spec : nsLookup_<kind> env_const.<field> key_arg
          = (nsLookup_all env_const key_arg).<field> *)
  in
    case build_tree_anon env_const handle _ => raise UNCHANGED of
      (SOME node, equiv_thm) => let
      val lookup_thm = tree_lookup_thm node key_str
      (* equiv_thm : nsLookup_all env_const = tree_lookup tree_tm *)
      val conv = RAND_CONV (RATOR_CONV (K equiv_thm) THENC K lookup_thm)
                  THENC proj_field_conv
      in CONV_RULE (RAND_CONV conv) spec end
    | (NONE, eq_thm) => let
      (* eq_thm : env_const = empty_env. Substitute and reduce via
        nsLookup_all_empty_env + proj_field_conv. *)
      val ap_all = AP_THM (AP_TERM nsLookup_all_const eq_thm) key_arg
        (* nsLookup_all env_const key_arg = nsLookup_all empty_env key_arg *)
      val empty_lookup = SPEC key_arg nsLookup_all_empty_env
        (* nsLookup_all empty_env key_arg = empty_entry *)
      val combined = TRANS ap_all empty_lookup
        (* nsLookup_all env_const key_arg = empty_entry *)
      val conv = RAND_CONV (K combined) THENC proj_field_conv
      in CONV_RULE (RAND_CONV conv) spec end
  end

(* PROFILE *)
val nsLookup_tree_conv = fn tm => Profile.profile "nsLookup_tree_conv" nsLookup_tree_conv tm

(* simpset-based nsLookup_conv.
   - rewrites: nsLookup_eq + bool/option cleanup
   - registered conv: nsLookup_tree_conv triggered on nsLookup_Short / nsLookup_Mod1
   Early exit: only run SIMP_CONV when the top-level head is one we own. *)
local
  structure Parse = struct
    open Parse
    val (Type, Term) = parse_from_grammars $ valOf $ grammarDB {thyname = "ml_prog"}
  end
  open Parse simpLib
  val pats = [``nsLookup_Short (env:v sem_env).c k``, ``nsLookup_Mod1 (env:v sem_env).c k``,
              ``nsLookup_Short (env:v sem_env).v k``, ``nsLookup_Mod1 (env:v sem_env).v k``]
  val ss = boolSimps.bool_ss ++ merge_ss [
    rewrites [nsLookup_eq, lookup_var_def, lookup_cons_def, boolTheory.REFL_CLAUSE,
      boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES, boolTheory.COND_CLAUSES,
      optionTheory.option_case_def, optionTheory.OPTION_CHOICE_def,
      (* symbolic-namespace forms used in cf proofs (eval_nsLookup_tac etc.) *)
      nsLookup_Short_nsBind, nsLookup_Short_nsAppend_simp, nsLookup_Short_Bind,
      nsLookup_Mod1_nsBind, nsLookup_Mod1_nsAppend, nsLookup_Mod1_Bind],
    std_conv_ss {name = "nsLookup_tree_conv", pats = pats, conv = nsLookup_tree_conv}]
in
  val nsLookup_conv = simpLib.SIMP_CONV ss []
end

(* PROFILE *)
val nsLookup_conv = Profile.profile "nsLookup_conv" nsLookup_conv
val nsLookup_tree_conv = Profile.profile "nsLookup_tree_conv" nsLookup_tree_conv

val () = [nsLookup_Mod1_tm, nsLookup_Short_tm]
  |> map (fn t => (t, 2, QCHANGED_CONV nsLookup_conv)) |> computeLib.add_convs

(* helper functions *)

val reduce_conv =
  (* this could be a custom compset, but it's easier to get the
     necessary state updates directly from EVAL
     TODO: Might need more custom rewrites for env-refactor updates
  *)
  EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC
  EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL;

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

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

fun let_st_abbrev conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
  val (th, abbrev_defs) = cond_let_abbrev true true (auto_name "st") conv op_nm th
  in (th, ML_code (abbrev_defs @ ss, envs, vs, ml_th)) end

fun let_env_abbrev conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
  val (th, abbrev_defs) = cond_let_abbrev true false (auto_name "env") conv op_nm th
  fun f d =
    ignore (derive_nsLookup_tree d)
    handle e => (
      TextIO.output (TextIO.stdErr,
        "derive_nsLookup_tree failed on:\n  "
        ^ Parse.thm_to_string d ^ "\n  error: "
        ^ General.exnMessage e ^ "\n");
      Portable.reraise e)
  in app f abbrev_defs; (th, ML_code (ss, abbrev_defs @ envs, vs, ml_th)) end

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

fun forall_nsLookup_upd _ (th,x) = let
  val conv = LAND_CONV (LAND_CONV (nsLookup_conv THENC EVAL) THENC REWR_CONV SOME_11)
  in (CONV_RULE (QUANT_CONV conv THENC unwind_forall_conv) th, x) end
  handle HOL_ERR _ => failwith "forall_nsLookup_upd: nsLookup failed to produce SOME"

fun solve_ml_imp f nm (th, ML_code code) = let
  val msg = "solve_ml_imp: " ^ nm ^ ": not imp"
  val _ = is_imp (concl th) orelse (print (msg ^ "\n\n"); print_term (concl th); failwith msg)
  in (f th, ML_code code) end
fun solve_ml_imp_mp lemma = solve_ml_imp (fn th => MATCH_MP th lemma)
val solve_ml_imp_conv = solve_ml_imp o MP_CONV

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

fun get_block_names (ML_code (_, _, _, th)) = ML_code_blocks (concl th) |> map (dest_comment o hd)

fun get_open_modules code = get_block_names code
  |> filter (fn ("Module", _) => true | _ => false)
  |> map snd |> rev

fun get_mod_prefix code = case get_open_modules code of [] => "" | (m :: _) => m ^ "_"

fun close_local_blocks code = case get_block_names code of
    ("Local", "in") :: _ => close_local_blocks (close_local_block code)
  | ("Local", "local") :: _ => open_local_in_block code |> close_local_block |> close_local_blocks
  | _ => code

(* PROFILE: rebind so that internal callers (add_dec) hit the profiled versions *)
val add_Dlet    = fn t => fn s => fn st => Profile.profile "add_Dlet"    (fn () => add_Dlet t s st) ()
val add_Dtype   = fn l => fn t => fn st => Profile.profile "add_Dtype"   (fn () => add_Dtype l t st) ()
val add_Dletrec = fn l => fn f => fn n => fn st => Profile.profile "add_Dletrec" (fn () => add_Dletrec l f n st) ()
val add_Dexn    = fn l => fn n => fn t => fn st => Profile.profile "add_Dexn" (fn () => add_Dexn l n t st) ()
val add_Dtabbrev = fn l => fn a => fn b => fn c => fn st => Profile.profile "add_Dtabbrev" (fn () => add_Dtabbrev l a b c st) ()
val add_Dlet_Fun = fn l => fn n => fn v => fn e => fn s => fn st => Profile.profile "add_Dlet_Fun" (fn () => add_Dlet_Fun l n v e s st) ()
val add_Dlet_Var_Var = fn l => fn n => fn vn => fn st => Profile.profile "add_Dlet_Var_Var" (fn () => add_Dlet_Var_Var l n vn st) ()
val add_Dlet_Var_Ref_Var = fn l => fn n => fn vn => fn vnm => fn st => Profile.profile "add_Dlet_Var_Ref_Var" (fn () => add_Dlet_Var_Ref_Var l n vn vnm st) ()
val add_Denv = fn t => fn s => fn st => Profile.profile "add_Denv" (fn () => add_Denv t s st) ()

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

fun get_thm (ML_code (_,_,_,th)) = th
fun get_v_defs (ML_code (_,_,vs,_)) = vs

fun get_prog (ML_code (_,_,_,th)) =
  case ML_code_blocks (concl th) of
    [_(*comm*) :: _(*st*) :: prog :: _] => prog
  | _ => failwith ("get_prog: couldn't get toplevel declarations")
fun get_Decls_thm code = let
  val _ = get_prog code
  in MATCH_MP ML_code_Decls (get_thm code) end

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

(* PROFILE *)
val add_dec  = fn d => fn p => fn st => Profile.profile "add_dec"  (fn () => add_dec d p st) ()
val add_prog = fn p => fn pn => fn st => Profile.profile "add_prog" (fn () => add_prog p pn st) ()

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) =
  pack_4tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (ss, envs, vs, th)

fun unpack_ml_prog_state t = let
  val (ss, envs, vs, th) =
    unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
      (unpack_list unpack_thm) unpack_thm t
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

(* PROFILE: dump on exit *)

(* Phase timing: measure script work vs theory export. *)
local
  val mlpL_load_time = Time.now ()
  val export_start = ref NONE : Time.time option ref
in
  val () = Theory.register_hook ("ml_progLib_profile_phase",
    fn TheoryDelta.ExportTheory _ =>
      (case !export_start of NONE => export_start := SOME (Time.now ()) | _ => ())
    | _ => ())
  val () = OS.Process.atExit (fn () =>
    let
      val thy = Theory.current_theory () handle _ => "?"
      val now = Time.now ()
      val t_script = case !export_start of
        SOME t => Time.toReal (Time.- (t, mlpL_load_time))
      | NONE => Time.toReal (Time.- (now, mlpL_load_time))
      val t_export = case !export_start of
        SOME t => Time.toReal (Time.- (now, t))
      | NONE => 0.0
      val out = TextIO.openAppend "/tmp/ml_progLib_profile.log"
    in
      TextIO.output (out, "=== " ^ thy ^ " (cakeml-3) ===\n");
      TextIO.output (out, "[phase] script=" ^ Real.fmt (StringCvt.FIX (SOME 2)) t_script
        ^ "s  export=" ^ Real.fmt (StringCvt.FIX (SOME 2)) t_export ^ "s\n");
      Profile.output_profile_results out (Profile.results ());
      TextIO.output (out, "\n");
      TextIO.closeOut out
    end handle _ => ())
end

end
