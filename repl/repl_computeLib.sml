structure repl_computeLib = struct
open preamble repl_funTheory ASCIInumbersLib intLib
open AstTheory inferTheory CompilerTheory compilerTerminationTheory bytecodeEvalTheory
open repl_computeTheory;

val t_unify_wfs = prove(
 ``t_wfs s ∧ (t_unify s t1 t2 = SOME sx) ==> t_wfs sx``,
 metis_tac[unifyTheory.t_unify_unifier])

val t_wfs_FEMPTY = prove(
  ``t_wfs FEMPTY``,
  rw[unifyTheory.t_wfs_def])

val _ = computeLib.add_funs
  [unifyTheory.t_walk_eqn
  ,unifyTheory.t_ext_s_check_eqn
  ,computeLib.lazyfy_thm(bytecodeEvalTheory.bc_eval_def)
  ]
val _ = computeLib.add_funs[listTheory.SUM] (* why isn't this in there already !? *)

val db = ref (Net.insert (rand(concl(t_wfs_FEMPTY)),t_wfs_FEMPTY) Net.empty)
fun t_unify_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_unify_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  val th3 = TRANS th1 th2
  val res = rhs(concl th2)
  val _ = if optionSyntax.is_some res then
          db := Net.insert (rand res,PROVE[wfs_s,t_unify_wfs,th3]``^(rator(concl wfs_s)) ^(rand res)``) (!db)
          else ()
  in th3 end
fun t_vwalk_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_vwalk_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_oc_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_oc_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_walkstar_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_walkstar_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end

val _ = computeLib.add_convs
[(``t_unify``,3,t_unify_conv)
,(``t_vwalk``,2,t_vwalk_conv)
,(``t_walkstar``,2,t_walkstar_conv)
,(``t_oc``,3,t_oc_conv)
]

(* add repl definitions to the compset *)

val RES_FORALL_set = prove(``RES_FORALL (set ls) P = EVERY P ls``,rw[RES_FORALL_THM,listTheory.EVERY_MEM])

val bc_fetch_aux_zero = prove(
``∀ls n. bc_fetch_aux ls (K 0) n = el_check n (FILTER ($~ o is_Label) ls)``,
Induct >> rw[CompilerLibTheory.el_check_def] >> fs[] >> fsrw_tac[ARITH_ss][] >>
simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

val _ = computeLib.add_funs
  [ElabTheory.elab_p_def
  ,ElabTheory.elab_decs_def
  ,CompilerLibTheory.find_index_def
  ,CompilerLibTheory.the_def
  ,CompilerLibTheory.lunion_def
  ,CompilerLibTheory.lshift_def
  ,pat_bindings_def
  ,compile_news_def
  ,ToBytecodeTheory.compile_varref_def
  ,CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)compile_def
  ,label_closures_def
  ,remove_mat_var_def
  ,ToIntLangTheory.remove_mat_vp_def
  ,mkshift_def
  ,ToBytecodeTheory.cce_aux_def
  ,exp_to_Cexp_def
  ,ToIntLangTheory.pat_to_Cpat_def
  ,ToIntLangTheory.Cpat_vars_def
  ,generalise_def
  ,RES_FORALL_set
  ,bc_fetch_aux_zero
  ]

val _ = let
  open computeLib
in
  set_skip the_compset ``evalcase_CASE`` (SOME 1);
  set_skip the_compset ``list_CASE`` (SOME 1);
  set_skip the_compset ``option_CASE`` (SOME 1);
  set_skip the_compset ``sum_CASE`` (SOME 1);
  set_skip the_compset ``id_CASE`` (SOME 1);
  set_skip the_compset ``tc0_CASE`` (SOME 1);
  set_skip the_compset ``t_CASE`` (SOME 1);
  set_skip the_compset ``lit_CASE`` (SOME 1);
  set_skip the_compset ``pat_CASE`` (SOME 1);
  set_skip the_compset ``lop_CASE`` (SOME 1);
  set_skip the_compset ``opb_CASE`` (SOME 1);
  set_skip the_compset ``opn_CASE`` (SOME 1);
  set_skip the_compset ``op_CASE`` (SOME 1);
  set_skip the_compset ``uop_CASE`` (SOME 1);
  set_skip the_compset ``exp_CASE`` (SOME 1);
  set_skip the_compset ``dec_CASE`` (SOME 1);
  set_skip the_compset ``spec_CASE`` (SOME 1);
  set_skip the_compset ``top_CASE`` (SOME 1);
  set_skip the_compset ``ast_t_CASE`` (SOME 1);
  set_skip the_compset ``ast_pat_CASE`` (SOME 1);
  set_skip the_compset ``ast_exp_CASE`` (SOME 1);
  set_skip the_compset ``ast_dec_CASE`` (SOME 1);
  set_skip the_compset ``ast_spec_CASE`` (SOME 1);
  set_skip the_compset ``ast_top_CASE`` (SOME 1);
  set_skip the_compset ``bc_stack_op_CASE`` (SOME 1);
  set_skip the_compset ``bc_inst_CASE`` (SOME 1);
  set_skip the_compset ``compiler_state_CASE`` (SOME 1);
  set_skip the_compset ``Cpat_CASE`` (SOME 1);
  set_skip the_compset ``exp_to_Cexp_state_CASE`` (SOME 1);
  set_skip the_compset ``compiler_result_CASE`` (SOME 1);
  set_skip the_compset ``call_context_CASE`` (SOME 1);
  set_skip the_compset ``ctbind_CASE`` (SOME 1);
  set_skip the_compset ``COND`` (SOME 1)
end

val eval_compile_primitives = EVAL ``compile_primitives``
val _ = computeLib.del_funs[compile_primitives_def]
val _ = computeLib.add_funs[eval_compile_primitives]
val eval_initial_repl_fun_state = EVAL ``initial_repl_fun_state``
val _ = PolyML.fullGC();
(* too slow!
val eval_initial_bc_state = EVAL ``initial_bc_state``
*)
val _ = computeLib.del_funs[initial_repl_fun_state_def,initial_bc_state_def]
val _ = computeLib.add_funs[eval_initial_repl_fun_state(*,eval_initial_bc_state*)]

(* faster evaluation of the compile_dec *)

val _ = Globals.max_print_depth := 15

fun rbinop_size acc t =
    if is_const t orelse is_var t then acc else rbinop_size (acc + 1) (rand t)
fun lbinop_size acc t =
    if is_const t orelse is_var t then acc else lbinop_size (acc + 1) (lhand t)

fun term_lsplit_after n t = let
  fun recurse acc n t =
    if n <= 0 then (List.rev acc, t)
    else
      let val (fx,y) = dest_comb t
          val (f,x) = dest_comb fx
      in
        recurse (x::acc) (n - 1) y
      end handle HOL_ERR _ => (List.rev acc, t)
in
  recurse [] n t
end

val (app_nil, app_cons) = CONJ_PAIR listTheory.APPEND
fun APP_CONV t = (* don't eta-convert *)
    ((REWR_CONV app_cons THENC RAND_CONV APP_CONV) ORELSEC
     REWR_CONV app_nil) t

fun onechunk n t = let
  val (pfx, sfx) = term_lsplit_after n t
in
  if null pfx orelse listSyntax.is_nil sfx then raise UNCHANGED
  else let
    val pfx_t = listSyntax.mk_list(pfx, type_of (hd pfx))
  in
    APP_CONV (listSyntax.mk_append(pfx_t, sfx)) |> SYM
  end
end

fun chunkify_CONV n t =
    TRY_CONV (onechunk n THENC RAND_CONV (chunkify_CONV n)) t

val Dlet_t = prim_mk_const{Thy = "Ast", Name = "Dlet"}
val Dletrec_t = prim_mk_const{Thy = "Ast", Name = "Dletrec"}
val Dtype_t = prim_mk_const{Thy = "Ast", Name = "Dtype"}
fun declstring t = let
  val (f, args) = strip_comb t
in
  if same_const f Dlet_t then "val " ^ Literal.dest_string_lit (rand (hd args))
  else if same_const f Dletrec_t then
    let
      val (fdecs,_) = listSyntax.dest_list (hd args)
    in
      "fun " ^ Literal.dest_string_lit (hd (pairSyntax.strip_pair (hd fdecs))) ^
      (if length fdecs > 1 then "*" else "")
    end
  else if same_const f Dtype_t then
    let
      val (tydecs,_) = listSyntax.dest_list (hd args)
    in
      "datatype " ^
      Literal.dest_string_lit (hd (tl (pairSyntax.strip_pair (hd tydecs)))) ^
      (if length tydecs > 1 then "*" else "")
    end
  else "??"
end

val (FOLDL_NIL, FOLDL_CONS) = CONJ_PAIR listTheory.FOLDL
val FOLDL_EVAL = let
  (* t is of form FOLDL f acc [e1; e2; e3; .. ] and f is evaluated with EVAL. *)
  fun eval n t = (PolyML.fullGC(); print ("(" ^ declstring (rand t) ^ ")");
                  EVAL t before print (Int.toString n ^ " "))
  fun recurse n t =
      (REWR_CONV FOLDL_NIL ORELSEC
       (REWR_CONV FOLDL_CONS THENC RATOR_CONV (RAND_CONV (eval n)) THENC
        recurse (n + 1))) t
in
  recurse 0
end

fun foldl_append_CONV d = let
  val core = RAND_CONV (K d) THENC FOLDL_EVAL
in
  REWR_CONV rich_listTheory.FOLDL_APPEND THENC
  RATOR_CONV (RAND_CONV core)
end

fun iterate n defs t = let
  fun recurse m defs th = let
    val t = rhs (concl th)
  in
    if m < 1 orelse null defs then (defs, th)
    else if listSyntax.is_append (rand t) then
      let
        val _ = print (Int.toString (n - m) ^ ": ")
        val th' = time (foldl_append_CONV (hd defs)) (rhs (concl th))
      in
        recurse (m - 1) (tl defs) (TRANS th th')
      end
    else
      let
        val _ = print (Int.toString (n - m) ^ ": ")
        val th' = time (RAND_CONV (K (hd defs)) THENC FOLDL_EVAL)
                       (rhs (concl th))
      in
        (tl defs, TRANS th th')
      end
  end
in
  recurse n defs (REFL t)
end

fun fmkeys fm_t = let
  val kv = rand fm_t
in
  lhand kv :: fmkeys (lhand fm_t)
end handle HOL_ERR _ => []

val FLOOKUP_t = prim_mk_const { Thy = "finite_map", Name = "FLOOKUP"}
val lookup_fmty = #1 (dom_rng (type_of FLOOKUP_t))
fun mk_flookup_eqn fm k =
    EVAL (mk_comb(mk_icomb(FLOOKUP_t, fm), k))

val mk_def = let
  val iref = ref 0
in
  fn t => let
    val i = !iref
    val _ = iref := !iref + 1;
    val nm = "internal" ^ Int.toString (!iref)
  in
    new_definition(nm ^ "_def", mk_eq(mk_var(nm, type_of t), t))
  end
end

fun extract_fmap sz t = let
  fun test t = finite_mapSyntax.is_fupdate t andalso lbinop_size 0 t > sz
  val fm = find_term test t
  val lookup_t = inst (match_type lookup_fmty (type_of fm)) FLOOKUP_t
  val def = mk_def fm
  val fl_def' = AP_TERM lookup_t def
  val keys = fmkeys fm
  fun fulleqn k = let
    val th0 = AP_THM fl_def' k
  in
    CONV_RULE (RAND_CONV EVAL) th0
  end
  val eqns = map fulleqn keys
in
  (ONCE_DEPTH_CONV (REWR_CONV (SYM def)) t, eqns, def)
end

fun doit i (lastfm_def, defs, th) = let
  val list_t = rand (rhs (concl th))
  val nstr = listSyntax.mk_length list_t |> (PURE_REWRITE_CONV defs THENC EVAL)
               |> concl |> rhs |> term_to_string
  val _ = print (nstr^" declarations still to go\n")
  val (defs', th20_0) = iterate i defs (rhs (concl th))
  val th20 = CONV_RULE (RAND_CONV (K th20_0)) th
  val th20_fm = CONV_RULE (PURE_REWRITE_CONV [lastfm_def]) th20
  val _ = print "  extracting finite-map "
  val _ = PolyML.fullGC()
  val (new_th0, fm_eqns, new_fmdef) = time (extract_fmap 20) (rhs (concl th20_fm))
  val new_th = TRANS th20_fm new_th0
  val _ = computeLib.add_funs fm_eqns
  val _ = PolyML.fullGC()
in
  (new_fmdef, defs', new_th)
end

end
