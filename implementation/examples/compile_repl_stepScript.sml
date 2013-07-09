open preamble repl_computeLib ml_repl_stepTheory
val _ = new_theory"compile_repl_step"

val stop_APPEND_def = zDefine`
  stop_APPEND (l1:bc_inst list) l2 = l1 ++ l2`

val _ = computeLib.stoppers := let
  val stoppers = [``Dlet``,``Dletrec``,``Dtype``,``stop_APPEND``]
  in SOME (fn tm => mem tm stoppers) end

val _ = computeLib.add_funs[ml_repl_step_decls]

val compile_dec1_def = Define`
  compile_dec1 mn menv (ct,m,env,rsz,cs) dec =
    let (vso,cs) = compile_dec menv m env rsz cs dec in
    let ct = dec_to_contab mn ct dec in
    let vs = case vso of NONE => [] | SOME vs => vs in
    let n = LENGTH vs in
    let m = m with <|cnmap := cmap ct; bvars := vs ++ m.bvars|> in
    let env = GENLIST (λi. CTDec (rsz+n-1-i)) n ++ env in
    let rsz = rsz + n in
    let cs = compile_news cs 0 vs in
    (ct,m,env,rsz,cs)`

val compile_decs_FOLDL = store_thm(
  "compile_decs_FOLDL",
  ``∀mn menv ct m env rsz cs decs.
      compile_decs mn menv ct m env rsz cs decs =
      let (ct,m,env,rsz,cs) = FOLDL (compile_dec1 mn menv) (ct,m,env,rsz,cs) decs in
      (ct,m,rsz,cs)``,
  Induct_on `decs` >- rw[compile_decs_def] >>
  fs[LET_THM] >>
  simp[compile_dec1_def] >>
  simp[compile_decs_def] >>
  simp[UNCURRY]);

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

val _ = Globals.max_print_depth := 15

val ct = ``init_compiler_state.contab``
val m = ``<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap(^ct)|>``
val cs = ``<|out:=[];next_label:=0|>``
fun mk_initial_split n =
  ``FOLDL (compile_dec1 NONE FEMPTY) (^ct,^m,[],0,^cs) ml_repl_step_decls``
     |> (RAND_CONV (EVAL THENC chunkify_CONV n) THENC
         RATOR_CONV (RAND_CONV EVAL))

val initial_split20 = mk_initial_split 20

val (initial', decllist_defs) = let
  val r = rhs (concl initial_split20)
  val r' = rand r
  val lists = spine_binop (Lib.total listSyntax.dest_append) r'
  val defs = map mk_def lists
  fun replace ths t =
    case ths of
      []=> ALL_CONV t
    | [d] => SYM d
    | d::ds => (LAND_CONV (K (SYM d)) THENC RAND_CONV (replace ds)) t
in
  (CONV_RULE (RAND_CONV (RAND_CONV (replace defs))) initial_split20, defs)
end

val x100 = doit 5 (TRUTH, decllist_defs, initial')
val x140 = doit 2 x100;
val x180 = doit 2 x140
val x220 = doit 2 x180;
val x240 = doit 1 x220;
val x260 = doit 1 x240;
val x280 = doit 1 x260;
val x300 = doit 1 x280;
val x320 = doit 1 x300;
val x340 = doit 1 x320;  (* manages this far on telemachus *)
val x356 = doit 1 x340;
val (_,_,th) = x356;

val compiled = save_thm("compiled", th);

(*

val _ = PolyML.fullGC();
val res = time EVAL
  ``compile_decs "CakeML" (TAKE 100 ml_repl_step_decls) (init_compiler_state,[])``
*)

(*
EVAL ``TAKE 20 (DROP 100 ml_repl_step_decls)``
val _ = time EVAL ``compile_decs "CakeML" ml_repl_step_decls (init_compiler_state,[])``
*)

(*
val Dlet_o = time EVAL ``EL 11 ml_repl_step_decls`` |> concl |> rhs
val many_o10 = EVAL ``GENLIST (K ^Dlet_o) 10`` |> concl |> rhs
val many_o20 = EVAL ``GENLIST (K ^Dlet_o) 20`` |> concl |> rhs
val many_o40 = EVAL ``GENLIST (K ^Dlet_o) 40`` |> concl |> rhs
val many_o80 = EVAL ``GENLIST (K ^Dlet_o) 80`` |> concl |> rhs
val many_o160 = EVAL ``GENLIST (K ^Dlet_o) 160`` |> concl |> rhs

val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs "CakeML" ^many_o10 (init_compiler_state,[])``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs "CakeML" ^many_o20 (init_compiler_state,[])``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs "CakeML" ^many_o40 (init_compiler_state,[])``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs "CakeML" ^many_o80 (init_compiler_state,[])``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs "CakeML" ^many_o160 (init_compiler_state,[])``

val _ = computeLib.stoppers := NONE
val num_compset = reduceLib.num_compset()
*)

val _ = export_theory()
